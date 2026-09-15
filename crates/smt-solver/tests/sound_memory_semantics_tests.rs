//! Tests for sound memory semantics, fault detection, over-approximation tracking,
//! store-chain compaction, and budget exhaustion bounds.

use smt_solver::lifter::{
    BranchCondition, BranchResolution, DeobfuscationStatus, IrInstruction, Lifter, MemoryPolicy,
    MemoryStateKind, Operand,
};

#[test]
fn test_sound_memory_strict_fault_on_unmapped_access() {
    let mut lifter = Lifter::new();
    lifter.memory_policy = MemoryPolicy::StrictFault;
    // Map only a 4KB page at 0x401000..0x402000
    lifter.mapped_ranges.push((0x401000, 0x402000));

    // 1. Attempt read from unmapped address 0x500000
    let unmapped_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x500000,
        width: 32,
    };
    let read_val = lifter.read_memory(&unmapped_mem);
    assert!(lifter.had_unmapped_fault);
    assert_eq!(lifter.fault_address, Some(0x500000));

    // 2. Writing to unmapped address also triggers fault
    lifter.write_memory(&unmapped_mem, read_val);
    assert!(lifter.had_unmapped_fault);

    // 3. Branch resolution reports MemoryFault
    let jmp = IrInstruction::Jmp { target: 0x401100 };
    let res = lifter.resolve_branch(&jmp, &[]);
    assert_eq!(
        res,
        BranchResolution::MemoryFault(MemoryStateKind::UnmappedFault, 0x500000)
    );

    // 4. Certified resolution reports FaultDetected
    let cert = lifter.resolve_branch_certified(&jmp, &[]);
    assert_eq!(cert.status, DeobfuscationStatus::FaultDetected);
    assert!(cert.certificate.contains("unmapped memory access"));
}

#[test]
fn test_sound_memory_strict_fault_on_read_only_violation() {
    let mut lifter = Lifter::new();
    lifter.memory_policy = MemoryPolicy::StrictFault;
    // Map 0x401000..0x402000 and designate it as read-only (.rodata/.text)
    lifter.mapped_ranges.push((0x401000, 0x402000));
    lifter.read_only_ranges.push((0x401000, 0x402000));

    let ro_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x401050,
        width: 32,
    };
    let dummy_val = lifter
        .terms
        .bv_const(0x12345678u64.into(), 32, &mut lifter.sorts);
    lifter.write_memory(&ro_mem, dummy_val);

    assert!(lifter.had_permission_fault);
    assert_eq!(lifter.fault_address, Some(0x401050));

    let jmp = IrInstruction::Jmp { target: 0x401200 };
    let res = lifter.resolve_branch(&jmp, &[]);
    assert_eq!(
        res,
        BranchResolution::MemoryFault(MemoryStateKind::PermissionFault, 0x401050)
    );

    let cert = lifter.resolve_branch_certified(&jmp, &[]);
    assert_eq!(cert.status, DeobfuscationStatus::FaultDetected);
    assert!(cert.certificate.contains("permission violation"));
}

#[test]
fn test_sound_memory_permissive_over_approximation_classification() {
    let mut lifter = Lifter::new();
    lifter.memory_policy = MemoryPolicy::PermissiveOverApproximation;
    lifter.mapped_ranges.push((0x401000, 0x402000));

    // Read from unmapped address in permissive mode -> introduces fresh symbolic variable
    let unmapped_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x600000,
        width: 32,
    };
    let _val = lifter.read_memory(&unmapped_mem);
    assert!(lifter.had_over_approximation);
    assert!(!lifter.had_unmapped_fault);

    // Opaque predicate: eax ^ eax == 0 (always true)
    let eax = Operand::Reg("eax".to_string(), 32);
    lifter.step(&IrInstruction::Xor {
        dst: eax.clone(),
        src: eax.clone(),
    });
    lifter.step(&IrInstruction::Test {
        left: eax.clone(),
        right: eax,
    });

    let jcc = IrInstruction::Jcc {
        cond: BranchCondition::Zero,
        target_true: 0x401050,
        target_false: 0x401090,
    };

    // Under permissive over-approximation, status MUST be OverApproximated, NOT ProvenInvariant
    let cert = lifter.resolve_branch_certified(&jcc, &[]);
    assert_eq!(cert.status, DeobfuscationStatus::OverApproximated);
    assert_eq!(cert.resolution, BranchResolution::Deterministic(0x401050));
}

#[test]
fn test_store_chain_compaction_and_load_forwarding() {
    let mut lifter = Lifter::new();
    // Use an unconstrained symbolic base register 'rdi'
    let sort64 = lifter.sorts.bv(64);
    let rdi_sym = lifter.terms.var("rdi_sym".to_string(), sort64);
    lifter.write_reg("rdi", rdi_sym, 64);

    let mem_op = Operand::Mem {
        base: Some("rdi".to_string()),
        index: None,
        disp: 8,
        width: 8,
    };

    let val1 = lifter.terms.bv_const(0x42u64.into(), 8, &mut lifter.sorts);
    let val2 = lifter.terms.bv_const(0x99u64.into(), 8, &mut lifter.sorts);

    // Write val1 to [rdi + 8]
    lifter.write_memory(&mem_op, val1);
    // Write val2 to the exact same symbolic location [rdi + 8]
    lifter.write_memory(&mem_op, val2);

    // Store-chain compaction ensures that multiple writes to identical symbolic addresses
    // coalesce into a single entry rather than accumulating redundant stores.
    assert_eq!(
        lifter.symbolic_memory.len(),
        1,
        "Store chain must compact identical address writes"
    );

    // Reading from [rdi + 8] must forward the updated val2 directly
    let read_val = lifter.read_memory(&mem_op);
    assert_eq!(read_val, val2);
}

#[test]
fn test_store_chain_depth_budget_exhaustion() {
    let mut lifter = Lifter::new();
    lifter.max_store_chain_depth = 8; // Small budget for testing

    let sort64 = lifter.sorts.bv(64);
    let rsi_sym = lifter.terms.var("rsi_sym".to_string(), sort64);
    lifter.write_reg("rsi", rsi_sym, 64);

    // Write 16 distinct symbolic memory locations [rsi + i*8]
    for i in 0..16 {
        let mem = Operand::Mem {
            base: Some("rsi".to_string()),
            index: None,
            disp: (i as i64) * 8,
            width: 8,
        };
        let val = lifter
            .terms
            .bv_const((i as u64).into(), 8, &mut lifter.sorts);
        lifter.write_memory(&mem, val);
    }

    assert!(lifter.had_budget_exhaustion);
    assert_eq!(lifter.symbolic_memory.len(), 8);

    let jmp = IrInstruction::Jmp { target: 0x401080 };
    let res = lifter.resolve_branch(&jmp, &[]);
    assert_eq!(res, BranchResolution::BudgetExhausted);

    let cert = lifter.resolve_branch_certified(&jmp, &[]);
    assert_eq!(cert.status, DeobfuscationStatus::ResourceExhausted);
    assert_eq!(cert.resolution, BranchResolution::BudgetExhausted);
}
