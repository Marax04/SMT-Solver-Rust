//! Formal coherence tests between StrictFault and PermissiveOverApproximation memory policies.
//!
//! Verifies that PermissiveOverApproximation is strictly conservative:
//! it never contradicts a mathematically proven invariant under StrictFault,
//! and whenever an unmapped access occurs, it marks the result as OverApproximated
//! rather than claiming a formal proof.

use smt_solver::lifter::{
    BranchCondition, BranchResolution, DeobfuscationStatus, IrInstruction, Lifter, MemoryPolicy,
    MemoryStateKind, Operand,
};

#[test]
fn test_memory_coherence_on_fully_mapped_invariants() {
    // Both lifters have the identical mapped memory page 0x401000..0x402000
    let mut strict = Lifter::new();
    strict.memory_policy = MemoryPolicy::StrictFault;
    strict.mapped_ranges.push((0x401000, 0x402000));

    let mut permissive = Lifter::new();
    permissive.memory_policy = MemoryPolicy::PermissiveOverApproximation;
    permissive.mapped_ranges.push((0x401000, 0x402000));

    // Execute identical instructions in mapped space:
    // Write 0x42 to [0x401050], read it back, xor with 0x42 -> zero flag set
    let mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x401050,
        width: 32,
    };
    let val_42 = strict.terms.bv_const(0x42u64.into(), 32, &mut strict.sorts);
    strict.write_memory(&mem, val_42);
    let val_42_p = permissive
        .terms
        .bv_const(0x42u64.into(), 32, &mut permissive.sorts);
    permissive.write_memory(&mem, val_42_p);

    let eax = Operand::Reg("eax".to_string(), 32);
    strict.step(&IrInstruction::Mov {
        dst: eax.clone(),
        src: mem.clone(),
    });
    permissive.step(&IrInstruction::Mov {
        dst: eax.clone(),
        src: mem.clone(),
    });

    let imm_42 = Operand::Imm(0x42, 32);
    strict.step(&IrInstruction::Sub {
        dst: eax.clone(),
        src: imm_42.clone(),
    });
    permissive.step(&IrInstruction::Sub {
        dst: eax,
        src: imm_42,
    });

    let jcc = IrInstruction::Jcc {
        cond: BranchCondition::Zero,
        target_true: 0x401100,
        target_false: 0x401200,
    };

    let strict_res = strict.resolve_branch_certified(&jcc, &[]);
    let permissive_res = permissive.resolve_branch_certified(&jcc, &[]);

    // 1. Both engines MUST agree on the deterministic branch resolution
    assert_eq!(
        strict_res.resolution,
        BranchResolution::Deterministic(0x401100)
    );
    assert_eq!(
        permissive_res.resolution,
        BranchResolution::Deterministic(0x401100)
    );

    // 2. Both engines certify the invariant since no unmapped access occurred
    assert_eq!(
        strict_res.status,
        DeobfuscationStatus::ProvenInvariant {
            surviving_target: 0x401100,
            dead_target: 0x401200,
        }
    );
    assert_eq!(
        permissive_res.status,
        DeobfuscationStatus::ProvenInvariant {
            surviving_target: 0x401100,
            dead_target: 0x401200,
        }
    );
}

#[test]
fn test_memory_coherence_on_unmapped_access_divergence() {
    let mut strict = Lifter::new();
    strict.memory_policy = MemoryPolicy::StrictFault;
    strict.mapped_ranges.push((0x401000, 0x402000));

    let mut permissive = Lifter::new();
    permissive.memory_policy = MemoryPolicy::PermissiveOverApproximation;
    permissive.mapped_ranges.push((0x401000, 0x402000));

    // Read from unmapped memory at 0x600000
    let unmapped_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x600000,
        width: 32,
    };
    let _s_val = strict.read_memory(&unmapped_mem);
    let _p_val = permissive.read_memory(&unmapped_mem);

    let jmp = IrInstruction::Jmp { target: 0x401080 };

    let s_cert = strict.resolve_branch_certified(&jmp, &[]);
    let p_cert = permissive.resolve_branch_certified(&jmp, &[]);

    // Strict detects the fault immediately
    assert_eq!(
        s_cert.resolution,
        BranchResolution::MemoryFault(MemoryStateKind::UnmappedFault, 0x600000)
    );
    assert_eq!(s_cert.status, DeobfuscationStatus::FaultDetected);

    // Permissive executes the direct jump, but marks status as OverApproximated if evaluated on condition
    assert_eq!(p_cert.resolution, BranchResolution::Deterministic(0x401080));
    assert!(permissive.had_over_approximation);
    assert!(!permissive.had_unmapped_fault);
}
