//! Verification of logical instruction flag semantics (TEST, AND, OR, XOR),
//! flag preservation across non-modifying instructions, and CMP vs SUB register non-destruction.

use smt_solver::lifter::{BranchCondition, BranchResolution, IrInstruction, Lifter, Operand};

#[test]
fn test_test_instruction_flag_semantics_against_native_cpu() {
    let mut lifter = Lifter::new();

    // Test cases: (a, b) pairs covering zero, sign, non-zero
    let test_cases: &[(u64, u64, u32)] = &[
        (0, 0, 32),
        (0x12345678, 0x87654321, 32),
        (0x80000000, 0x80000000, 32),
        (0x7fffffff, 0x00000001, 32),
        (0x8000_0000_0000_0000, 0x8000_0000_0000_0000, 64),
        (0xdeadbeef, 0x00000000, 32),
        (0xff, 0x01, 8),
        (0x80, 0x80, 8),
    ];

    for &(a, b, width) in test_cases {
        lifter.push();

        let inst = IrInstruction::Test {
            left: Operand::Imm(a, width),
            right: Operand::Imm(b, width),
        };
        lifter.step(&inst);

        // Native CPU calculation
        let native_and = a & b;
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        let native_val = native_and & mask;
        let expected_zf = native_val == 0;
        let expected_sf = (native_val & (1u64 << (width - 1))) != 0;
        let expected_cf = false;
        let expected_of = false;
        assert!(!expected_cf);
        assert!(!expected_of);

        // Verify with SMT branch queries
        // 1. Equal / Zero branch
        let branch_z = IrInstruction::Jcc {
            cond: BranchCondition::Zero,
            target_true: 0x1,
            target_false: 0x2,
        };
        let res_z = lifter.resolve_branch(&branch_z, &[]);
        let expected_target_z = if expected_zf { 0x1 } else { 0x2 };
        assert_eq!(res_z, BranchResolution::Deterministic(expected_target_z));

        // 2. Sign branch
        let branch_s = IrInstruction::Jcc {
            cond: BranchCondition::Sign,
            target_true: 0x1,
            target_false: 0x2,
        };
        let res_s = lifter.resolve_branch(&branch_s, &[]);
        let expected_target_s = if expected_sf { 0x1 } else { 0x2 };
        assert_eq!(res_s, BranchResolution::Deterministic(expected_target_s));

        // 3. Carry branch (must be false)
        let branch_c = IrInstruction::Jcc {
            cond: BranchCondition::BelowUnsigned,
            target_true: 0x1,
            target_false: 0x2,
        };
        let res_c = lifter.resolve_branch(&branch_c, &[]);
        assert_eq!(res_c, BranchResolution::Deterministic(0x2));

        // 4. Overflow branch (must be false)
        let branch_o = IrInstruction::Jcc {
            cond: BranchCondition::Overflow,
            target_true: 0x1,
            target_false: 0x2,
        };
        let res_o = lifter.resolve_branch(&branch_o, &[]);
        assert_eq!(res_o, BranchResolution::Deterministic(0x2));

        lifter.pop();
    }
}

#[test]
fn test_flag_preservation_across_non_modifying_instructions() {
    let mut lifter = Lifter::new();

    // 1. Set flags via CMP rax, 0 (where rax = 0 -> ZF = 1)
    let inst_cmp = IrInstruction::Cmp {
        left: Operand::Imm(0, 64),
        right: Operand::Imm(0, 64),
    };
    lifter.step(&inst_cmp);

    // Verify initial ZF = 1
    let branch1 = IrInstruction::Jcc {
        cond: BranchCondition::Zero,
        target_true: 0x100,
        target_false: 0x200,
    };
    assert_eq!(
        lifter.resolve_branch(&branch1, &[]),
        BranchResolution::Deterministic(0x100)
    );

    // 2. Execute non-modifying instructions: MOV, PUSH, POP, NOP
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rbx".to_string(), 64),
        src: Operand::Imm(0x1234, 64),
    });
    lifter.step(&IrInstruction::Push {
        src: Operand::Reg("rbx".to_string(), 64),
    });
    lifter.step(&IrInstruction::Pop {
        dst: Operand::Reg("rcx".to_string(), 64),
    });
    lifter.step(&IrInstruction::Nop);

    // 3. Verify ZF is STILL 1 (unmodified by Mov, Push, Pop, Nop)
    assert_eq!(
        lifter.resolve_branch(&branch1, &[]),
        BranchResolution::Deterministic(0x100)
    );
}

#[test]
fn test_cmp_vs_sub_non_destruction_invariant() {
    let mut lifter = Lifter::new();

    // Initialize rax = 100
    let inst_mov = IrInstruction::Mov {
        dst: Operand::Reg("rax".to_string(), 64),
        src: Operand::Imm(100, 64),
    };
    lifter.step(&inst_mov);

    // CMP rax, 40 (must set flags but NOT modify rax)
    let inst_cmp = IrInstruction::Cmp {
        left: Operand::Reg("rax".to_string(), 64),
        right: Operand::Imm(40, 64),
    };
    lifter.step(&inst_cmp);

    // rax must still equal 100!
    let rax_term = lifter.read_reg("rax", 64);
    assert_eq!(lifter.eval_concrete_u64(rax_term), Some(100));

    // Now SUB rax, 40 (must set flags AND modify rax to 60)
    let inst_sub = IrInstruction::Sub {
        dst: Operand::Reg("rax".to_string(), 64),
        src: Operand::Imm(40, 64),
    };
    lifter.step(&inst_sub);

    // rax must now equal 60!
    let rax_after_sub = lifter.read_reg("rax", 64);
    assert_eq!(lifter.eval_concrete_u64(rax_after_sub), Some(60));
}
