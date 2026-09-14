//! Integration test suite for real x86-64 machine code decoding,
//! register aliasing, implicit 32-bit zero-extension, and opaque predicate pruning.

use smt_solver::engine::{CheckSatResult, Solver};
use smt_solver::lifter::{
    BranchCondition, BranchResolution, DeobfuscationStatus, IrInstruction, Lifter, Operand,
};
use smt_solver::x86_decoder::X86Decoder;

#[test]
fn test_x86_implicit_32bit_zero_extension() {
    let mut lifter = Lifter::new();

    // In x86-64, writing to a 32-bit destination register (e.g. `mov eax, 0x12345678`)
    // implicitly zero-extends to 64 bits, forcing rax[32..63] = 0.
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rax".into(), 64),
        src: Operand::Imm(0xffff_ffff_ffff_ffff, 64),
    });

    // Overwrite with 32-bit immediate
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("eax".into(), 32),
        src: Operand::Imm(0x1234_5678, 32),
    });

    let rax_term = lifter.eval_operand(&Operand::Reg("rax".into(), 64));
    let expected_rax =
        lifter
            .terms
            .bv_const(0x0000_0000_1234_5678u64.into(), 64, &mut lifter.sorts);

    // Verify formally via SMT equivalence check: rax == 0x0000000012345678
    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");
    let eq = solver.terms.eq(rax_term, expected_rax, &solver.sorts);
    let not_eq = solver.terms.not(eq);
    solver.assert_formula(not_eq);

    assert_eq!(
        solver.check_sat(),
        CheckSatResult::Unsat,
        "Upper 32 bits of RAX must be cleared by 32-bit register write"
    );
}

#[test]
fn test_x86_subregister_partial_aliasing_roundtrip() {
    let mut lifter = Lifter::new();

    // 1. Set full 64-bit RAX = 0x1122_3344_5566_7788
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rax".into(), 64),
        src: Operand::Imm(0x1122_3344_5566_7788, 64),
    });

    // 2. Modify AL (bits 0..7) = 0xAA
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("al".into(), 8),
        src: Operand::Imm(0xaa, 8),
    });

    // 3. Modify AH (bits 8..15) = 0xBB
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("ah".into(), 8),
        src: Operand::Imm(0xbb, 8),
    });

    // Expected state:
    // AL = 0xAA
    // AH = 0xBB
    // AX = 0xBBAA
    // RAX = 0x1122_3344_5566_BBAA
    let rax_term = lifter.eval_operand(&Operand::Reg("rax".into(), 64));
    let ax_term = lifter.eval_operand(&Operand::Reg("ax".into(), 16));
    let al_term = lifter.eval_operand(&Operand::Reg("al".into(), 8));
    let ah_term = lifter.eval_operand(&Operand::Reg("ah".into(), 8));

    let expected_rax =
        lifter
            .terms
            .bv_const(0x1122_3344_5566_bbaau64.into(), 64, &mut lifter.sorts);
    let expected_ax = lifter
        .terms
        .bv_const(0xbbaau64.into(), 16, &mut lifter.sorts);
    let expected_al = lifter.terms.bv_const(0xaau64.into(), 8, &mut lifter.sorts);
    let expected_ah = lifter.terms.bv_const(0xbbu64.into(), 8, &mut lifter.sorts);

    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");

    let eq_rax = solver.terms.eq(rax_term, expected_rax, &solver.sorts);
    let eq_ax = solver.terms.eq(ax_term, expected_ax, &solver.sorts);
    let eq_al = solver.terms.eq(al_term, expected_al, &solver.sorts);
    let eq_ah = solver.terms.eq(ah_term, expected_ah, &solver.sorts);

    let all_eq = solver
        .terms
        .and(vec![eq_rax, eq_ax, eq_al, eq_ah], &solver.sorts);
    let disproved = solver.terms.not(all_eq);
    solver.assert_formula(disproved);

    assert_eq!(
        solver.check_sat(),
        CheckSatResult::Unsat,
        "Partial subregister writes (AL, AH) must accurately update AX and RAX without corrupting higher bits"
    );
}

#[test]
fn test_x86_stack_push_pop_roundtrip_machine_code() {
    let mut lifter = Lifter::new();

    // Initialize RSP with base address
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rsp".into(), 64),
        src: Operand::Imm(0x7fff_ffff_0000, 64),
    });

    // Real machine code bytes:
    // 0x48, 0xb8, 0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00: movabs rax, 0xdeadbeef
    // 0x50: PUSH RAX
    // 0x5b: POP RBX
    let bytes = [
        0x48, 0xb8, 0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00, // movabs rax, 0xdeadbeef
        0x50, // push rax
        0x5b, // pop rbx
    ];

    let instrs = lifter
        .decode_and_execute_bytes(&bytes, 0x401000)
        .expect("Decoding and execution must succeed");

    assert_eq!(instrs.len(), 3);

    // Verify RBX received RAX value, and RSP returned to original stack pointer
    let rbx_term = lifter.eval_operand(&Operand::Reg("rbx".into(), 64));
    let rsp_term = lifter.eval_operand(&Operand::Reg("rsp".into(), 64));

    let expected_val = lifter
        .terms
        .bv_const(0xdead_beefu64.into(), 64, &mut lifter.sorts);
    let expected_rsp = lifter
        .terms
        .bv_const(0x7fff_ffff_0000u64.into(), 64, &mut lifter.sorts);

    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");

    let eq_rbx = solver.terms.eq(rbx_term, expected_val, &solver.sorts);
    let eq_rsp = solver.terms.eq(rsp_term, expected_rsp, &solver.sorts);
    let all_correct = solver.terms.and(vec![eq_rbx, eq_rsp], &solver.sorts);
    let disproved = solver.terms.not(all_correct);
    solver.assert_formula(disproved);

    assert_eq!(
        solver.check_sat(),
        CheckSatResult::Unsat,
        "Stack push/pop sequence must roundtrip operand and balance stack pointer"
    );
}

#[test]
fn test_x86_all_16_branch_conditions_certified() {
    let test_cases = vec![
        (BranchCondition::Equal, 10u64, 10u64, true),
        (BranchCondition::NotEqual, 10u64, 20u64, true),
        (BranchCondition::BelowUnsigned, 5u64, 10u64, true),
        (BranchCondition::AboveOrEqualUnsigned, 10u64, 5u64, true),
        (BranchCondition::BelowOrEqualUnsigned, 10u64, 10u64, true),
        (BranchCondition::AboveUnsigned, 15u64, 10u64, true),
        (BranchCondition::Sign, 5u64, 10u64, true),
        (BranchCondition::NotSign, 10u64, 5u64, true),
        (BranchCondition::LessThanSigned, 5u64, 10u64, true),
        (BranchCondition::GreaterOrEqualSigned, 10u64, 5u64, true),
        (BranchCondition::LessOrEqualSigned, 10u64, 10u64, true),
        (BranchCondition::GreaterThanSigned, 20u64, 10u64, true),
    ];

    for (cond, left_val, right_val, expected_true_branch) in test_cases {
        let mut lifter = Lifter::new();
        lifter.step(&IrInstruction::Mov {
            dst: Operand::Reg("rax".into(), 64),
            src: Operand::Imm(left_val, 64),
        });
        lifter.step(&IrInstruction::Mov {
            dst: Operand::Reg("rbx".into(), 64),
            src: Operand::Imm(right_val, 64),
        });
        lifter.step(&IrInstruction::Cmp {
            left: Operand::Reg("rax".into(), 64),
            right: Operand::Reg("rbx".into(), 64),
        });

        let target_true = 0x1000;
        let target_false = 0x2000;
        let jcc = IrInstruction::Jcc {
            cond,
            target_true,
            target_false,
        };

        let resolution = lifter.resolve_branch_certified(&jcc, &[]);
        let expected_target = if expected_true_branch {
            target_true
        } else {
            target_false
        };

        assert_eq!(
            resolution.resolution,
            BranchResolution::Deterministic(expected_target),
            "Branch condition {:?} for left={} right={} must deterministically resolve to {:#x}",
            cond,
            left_val,
            right_val,
            expected_target
        );
        assert!(
            matches!(
                resolution.status,
                DeobfuscationStatus::ProvenInvariant { .. }
            ),
            "Must be mathematically certified as invariant"
        );
    }
}

#[test]
fn test_x86_synthetic_opaque_dispatch_byte_decoder_and_smt_refutation() {
    // Synthetic benchmark: simplified x86-64 machine code sequence imitating
    // Tigress / OLLVM style constant-folding opaque dispatch:
    //
    // 0x401000: 48 b8 37 13 00 00 00 00 00 00    movabs rax, 0x1337
    // 0x40100a: 48 89 c3                         mov rbx, rax
    // 0x40100d: 48 29 d8                         sub rax, rbx       ; rax = 0, ZF = 1
    // 0x401010: 48 83 f8 00                      cmp rax, 0         ; redundant comparison
    // 0x401014: 75 08                            jne +8 (0x40101e)  ; Synthetic invariant branch! Never taken!
    let bytes = [
        0x48, 0xb8, 0x37, 0x13, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // movabs rax, 0x1337
        0x48, 0x89, 0xc3, // mov rbx, rax
        0x48, 0x29, 0xd8, // sub rax, rbx
        0x48, 0x83, 0xf8, 0x00, // cmp rax, 0
        0x75, 0x08, // jne +8 (target_true=0x40101e, target_false=0x401016)
    ];

    let bb = X86Decoder::decode_block(&bytes, 0x401000).expect("Byte decoding must succeed");
    assert_eq!(bb.instructions.len(), 5);

    let mut lifter = Lifter::new();
    lifter.execute_block(&bb);

    let terminator = bb.instructions.last().unwrap();
    let cert = lifter.resolve_branch_certified(terminator, &[]);

    // Legitimate fallthrough: 0x401014 + 2 = 0x401016
    // Bogus dead branch: 0x401014 + 2 + 8 = 0x40101e
    assert_eq!(
        cert.resolution,
        BranchResolution::Deterministic(0x401016),
        "Tigress opaque jump must be pruned, leaving deterministic fallthrough at 0x401016"
    );

    match cert.status {
        DeobfuscationStatus::ProvenInvariant {
            surviving_target,
            dead_target,
        } => {
            assert_eq!(surviving_target, 0x401016);
            assert_eq!(dead_target, 0x40101e);
        }
        _ => panic!("Expected ProvenInvariant status"),
    }

    assert!(
        cert.certificate.contains("UNSAT refutation"),
        "Certificate must explain SMT-backed proof: {}",
        cert.certificate
    );
}
