//! Comprehensive unit and integration tests for the unified byte-addressed memory and stack model.

use smt_solver::engine::{CheckSatResult, Solver};
use smt_solver::lifter::{IrInstruction, Lifter, Operand};

#[test]
fn test_memory_byte_addressed_endianness_and_partial_overwrites() {
    let mut lifter = Lifter::new();

    // Store 64-bit constant at 0x2000
    let target_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x2000,
        width: 64,
    };
    lifter.step(&IrInstruction::Mov {
        dst: target_mem.clone(),
        src: Operand::Imm(0x0123_4567_89ab_cdef, 64),
    });

    // Read low 32 bits from 0x2000 into EAX
    let low32_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x2000,
        width: 32,
    };
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("eax".into(), 32),
        src: low32_mem,
    });

    // Read high 32 bits from 0x2004 into EDX
    let high32_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x2004,
        width: 32,
    };
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("edx".into(), 32),
        src: high32_mem,
    });

    // Overwrite byte 1 (offset 1, originally 0xcd) with 0x00
    let byte1_mem = Operand::Mem {
        base: None,
        index: None,
        disp: 0x2001,
        width: 8,
    };
    lifter.step(&IrInstruction::Mov {
        dst: byte1_mem,
        src: Operand::Imm(0x00, 8),
    });

    // Read modified full 64-bit value into RBX
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rbx".into(), 64),
        src: target_mem,
    });

    // Verify symbolically via SMT
    let eax = lifter.eval_operand(&Operand::Reg("eax".into(), 32));
    let edx = lifter.eval_operand(&Operand::Reg("edx".into(), 32));
    let rbx = lifter.eval_operand(&Operand::Reg("rbx".into(), 64));

    let exp_eax = lifter
        .terms
        .bv_const(0x89ab_cdefu32.into(), 32, &mut lifter.sorts);
    let exp_edx = lifter
        .terms
        .bv_const(0x0123_4567u32.into(), 32, &mut lifter.sorts);
    // Modified: 0x0123_4567_89ab_00ef
    let exp_rbx = lifter
        .terms
        .bv_const(0x0123_4567_89ab_00efu64.into(), 64, &mut lifter.sorts);

    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");

    let eq_eax = solver.terms.eq(eax, exp_eax, &solver.sorts);
    let eq_edx = solver.terms.eq(edx, exp_edx, &solver.sorts);
    let eq_rbx = solver.terms.eq(rbx, exp_rbx, &solver.sorts);
    let all_correct = solver
        .terms
        .and(vec![eq_eax, eq_edx, eq_rbx], &solver.sorts);
    let not_correct = solver.terms.not(all_correct);
    solver.assert_formula(not_correct);

    assert_eq!(
        solver.check_sat(),
        CheckSatResult::Unsat,
        "Endianness and partial byte modifications must be soundly verified"
    );
}

#[test]
fn test_memory_unified_stack_aliasing_and_push_pop() {
    let mut lifter = Lifter::new();

    // 1. Initial stack pointer is default concrete 0x7fff_ffff_0000
    // Push symbolic value RAX
    let rax_term = lifter.init_register("secret_input", 64);
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rax".into(), 64),
        src: Operand::Reg("secret_input".into(), 64),
    });

    lifter.step(&IrInstruction::Push {
        src: Operand::Reg("rax".into(), 64),
    });

    // 2. Direct memory read from [rsp] into RBX must alias with pushed value
    let mem_at_rsp = Operand::Mem {
        base: Some("rsp".into()),
        index: None,
        disp: 0,
        width: 64,
    };
    lifter.step(&IrInstruction::Mov {
        dst: Operand::Reg("rbx".into(), 64),
        src: mem_at_rsp.clone(),
    });

    // 3. Overwrite [rsp] with concrete constant 0xcafe_babe
    lifter.step(&IrInstruction::Mov {
        dst: mem_at_rsp,
        src: Operand::Imm(0xcafe_babe, 64),
    });

    // 4. Pop into RCX must retrieve overwritten value 0xcafe_babe and restore RSP
    lifter.step(&IrInstruction::Pop {
        dst: Operand::Reg("rcx".into(), 64),
    });

    let rbx_term = lifter.eval_operand(&Operand::Reg("rbx".into(), 64));
    let rcx_term = lifter.eval_operand(&Operand::Reg("rcx".into(), 64));
    let rsp_term = lifter.eval_operand(&Operand::Reg("rsp".into(), 64));

    let exp_rcx = lifter
        .terms
        .bv_const(0xcafe_babeu64.into(), 64, &mut lifter.sorts);
    let exp_rsp = lifter
        .terms
        .bv_const(0x7fff_ffff_0000u64.into(), 64, &mut lifter.sorts);

    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");

    let eq_rbx = solver.terms.eq(rbx_term, rax_term, &solver.sorts);
    let eq_rcx = solver.terms.eq(rcx_term, exp_rcx, &solver.sorts);
    let eq_rsp = solver.terms.eq(rsp_term, exp_rsp, &solver.sorts);
    let all_ok = solver
        .terms
        .and(vec![eq_rbx, eq_rcx, eq_rsp], &solver.sorts);
    let disproved = solver.terms.not(all_ok);
    solver.assert_formula(disproved);

    assert_eq!(
        solver.check_sat(),
        CheckSatResult::Unsat,
        "Stack aliasing, memory writes to [rsp], and POP must be unified and sound"
    );
}

#[test]
fn test_memory_scope_push_pop_state_isolation() {
    let mut lifter = Lifter::new();

    let mem_loc = Operand::Mem {
        base: None,
        index: None,
        disp: 0x5000,
        width: 64,
    };

    lifter.step(&IrInstruction::Mov {
        dst: mem_loc.clone(),
        src: Operand::Imm(0x1111, 64),
    });

    lifter.push();

    // In child scope, modify memory
    lifter.step(&IrInstruction::Mov {
        dst: mem_loc.clone(),
        src: Operand::Imm(0x9999, 64),
    });

    let child_val = lifter.eval_operand(&mem_loc);
    let exp_child = lifter
        .terms
        .bv_const(0x9999u64.into(), 64, &mut lifter.sorts);

    let mut solver = Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    let eq = solver.terms.eq(child_val, exp_child, &solver.sorts);
    let neq = solver.terms.not(eq);
    solver.assert_formula(neq);
    assert_eq!(solver.check_sat(), CheckSatResult::Unsat);

    // Pop scope: memory should revert to 0x1111
    assert!(lifter.pop());
    let parent_val = lifter.eval_operand(&mem_loc);
    let exp_parent = lifter
        .terms
        .bv_const(0x1111u64.into(), 64, &mut lifter.sorts);

    let mut solver2 = Solver::new();
    solver2.sorts = lifter.sorts.clone();
    solver2.terms = lifter.terms.clone();
    let eq2 = solver2.terms.eq(parent_val, exp_parent, &solver2.sorts);
    let neq2 = solver2.terms.not(eq2);
    solver2.assert_formula(neq2);
    assert_eq!(solver2.check_sat(), CheckSatResult::Unsat);
}
