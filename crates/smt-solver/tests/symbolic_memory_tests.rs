use smt_solver::lifter::{IrInstruction, Lifter, Operand};

#[test]
fn test_symbolic_memory_read_after_write_forwarding() {
    let mut lifter = Lifter::new();

    // RDX holds symbolic address 'sym_ptr'
    let sym_ptr = lifter.init_register("rdx", 64);
    assert_eq!(lifter.eval_concrete_u64(sym_ptr), None);

    // Write 0x11223344_55667788 to [rdx]
    let mem_op = Operand::Mem {
        base: Some("rdx".to_string()),
        index: None,
        disp: 0,
        width: 64,
    };
    let val_to_write = lifter
        .terms
        .bv_const(0x11223344_55667788u64.into(), 64, &mut lifter.sorts);
    lifter.write_memory(&mem_op, val_to_write);

    // Read back from [rdx]
    let read_back = lifter.read_memory(&mem_op);

    // Verify formal equivalence using SMT: read_back == val_to_write is invariant
    let neq = lifter
        .terms
        .distinct(vec![read_back, val_to_write], &lifter.sorts);
    let mut solver = smt_solver::engine::Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");
    let bv64 = solver.sorts.bv(64);
    solver.declare_const("sym_ptr", bv64);
    solver.assert_formula(neq);
    assert_eq!(
        solver.check_sat(),
        smt_solver::engine::CheckSatResult::Unsat
    );
}

#[test]
fn test_symbolic_memory_distinct_displacements_do_not_clobber() {
    let mut lifter = Lifter::new();

    // RSI holds symbolic pointer 'base_ptr'
    let base_ptr = lifter.init_register("rsi", 64);
    assert_eq!(lifter.eval_concrete_u64(base_ptr), None);

    // Write val_a to [rsi]
    let mem_op_a = Operand::Mem {
        base: Some("rsi".to_string()),
        index: None,
        disp: 0,
        width: 64,
    };
    let val_a = lifter
        .terms
        .bv_const(0xaaaaaaaa_aaaaaaaau64.into(), 64, &mut lifter.sorts);
    lifter.write_memory(&mem_op_a, val_a);

    // Write val_b to [rsi + 8]
    let mem_op_b = Operand::Mem {
        base: Some("rsi".to_string()),
        index: None,
        disp: 8,
        width: 64,
    };
    let val_b = lifter
        .terms
        .bv_const(0xbbbbbbbb_bbbbbbbbu64.into(), 64, &mut lifter.sorts);
    lifter.write_memory(&mem_op_b, val_b);

    // Read back from [rsi]
    let read_a = lifter.read_memory(&mem_op_a);

    // Verify via SMT that read_a == val_a (not overwritten by write to [rsi + 8])
    let neq = lifter.terms.distinct(vec![read_a, val_a], &lifter.sorts);
    let mut solver = smt_solver::engine::Solver::new();
    solver.sorts = lifter.sorts.clone();
    solver.terms = lifter.terms.clone();
    solver.set_logic("QF_BV");
    let bv64 = solver.sorts.bv(64);
    solver.declare_const("base_ptr", bv64);
    solver.assert_formula(neq);
    assert_eq!(
        solver.check_sat(),
        smt_solver::engine::CheckSatResult::Unsat
    );
}

#[test]
fn test_symbolic_memory_alias_reasoning_in_branch_condition() {
    let mut lifter = Lifter::new();

    // RDI: key (symbolic 64-bit)
    lifter.init_register("rdi", 64);
    // Write 0x42 to symbolic address [rdi]
    let op_write = Operand::Mem {
        base: Some("rdi".to_string()),
        index: None,
        disp: 0,
        width: 64,
    };
    let val_42 = lifter.terms.bv_const(42u64.into(), 64, &mut lifter.sorts);
    lifter.write_memory(&op_write, val_42);

    // Read from [rdi] into rax
    let inst_mov = IrInstruction::Mov {
        dst: Operand::Reg("rax".to_string(), 64),
        src: op_write,
    };
    lifter.step(&inst_mov);

    // cmp rax, 42
    let inst_cmp = IrInstruction::Cmp {
        left: Operand::Reg("rax".to_string(), 64),
        right: Operand::Imm(42, 64),
    };
    lifter.step(&inst_cmp);

    // jz target (opaque true branch)
    let inst_branch = IrInstruction::Jcc {
        cond: smt_solver::lifter::BranchCondition::Equal,
        target_true: 0x1000,
        target_false: 0x2000,
    };

    let resolution = lifter.resolve_branch(&inst_branch, &[]);
    assert_eq!(
        resolution,
        smt_solver::lifter::BranchResolution::Deterministic(0x1000)
    );
}
