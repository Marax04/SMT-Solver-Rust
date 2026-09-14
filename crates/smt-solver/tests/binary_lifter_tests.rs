use smt_core::term::Op;
use smt_solver::lifter::{
    BasicBlock, BranchCondition, BranchResolution, IrInstruction, Lifter, Operand,
};

#[test]
fn test_lifter_opaque_predicate_elimination() {
    let mut lifter = Lifter::new();

    // Initialize symbolic register x
    let _x_term = lifter.init_register("eax", 32);

    // Build a basic block executing an invariant 7*y^2 - 1 == x^2 opaque check
    // Here we use the classic algebraic identity: x*(x-1) is always even,
    // so ((x & 1) ^ (x - 1) & 1) or directly:
    // (x ^ y) + 2*(x & y) == x + y
    // Let's create an opaque check:
    // r1 = (x ^ y) + 2*(x & y)
    // r2 = x + y
    // cmp r1, r2
    // jne 0xDEADBEEF (dead branch / bogus control flow)
    // jmp 0x00401020 (real fallthrough)
    let mut bb = BasicBlock::new(0x00401000);
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r1_xor".into(), 32),
        src: Operand::Reg("x".into(), 32),
    });
    bb.push(IrInstruction::Xor {
        dst: Operand::Reg("r1_xor".into(), 32),
        src: Operand::Reg("y".into(), 32),
    });
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r1_and".into(), 32),
        src: Operand::Reg("x".into(), 32),
    });
    bb.push(IrInstruction::And {
        dst: Operand::Reg("r1_and".into(), 32),
        src: Operand::Reg("y".into(), 32),
    });
    // two_and = 2 * (x & y) = (x & y) + (x & y)
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("two_and".into(), 32),
        src: Operand::Reg("r1_and".into(), 32),
    });
    bb.push(IrInstruction::Add {
        dst: Operand::Reg("two_and".into(), 32),
        src: Operand::Reg("r1_and".into(), 32),
    });
    // r1 = r1_xor + two_and
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r1".into(), 32),
        src: Operand::Reg("r1_xor".into(), 32),
    });
    bb.push(IrInstruction::Add {
        dst: Operand::Reg("r1".into(), 32),
        src: Operand::Reg("two_and".into(), 32),
    });

    // r2 = x + y
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r2".into(), 32),
        src: Operand::Reg("x".into(), 32),
    });
    bb.push(IrInstruction::Add {
        dst: Operand::Reg("r2".into(), 32),
        src: Operand::Reg("y".into(), 32),
    });

    // cmp r1, r2
    bb.push(IrInstruction::Cmp {
        left: Operand::Reg("r1".into(), 32),
        right: Operand::Reg("r2".into(), 32),
    });

    lifter.execute_block(&bb);

    // Opaque branch: Jcc NotEqual -> 0xDEAD_BEEF, else 0x0040_1020
    let terminator = IrInstruction::Jcc {
        cond: BranchCondition::NotEqual,
        target_true: 0xDEAD_BEEF,
        target_false: 0x0040_1020,
    };

    let resolution = lifter.resolve_branch(&terminator, &[]);
    assert_eq!(
        resolution,
        BranchResolution::Deterministic(0x0040_1020),
        "Opaque bogus branch to 0xDEADBEEF must be pruned, leaving deterministic target 0x00401020"
    );
}

#[test]
fn test_lifter_mba_register_simplification() {
    let mut lifter = Lifter::new();

    // r = (x | y) - (x & y)
    let mut bb = BasicBlock::new(0x1000);
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r_or".into(), 32),
        src: Operand::Reg("x".into(), 32),
    });
    bb.push(IrInstruction::Or {
        dst: Operand::Reg("r_or".into(), 32),
        src: Operand::Reg("y".into(), 32),
    });
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("r_and".into(), 32),
        src: Operand::Reg("x".into(), 32),
    });
    bb.push(IrInstruction::And {
        dst: Operand::Reg("r_and".into(), 32),
        src: Operand::Reg("y".into(), 32),
    });
    bb.push(IrInstruction::Mov {
        dst: Operand::Reg("res".into(), 32),
        src: Operand::Reg("r_or".into(), 32),
    });
    bb.push(IrInstruction::Sub {
        dst: Operand::Reg("res".into(), 32),
        src: Operand::Reg("r_and".into(), 32),
    });

    lifter.execute_block(&bb);
    lifter.simplify_state();

    let res_op = Operand::Reg("res".into(), 32);
    let term_id = lifter.eval_operand(&res_op);
    let term = lifter.terms.get(term_id);

    // Must simplify to BvXor
    assert_eq!(
        term.op,
        Op::BvXor,
        "MBA register state must be deobfuscated to BvXor"
    );
}

#[test]
fn test_lifter_genuine_conditional_branch() {
    let mut lifter = Lifter::new();

    let mut bb = BasicBlock::new(0x2000);
    bb.push(IrInstruction::Cmp {
        left: Operand::Reg("user_input".into(), 32),
        right: Operand::Imm(42, 32),
    });
    lifter.execute_block(&bb);

    let terminator = IrInstruction::Jcc {
        cond: BranchCondition::Equal,
        target_true: 0x2050,
        target_false: 0x2080,
    };

    let resolution = lifter.resolve_branch(&terminator, &[]);
    assert_eq!(
        resolution,
        BranchResolution::Conditional {
            true_target: 0x2050,
            false_target: 0x2080,
        },
        "Unconstrained user input comparison must remain a genuine conditional branch"
    );
}
