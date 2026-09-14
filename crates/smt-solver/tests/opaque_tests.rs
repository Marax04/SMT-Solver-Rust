use smt_core::term::Op;
use smt_solver::engine::Solver;
use smt_solver::opaque::OpaqueClassification;

#[test]
fn test_opaque_always_true_xor_identity() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    // Predicate: x ^ x == 0 (Always True)
    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);
    let x_xor_x = solver.terms.bv_binop(Op::BvXor, x, x).unwrap();
    let predicate = solver.terms.eq(x_xor_x, zero, &solver.sorts);

    let classification = solver.check_opaque(predicate);
    assert_eq!(classification, OpaqueClassification::AlwaysTrue);
}

#[test]
fn test_opaque_always_true_linear_mba() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    let y = solver.declare_const("y", bv32);
    solver.set_logic("QF_BV");

    // Predicate: (x ^ y) + 2*(x & y) == x + y (Always True MBA identity)
    let xor_term = solver.terms.bv_binop(Op::BvXor, x, y).unwrap();
    let and_term = solver.terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let two = solver.terms.bv_const(2u32.into(), 32, &mut solver.sorts);
    let two_and = solver.terms.bv_binop(Op::BvMul, two, and_term).unwrap();
    let mba_expr = solver.terms.bv_binop(Op::BvAdd, xor_term, two_and).unwrap();
    let add_xy = solver.terms.bv_binop(Op::BvAdd, x, y).unwrap();
    let predicate = solver.terms.eq(mba_expr, add_xy, &solver.sorts);

    let classification = solver.check_opaque(predicate);
    assert_eq!(classification, OpaqueClassification::AlwaysTrue);
}

#[test]
fn test_opaque_always_false() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    // Predicate: x ^ x != 0 (Always False)
    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);
    let x_xor_x = solver.terms.bv_binop(Op::BvXor, x, x).unwrap();
    let eq = solver.terms.eq(x_xor_x, zero, &solver.sorts);
    let predicate = solver.terms.not(eq);

    let classification = solver.check_opaque(predicate);
    assert_eq!(classification, OpaqueClassification::AlwaysFalse);
}

#[test]
fn test_opaque_dynamic() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    // Predicate: x == 42 (Dynamic - true for x=42, false otherwise)
    let target = solver.terms.bv_const(42u32.into(), 32, &mut solver.sorts);
    let predicate = solver.terms.eq(x, target, &solver.sorts);

    let classification = solver.check_opaque(predicate);
    assert_eq!(classification, OpaqueClassification::Dynamic);
}

#[test]
fn test_opaque_contextual_implied() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    // Path condition: x > 10
    let ten = solver.terms.bv_const(10u32.into(), 32, &mut solver.sorts);
    let pc_x_gt_10 = solver
        .terms
        .intern(Op::BvUgt, vec![x, ten], solver.sorts.bool_sort);

    // Predicate: x > 5
    let five = solver.terms.bv_const(5u32.into(), 32, &mut solver.sorts);
    let pred_x_gt_5 = solver
        .terms
        .intern(Op::BvUgt, vec![x, five], solver.sorts.bool_sort);

    // 1. In isolation, x > 5 is Dynamic (can be true or false)
    assert_eq!(
        solver.check_opaque(pred_x_gt_5),
        OpaqueClassification::Dynamic
    );

    // 2. Under the context (x > 10), x > 5 is an Opaque Invariant (AlwaysTrue)
    let context_class = solver.check_opaque_contextual(&[pc_x_gt_10], pred_x_gt_5);
    assert_eq!(context_class, OpaqueClassification::AlwaysTrue);

    // 3. Negated predicate: x < 5 under (x > 10) is AlwaysFalse
    let pred_x_lt_5 = solver
        .terms
        .intern(Op::BvUlt, vec![x, five], solver.sorts.bool_sort);
    let context_false = solver.check_opaque_contextual(&[pc_x_gt_10], pred_x_lt_5);
    assert_eq!(context_false, OpaqueClassification::AlwaysFalse);
}

#[test]
fn test_path_condition_folding_trace() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    let ten = solver.terms.bv_const(10u32.into(), 32, &mut solver.sorts);
    let five = solver.terms.bv_const(5u32.into(), 32, &mut solver.sorts);

    let pred_gt_10 = solver
        .terms
        .intern(Op::BvUgt, vec![x, ten], solver.sorts.bool_sort);
    let pred_gt_5 = solver
        .terms
        .intern(Op::BvUgt, vec![x, five], solver.sorts.bool_sort);

    // Trace: Block 100 branches on x > 10 (taken)
    //        Block 101 branches on x > 5 (contextually opaque!)
    let trace = vec![
        smt_solver::opaque::TraceBranch {
            block_id: 100,
            predicate: pred_gt_10,
            taken: true,
        },
        smt_solver::opaque::TraceBranch {
            block_id: 101,
            predicate: pred_gt_5,
            taken: true,
        },
    ];

    let result = solver.fold_trace(&trace);
    assert_eq!(result.reachable_blocks, vec![100, 101]);
    assert_eq!(result.classifications[0].1, OpaqueClassification::Dynamic);
    assert_eq!(
        result.classifications[1].1,
        OpaqueClassification::AlwaysTrue
    );
    assert!(result.eliminated_dead_edges.contains(&(101, false)));
}
