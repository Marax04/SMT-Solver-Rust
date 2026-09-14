use smt_api::fluent::FluentSolver;
use smt_solver::engine::CheckSatResult;

#[test]
fn test_fluent_bv_solving() {
    let mut solver = FluentSolver::new();
    let x = solver.bv_var("x", 32);
    let c10 = solver.bv_const(10, 32);
    let c25 = solver.bv_const(25, 32);

    // x + 10 == 25
    let sum = solver.bv_add(x, c10);
    let eq = solver.eq(sum, c25);
    solver.assert(eq);

    let res = solver.check();
    assert_eq!(res, CheckSatResult::Sat);

    let x_val = solver.get_bv_u64("x").unwrap();
    assert_eq!(x_val, 15);
}

#[test]
fn test_fluent_unsat() {
    let mut solver = FluentSolver::new();
    let b = solver.bool_var("b");
    let not_b = solver.not(b);
    let contradiction = solver.and(&[b, not_b]);

    solver.assert(contradiction);

    let res = solver.check();
    assert_eq!(res, CheckSatResult::Unsat);
}
