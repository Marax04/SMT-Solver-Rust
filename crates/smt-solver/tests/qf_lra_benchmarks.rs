use smt_solver::engine::Solver;

#[test]
fn test_qf_lra_strict_bounds_conflict() {
    // x < 5.0 and x > 5.0 is UNSAT
    let script = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_qf_lra_feasible_interval() {
    let script = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 0.0))
        (assert (<= x 10.0))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}
