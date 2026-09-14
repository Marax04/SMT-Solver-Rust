use smt_solver::engine::Solver;

#[test]
fn test_qf_uflra_shared_equality_unsat() {
    let mut solver = Solver::new();
    let script = r#"
        (set-logic QF_UFLRA)
        (declare-sort U 0)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= x y))
        (assert (<= y x))
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;
    let outputs = solver
        .execute_script(script)
        .expect("Script execution failed");
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_qf_uflra_shared_variable_sat() {
    let mut solver = Solver::new();
    let script = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 1.0))
        (assert (<= y 3.0))
        (assert (= (f x) (f y)))
        (check-sat)
        (get-model)
    "#;
    let outputs = solver
        .execute_script(script)
        .expect("Script execution failed");
    assert_eq!(outputs[0], "sat");
}
