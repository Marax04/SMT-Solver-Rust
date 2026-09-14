use smt_solver::engine::Solver;

#[test]
fn test_qf_uf_transitivity() {
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (= b c))
        (assert (distinct (f a) (f c)))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_qf_uf_congruence_chain() {
    let script = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun x () S)
        (declare-fun y () S)
        (declare-fun f (S) S)
        (assert (= x y))
        (assert (= (f x) x))
        (assert (distinct (f y) y))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
