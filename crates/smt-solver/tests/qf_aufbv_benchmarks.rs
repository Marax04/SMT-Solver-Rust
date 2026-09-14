use smt_solver::engine::Solver;

#[test]
fn test_qf_aufbv_read_over_write() {
    // Array read-over-write:
    // (select (store a i v) i) == v
    // Assert (distinct (select (store a i #x42) i) #x42) => UNSAT
    let script = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const i (_ BitVec 32))
        (assert (distinct (select (store a i #x42) i) #x42))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
