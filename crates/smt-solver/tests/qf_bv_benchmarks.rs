use smt_solver::engine::Solver;

#[test]
fn test_bv_overflow_detection() {
    // Check whether 8-bit unsigned addition overflows: (bvadd x #x01) == #x00 with x != #xff -> unsat
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x00))
        (assert (distinct x #xff))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_bv_sha_round_mock() {
    // Reverse engineering pattern: rotate left + xor + and
    let script = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (assert (= (bvxor a b) #x12345678))
        (assert (= (bvand a b) #x00000000))
        (check-sat)
        (get-model)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();
    assert_eq!(outputs[0], "sat");
    let model = solver.get_model().unwrap();
    assert!(model.get("a").is_some());
    assert!(model.get("b").is_some());
}

#[test]
fn test_bv_multiplier_factoring() {
    // Factoring 15 into 3 * 5
    let script = r#"
        (set-logic QF_BV)
        (declare-const p (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (assert (= (bvmul p q) #x0f))
        (assert (distinct p #x01))
        (assert (distinct q #x01))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let res = solver.execute_script(script).unwrap();
    assert_eq!(res, vec!["sat"]);
}
