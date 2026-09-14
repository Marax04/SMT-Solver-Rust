use smt_core::value::Value;
use smt_solver::engine::{CheckSatResult, Solver};

#[test]
fn test_solver_qf_bv_crackme() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const key (_ BitVec 32))
        (assert (= (bvxor key #x12345678) #xdeadbeef))
        (check-sat)
        (get-model)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");

    let model = solver.get_model().unwrap();
    if let Some(Value::BitVec { value, width }) = model.get("key") {
        assert_eq!(*width, 32);
        // key = 0x12345678 ^ 0xdeadbeef = 0xcc99e897
        let expected = num_bigint::BigUint::parse_bytes(b"cc99e897", 16).unwrap();
        assert_eq!(*value, expected);
    } else {
        panic!("Expected bitvector key in model");
    }
}

#[test]
fn test_solver_qf_bv_unsat() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x05))
        (assert (bvugt x #x0a))
        (check-sat)
    "#;

    let mut solver = Solver::new();
    let outputs = solver.execute_script(script).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "unsat");
    assert_eq!(solver.check_sat(), CheckSatResult::Unsat);
}

#[test]
fn test_solver_incremental_push_pop() {
    let mut solver = Solver::new();
    let b_sort = solver.sorts.bool_sort;
    let x = solver.declare_const("x", b_sort);

    solver.assert_formula(x);
    assert_eq!(solver.check_sat(), CheckSatResult::Sat);

    solver.push(1);
    let not_x = solver.terms.not(x);
    solver.assert_formula(not_x);
    assert_eq!(solver.check_sat(), CheckSatResult::Unsat);

    solver.pop(1);
    assert_eq!(solver.check_sat(), CheckSatResult::Sat);
}
