use smt_core::term::Op;
use smt_core::value::Value;
use smt_solver::engine::Solver;

#[test]
fn test_decrypt_key_enumeration_multiple_solutions() {
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    let key = solver.declare_const("key", bv8);
    solver.set_logic("QF_BV");

    // Constraint: (key == 10) OR (key == 20) OR (key == 30)
    let c10 = solver.terms.bv_const(10u32.into(), 8, &mut solver.sorts);
    let c20 = solver.terms.bv_const(20u32.into(), 8, &mut solver.sorts);
    let c30 = solver.terms.bv_const(30u32.into(), 8, &mut solver.sorts);

    let eq1 = solver.terms.eq(key, c10, &solver.sorts);
    let eq2 = solver.terms.eq(key, c20, &solver.sorts);
    let eq3 = solver.terms.eq(key, c30, &solver.sorts);

    let constraint = solver.terms.or(vec![eq1, eq2, eq3], &solver.sorts);
    solver.assert_formula(constraint);

    // Enumerate models up to 10
    let models = solver.enumerate_models(&["key"], 10);
    assert_eq!(
        models.len(),
        3,
        "Should discover exactly the 3 distinct solutions"
    );

    let mut found_keys = Vec::new();
    for m in &models {
        if let Some(Value::BitVec { value, .. }) = m.get("key") {
            found_keys.push(value.clone());
        }
    }
    found_keys.sort();
    assert_eq!(found_keys, vec![10u32.into(), 20u32.into(), 30u32.into()]);
}

#[test]
fn test_decrypt_unique_key_certification() {
    let mut solver = Solver::new();
    let bv16 = solver.sorts.bv(16);
    let key = solver.declare_const("key", bv16);
    solver.set_logic("QF_BV");

    // Crackme verification equation: key ^ 0x1337 == 0xbeef
    let mask = solver
        .terms
        .bv_const(0x1337u32.into(), 16, &mut solver.sorts);
    let target = solver
        .terms
        .bv_const(0xbeefu32.into(), 16, &mut solver.sorts);
    let xor_term = solver.terms.bv_binop(Op::BvXor, key, mask).unwrap();
    let eq = solver.terms.eq(xor_term, target, &solver.sorts);
    solver.assert_formula(eq);

    let models = solver.enumerate_models(&["key"], 5);
    assert_eq!(models.len(), 1, "There should only be 1 unique solution");

    if let Some(Value::BitVec { value, .. }) = models[0].get("key") {
        let expected: u32 = 0xbeef ^ 0x1337;
        assert_eq!(*value, expected.into());
    } else {
        panic!("Key not found in model");
    }
}

#[test]
fn test_decrypt_scored_model_enumeration() {
    use smt_solver::ScoreHeuristic;

    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    let key = solver.declare_const("key", bv8);
    solver.set_logic("QF_BV");

    // Three possible solutions:
    // 1: 0x01 (binary 00000001, unprintable, 1 set bit)
    // 2: 0x41 ('A', printable ASCII, 2 set bits)
    // 3: 0xFF (binary 11111111, unprintable, 8 set bits)
    let c_bin = solver.terms.bv_const(0x01u32.into(), 8, &mut solver.sorts);
    let c_asc = solver.terms.bv_const(0x41u32.into(), 8, &mut solver.sorts);
    let c_all = solver.terms.bv_const(0xffu32.into(), 8, &mut solver.sorts);

    let eq1 = solver.terms.eq(key, c_bin, &solver.sorts);
    let eq2 = solver.terms.eq(key, c_asc, &solver.sorts);
    let eq3 = solver.terms.eq(key, c_all, &solver.sorts);

    let disj = solver.terms.or(vec![eq1, eq2, eq3], &solver.sorts);
    solver.assert_formula(disj);

    // Test ASCII Printable scoring: 'A' (0x41) should rank top
    let scored_ascii = solver.enumerate_models_scored(&["key"], 5, ScoreHeuristic::AsciiPrintable);
    assert_eq!(scored_ascii.len(), 3);
    let top_ascii = scored_ascii[0].0.get("key").unwrap();
    if let Value::BitVec { value, .. } = top_ascii {
        assert_eq!(
            *value,
            0x41u32.into(),
            "ASCII printable 'A' should score highest"
        );
    } else {
        panic!("Expected bitvector");
    }
    assert_eq!(scored_ascii[0].1, 1.0);

    // Reset solver assertions and test LowHammingWeight scoring
    solver.reset();
    let key = solver.declare_const("key", bv8);
    solver.set_logic("QF_BV");
    let c_bin = solver.terms.bv_const(0x01u32.into(), 8, &mut solver.sorts);
    let c_asc = solver.terms.bv_const(0x41u32.into(), 8, &mut solver.sorts);
    let c_all = solver.terms.bv_const(0xffu32.into(), 8, &mut solver.sorts);
    let eq1 = solver.terms.eq(key, c_bin, &solver.sorts);
    let eq2 = solver.terms.eq(key, c_asc, &solver.sorts);
    let eq3 = solver.terms.eq(key, c_all, &solver.sorts);
    let disj = solver.terms.or(vec![eq1, eq2, eq3], &solver.sorts);
    solver.assert_formula(disj);

    let scored_hw = solver.enumerate_models_scored(&["key"], 5, ScoreHeuristic::LowHammingWeight);
    assert_eq!(scored_hw.len(), 3);
    let top_hw = scored_hw[0].0.get("key").unwrap();
    if let Value::BitVec { value, .. } = top_hw {
        assert_eq!(
            *value,
            0x01u32.into(),
            "0x01 with 1 set bit should score highest on LowHammingWeight"
        );
    } else {
        panic!("Expected bitvector");
    }
}
