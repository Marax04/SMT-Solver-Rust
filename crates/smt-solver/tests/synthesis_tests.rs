use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena};
use smt_solver::synthesis::{Gf2LinearMbaSimplifier, IoProgramSynthesizer};

#[test]
fn test_symbolic_mba_equivalence_checking_32bit() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);

    // a = (x ^ y) + 2*(x & y)
    let xor_term = terms.bv_binop(Op::BvXor, x, y).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let two = terms.bv_const(2u32.into(), 32, &mut sorts);
    let two_and = terms.bv_binop(Op::BvMul, two, and_term).unwrap();
    let a = terms.bv_binop(Op::BvAdd, xor_term, two_and).unwrap();

    // b = x + y
    let b = terms.bv_binop(Op::BvAdd, x, y).unwrap();

    // c = x - y (not equivalent)
    let c = terms.bv_binop(Op::BvSub, x, y).unwrap();

    // SMT oracle formal verification
    assert!(
        IoProgramSynthesizer::verify_equivalence(a, b, &mut terms, &mut sorts),
        "Formal SMT oracle must prove (x ^ y) + 2*(x & y) == x + y for 32-bit width"
    );
    assert!(
        !IoProgramSynthesizer::verify_equivalence(a, c, &mut terms, &mut sorts),
        "Formal SMT oracle must refute (x ^ y) + 2*(x & y) == x - y"
    );
}

#[test]
fn test_symbolic_mba_equivalence_checking_64bit() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv64 = sorts.bv(64);
    let x = terms.var("x", bv64);
    let y = terms.var("y", bv64);

    // a = (x | y) - (x & y)
    let or_term = terms.bv_binop(Op::BvOr, x, y).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let a = terms.bv_binop(Op::BvSub, or_term, and_term).unwrap();

    // b = x ^ y
    let b = terms.bv_binop(Op::BvXor, x, y).unwrap();

    assert!(
        IoProgramSynthesizer::verify_equivalence(a, b, &mut terms, &mut sorts),
        "Formal SMT oracle must prove (x | y) - (x & y) == x ^ y for 64-bit width"
    );
}

#[test]
fn test_io_synthesis_and_verification_pipeline() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);

    let xor_term = terms.bv_binop(Op::BvXor, x, y).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let two = terms.bv_const(2u32.into(), 32, &mut sorts);
    let two_and = terms.bv_binop(Op::BvMul, two, and_term).unwrap();
    let mba_expr = terms.bv_binop(Op::BvAdd, xor_term, two_and).unwrap();

    let synthesized = IoProgramSynthesizer::synthesize(mba_expr, &mut terms, &mut sorts);
    assert!(synthesized.is_some());
    let syn_id = synthesized.unwrap();
    let t = terms.get(syn_id);
    assert_eq!(t.op, Op::BvAdd);
}

#[test]
fn test_gf2_linear_mba_simplifier_oracle_pipeline() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);

    let v0 = terms.var("v0", bv32);
    let _v1 = terms.var("v1", bv32);
    let _v2 = terms.var("v2", bv32);
    let _v3 = terms.var("v3", bv32);
    let v4 = terms.var("v4", bv32);

    // (v0 | v4) - (v0 & v4) == v0 ^ v4
    let or_term = terms.bv_binop(Op::BvOr, v0, v4).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, v0, v4).unwrap();
    let mba_expr = terms.bv_binop(Op::BvSub, or_term, and_term).unwrap();

    let simplified = Gf2LinearMbaSimplifier::simplify(mba_expr, &mut terms, &mut sorts);
    assert!(simplified.is_some());
    let res = simplified.unwrap();
    let term = terms.get(res);
    assert_eq!(term.op, Op::BvXor);
}

#[test]
fn test_equivalence_counterexample_model_extraction() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);

    // a = x + y
    let a = terms.bv_binop(Op::BvAdd, x, y).unwrap();
    // b = x - y (not equivalent)
    let b = terms.bv_binop(Op::BvSub, x, y).unwrap();

    let res =
        IoProgramSynthesizer::verify_equivalence_with_counterexample(a, b, &mut terms, &mut sorts);
    assert!(
        res.is_err(),
        "Non-equivalent expressions must return Err(model)"
    );

    let counterexample = res.unwrap_err();
    // Counterexample model must contain assignments for x and y
    assert!(
        counterexample.get("y").is_some(),
        "Counterexample must assign variable y to prove discrepancy"
    );

    // Verify counterexample witness: evaluating a and b on model yields distinct results
    let mut validator = smt_solver::validator::ModelValidator::new();
    let val_a = validator
        .evaluate(a, &counterexample, &terms, &sorts)
        .unwrap();
    let val_b = validator
        .evaluate(b, &counterexample, &terms, &sorts)
        .unwrap();
    assert_ne!(
        val_a, val_b,
        "Counterexample model must produce different concrete values: {:?} != {:?}",
        val_a, val_b
    );
}

#[test]
fn test_smtlib_qf_bv_edge_cases_semantics() {
    use smt_solver::engine::Solver;

    let mut solver = Solver::new();
    solver.set_logic("QF_BV");

    // SMT-LIB standard edge cases:
    // 1. (bvudiv x (_ bv0 32)) == #xffffffff
    // 2. (bvurem x (_ bv0 32)) == x
    // 3. (bvlshr x (_ bv32 32)) == #x00000000
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (distinct (bvudiv x (_ bv0 32)) (_ bv4294967295 32)))
(check-sat)
"#;
    let res = solver.execute_script(script).unwrap();
    assert_eq!(
        res.join(" ").trim(),
        "unsat",
        "SMT-LIB division by zero must equal all 1s (4294967295) for all x"
    );

    let script2 = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (distinct (bvurem x (_ bv0 32)) x))
(check-sat)
"#;
    let mut solver2 = Solver::new();
    let res2 = solver2.execute_script(script2).unwrap();
    assert_eq!(
        res2.join(" ").trim(),
        "unsat",
        "SMT-LIB remainder by zero must equal the dividend x for all x"
    );

    let script3 = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (distinct (bvlshr x (_ bv32 32)) (_ bv0 32)))
(check-sat)
"#;
    let mut solver3 = Solver::new();
    let res3 = solver3.execute_script(script3).unwrap();
    assert_eq!(
        res3.join(" ").trim(),
        "unsat",
        "SMT-LIB shift right by >= bitwidth must equal zero for all x"
    );
}
