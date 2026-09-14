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
