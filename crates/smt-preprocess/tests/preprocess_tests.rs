use num_bigint::BigUint;
use smt_core::sort::SortArena;
use smt_core::term::TermArena;
use smt_preprocess::{ConstantFolder, Rewriter, TseitinEncoder};
use smt_sat::{LBool, SatSolver};

#[test]
fn test_constant_folding_bv() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let c5 = terms.bv_const(BigUint::from(5u32), 32, &mut sorts);
    let c7 = terms.bv_const(BigUint::from(7u32), 32, &mut sorts);
    let sum = terms.bv_binop(smt_core::term::Op::BvAdd, c5, c7).unwrap();

    let mut folder = ConstantFolder::new(&mut terms, &mut sorts);
    let folded = folder.fold_term(sum);

    if let smt_core::term::Op::BvConst { value, width } = folder.terms.op_of(folded) {
        assert_eq!(*value, BigUint::from(12u32));
        assert_eq!(*width, 32);
    } else {
        panic!("Expected BvConst");
    }
}

#[test]
fn test_rewriter_identities() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let x = terms.var("x", sorts.bool_sort);
    let not_x = terms.not(x);
    let not_not_x = terms.not(not_x);

    let mut folder = ConstantFolder::new(&mut terms, &mut sorts);
    let folded = folder.fold_term(not_not_x);
    assert_eq!(folded, x);

    let mut rewriter = Rewriter::new(&mut terms, &mut sorts);
    let eq_x_x = rewriter.terms.eq(x, x, rewriter.sorts);
    let rewritten = rewriter.rewrite(eq_x_x);
    assert_eq!(rewritten, rewriter.terms.true_id);
}

#[test]
fn test_tseitin_cnf() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let a = terms.var("a", sorts.bool_sort);
    let b = terms.var("b", sorts.bool_sort);
    let a_and_b = terms.and(vec![a, b], &sorts);

    let mut solver = SatSolver::new();
    let mut tseitin = TseitinEncoder::new();
    tseitin.assert_formula(a_and_b, &mut solver, &terms);

    let res = solver.solve();
    assert_eq!(res, LBool::True);
}
