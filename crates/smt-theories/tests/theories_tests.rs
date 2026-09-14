use num_bigint::BigUint;
use num_rational::BigRational;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena};
use smt_sat::{LBool, SatSolver};
use smt_theories::bitvector::BitBlaster;
use smt_theories::euf::EufSolver;
use smt_theories::simplex::{Bound, DeltaRational, SimplexSolver};
use smt_theories::theory::Theory;

#[test]
fn test_euf_congruence() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let a = terms.var("a", sorts.bool_sort);
    let b = terms.var("b", sorts.bool_sort);
    let fa = terms.apply("f", vec![a], sorts.bool_sort);
    let fb = terms.apply("f", vec![b], sorts.bool_sort);

    let mut euf = EufSolver::new(&terms);
    euf.register_term(fa);
    euf.register_term(fb);
    euf.merge(a, b, None);

    assert_eq!(euf.find(fa), euf.find(fb));
}

#[test]
fn test_euf_conflict() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let a = terms.var("a", sorts.bool_sort);
    let b = terms.var("b", sorts.bool_sort);
    let eq_ab = terms.eq(a, b, &sorts);

    let mut solver = SatSolver::new();
    let var_eq = solver.new_var();
    let lit_eq = var_eq.to_lit();

    let mut euf = EufSolver::new(&terms);
    // Assert a == b
    euf.assert_term(lit_eq, eq_ab);
    // Assert a != b
    euf.assert_term(!lit_eq, eq_ab);

    let res = euf.check();
    assert!(res.is_err());
}

#[test]
fn test_simplex_feasibility() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let x = terms.var("x", sorts.real_sort);
    let mut simplex = SimplexSolver::new(&terms);
    let var_x = simplex.get_or_create_var(x, false);

    // 0 <= x <= 10
    simplex.set_lower_bound(
        var_x,
        Bound {
            value: DeltaRational::from_rational(BigRational::from_integer(0.into())),
            reason: None,
        },
    );
    simplex.set_upper_bound(
        var_x,
        Bound {
            value: DeltaRational::from_rational(BigRational::from_integer(10.into())),
            reason: None,
        },
    );

    let res = simplex.solve_simplex();
    assert!(res.is_ok());
}

#[test]
fn test_bitblaster_adder() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let c3 = terms.bv_const(BigUint::from(3u32), 4, &mut sorts);
    let c4 = terms.bv_const(BigUint::from(4u32), 4, &mut sorts);
    let sum = terms.bv_binop(Op::BvAdd, c3, c4).unwrap();
    let c7 = terms.bv_const(BigUint::from(7u32), 4, &mut sorts);
    let eq = terms.eq(sum, c7, &sorts);

    let mut solver = SatSolver::new();
    let mut bb = BitBlaster::new(&terms, &sorts);
    let eq_lit = bb.blast_bool(eq, &mut solver);
    solver.add_clause(vec![eq_lit]);

    let sat_res = solver.solve();
    assert_eq!(sat_res, LBool::True);
}

#[test]
fn test_bitblaster_unsat() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let c3 = terms.bv_const(BigUint::from(3u32), 4, &mut sorts);
    let c4 = terms.bv_const(BigUint::from(4u32), 4, &mut sorts);
    let sum = terms.bv_binop(Op::BvAdd, c3, c4).unwrap();
    let c8 = terms.bv_const(BigUint::from(8u32), 4, &mut sorts);
    let eq = terms.eq(sum, c8, &sorts);

    let mut solver = SatSolver::new();
    let mut bb = BitBlaster::new(&terms, &sorts);
    let eq_lit = bb.blast_bool(eq, &mut solver);
    solver.add_clause(vec![eq_lit]);

    let sat_res = solver.solve();
    assert_eq!(sat_res, LBool::False);
}
