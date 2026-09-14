//! Differential Testing & Grammar-Based Fuzzing Harness for QF_BV and QF_LRA.

use num_bigint::BigUint;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_preprocess::Rewriter;
use smt_solver::engine::{CheckSatResult, Solver};
use smt_solver::validator::ModelValidator;

/// Simple deterministic PRNG (Xorshift64) to ensure reproducible fuzz runs.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn next_u32(&mut self, max: u32) -> u32 {
        if max == 0 {
            0
        } else {
            (self.next_u64() % (max as u64)) as u32
        }
    }
    fn next_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

/// Generates a random bit-vector expression of a given width and depth.
fn gen_random_bv(
    depth: usize,
    width: u32,
    vars: &[TermId],
    rng: &mut Rng,
    terms: &mut TermArena,
    sorts: &mut SortArena,
) -> TermId {
    if depth == 0 || rng.next_bool() {
        if !vars.is_empty() && rng.next_bool() {
            let idx = rng.next_u32(vars.len() as u32) as usize;
            vars[idx]
        } else {
            let val = BigUint::from(rng.next_u64() & ((1u64 << width.min(63)) - 1));
            terms.bv_const(val, width, sorts)
        }
    } else {
        let op_choice = rng.next_u32(8);
        match op_choice {
            0 => {
                let inner = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let sort = terms.sort_of(inner);
                terms.intern(Op::BvNot, vec![inner], sort)
            }
            1 => {
                let inner = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let sort = terms.sort_of(inner);
                terms.intern(Op::BvNeg, vec![inner], sort)
            }
            2 => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvAdd, a, b).unwrap()
            }
            3 => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvSub, a, b).unwrap()
            }
            4 => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvAnd, a, b).unwrap()
            }
            5 => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvOr, a, b).unwrap()
            }
            6 => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvXor, a, b).unwrap()
            }
            _ => {
                let a = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                let b = gen_random_bv(depth - 1, width, vars, rng, terms, sorts);
                terms.bv_binop(Op::BvMul, a, b).unwrap()
            }
        }
    }
}

#[test]
fn test_fuzz_bv_model_soundness() {
    let mut rng = Rng::new(0xdeadbeef_cafebabe);

    for iteration in 0..50 {
        let mut solver = Solver::new();
        solver.set_logic("QF_BV");

        let sort_bv8 = solver.sorts.bv(8);
        let x = solver.declare_const("x", sort_bv8);
        let y = solver.declare_const("y", sort_bv8);
        let vars = vec![x, y];

        let lhs = gen_random_bv(3, 8, &vars, &mut rng, &mut solver.terms, &mut solver.sorts);
        let rhs = gen_random_bv(2, 8, &vars, &mut rng, &mut solver.terms, &mut solver.sorts);
        let formula = solver.terms.eq(lhs, rhs, &solver.sorts);

        solver.assert_formula(formula);
        let res = solver.check_sat();

        if res == CheckSatResult::Sat {
            let model = solver.get_model().expect("SAT outcome must have a model");
            let mut validator = ModelValidator::new();
            let valid = validator.validate(&[formula], model, &solver.terms, &solver.sorts);
            assert!(
                valid.is_ok(),
                "Fuzz iteration {} produced invalid model: {:?}",
                iteration,
                valid.err()
            );
        }
    }
}

#[test]
fn test_fuzz_rewriter_differential_equivalence() {
    let mut rng = Rng::new(0x12345678_9abcdef0);

    for _ in 0..50 {
        let mut sorts = SortArena::new();
        let mut terms = TermArena::new(&mut sorts);

        let sort_bv8 = sorts.bv(8);
        let x = terms.var("x".to_string(), sort_bv8);
        let y = terms.var("y".to_string(), sort_bv8);
        let vars = vec![x, y];

        let expr = gen_random_bv(4, 8, &vars, &mut rng, &mut terms, &mut sorts);
        let mut rewriter = Rewriter::new(&mut terms, &mut sorts);
        let simplified = rewriter.rewrite(expr);

        // Verify with concrete evaluation across sample values
        for val_x in [0u32, 1, 42, 255] {
            for val_y in [0u32, 1, 13, 254] {
                let mut model = smt_solver::model::Model::new();
                model.insert("x", smt_core::value::Value::new_bv(val_x.into(), 8));
                model.insert("y", smt_core::value::Value::new_bv(val_y.into(), 8));

                let mut val1 = ModelValidator::new();
                let v1 = val1.evaluate(expr, &model, &terms, &sorts).unwrap();

                let mut val2 = ModelValidator::new();
                let v2 = val2.evaluate(simplified, &model, &terms, &sorts).unwrap();

                assert_eq!(
                    v1, v2,
                    "Rewriter changed semantics! x={}, y={}, orig={:?}, simplified={:?}",
                    val_x, val_y, expr, simplified
                );
            }
        }
    }
}
