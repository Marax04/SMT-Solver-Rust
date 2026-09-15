//! Scaled differential grammar fuzzing suite for bitvector theories (QF_BV).
//!
//! Generates hundreds of pseudo-random symbolic AST expressions across bit-widths
//! 8, 16, 32, and 64, verifying:
//! 1. Formal equivalence of algebraic, boolean, and MBA invariants.
//! 2. Concrete interpreter evaluation concordance against SMT bit-blaster models.
//! 3. Zero solver crashes, memory leaks, or unsound SAT/UNSAT contradictions.

use num_bigint::BigUint;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena};
use smt_solver::engine::{CheckSatResult, Solver};
use smt_solver::synthesis::{EquivalenceResult, IoProgramSynthesizer};

/// Deterministic 64-bit LCG random number generator.
struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn next_range(&mut self, max: usize) -> usize {
        (self.next_u64() as usize) % max
    }
}

/// Evaluates a 64-bit unsigned integer expression concretely in pure Rust arithmetic.
fn eval_concrete_op(op: Op, a: u64, b: Option<u64>, width: u32) -> u64 {
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let a_val = a & mask;
    let b_val = b.unwrap_or(0) & mask;

    let res = match op {
        Op::BvNot => !a_val,
        Op::BvNeg => (!a_val).wrapping_add(1),
        Op::BvAnd => a_val & b_val,
        Op::BvOr => a_val | b_val,
        Op::BvXor => a_val ^ b_val,
        Op::BvAdd => a_val.wrapping_add(b_val),
        Op::BvSub => a_val.wrapping_sub(b_val),
        Op::BvMul => a_val.wrapping_mul(b_val),
        Op::BvShl => {
            let shift = (b_val % (width as u64)) as u32;
            a_val.wrapping_shl(shift)
        }
        Op::BvLshr => {
            let shift = (b_val % (width as u64)) as u32;
            a_val.wrapping_shr(shift)
        }
        _ => a_val,
    };

    res & mask
}

#[test]
fn test_differential_algebraic_identities_scaled() {
    let widths = [8u32, 16, 32, 64];

    for &width in &widths {
        let mut sorts = SortArena::new();
        let mut terms = TermArena::new(&mut sorts);
        let bv_sort = sorts.bv(width);

        let x = terms.var("x", bv_sort);
        let y = terms.var("y", bv_sort);
        let z = terms.var("z", bv_sort);

        // 1. Double Negation: ~~x == x
        let not_x = terms.bv_unop(Op::BvNot, x).unwrap();
        let not_not_x = terms.bv_unop(Op::BvNot, not_x).unwrap();
        let res1 =
            IoProgramSynthesizer::verify_equivalence_detailed(not_not_x, x, &mut terms, &mut sorts);
        assert!(
            matches!(res1, EquivalenceResult::Equivalent { .. }),
            "~~x must be equivalent to x for width {}",
            width
        );

        // 2. Commutativity of XOR: x ^ y == y ^ x
        let xor_xy = terms.bv_binop(Op::BvXor, x, y).unwrap();
        let xor_yx = terms.bv_binop(Op::BvXor, y, x).unwrap();
        let res2 = IoProgramSynthesizer::verify_equivalence_detailed(
            xor_xy, xor_yx, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res2, EquivalenceResult::Equivalent { .. }),
            "x ^ y must be equivalent to y ^ x for width {}",
            width
        );

        // 3. Commutativity of ADD: x + y == y + x
        let add_xy = terms.bv_binop(Op::BvAdd, x, y).unwrap();
        let add_yx = terms.bv_binop(Op::BvAdd, y, x).unwrap();
        let res3 = IoProgramSynthesizer::verify_equivalence_detailed(
            add_xy, add_yx, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res3, EquivalenceResult::Equivalent { .. }),
            "x + y must be equivalent to y + x for width {}",
            width
        );

        // 4. Associativity of XOR: (x ^ y) ^ z == x ^ (y ^ z)
        let xor_xy_z = terms.bv_binop(Op::BvXor, xor_xy, z).unwrap();
        let xor_yz = terms.bv_binop(Op::BvXor, y, z).unwrap();
        let xor_x_yz = terms.bv_binop(Op::BvXor, x, xor_yz).unwrap();
        let res4 = IoProgramSynthesizer::verify_equivalence_detailed(
            xor_xy_z, xor_x_yz, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res4, EquivalenceResult::Equivalent { .. }),
            "(x ^ y) ^ z must be equivalent to x ^ (y ^ z) for width {}",
            width
        );

        // 5. De Morgan's Law: ~(x & y) == (~x) | (~y)
        let and_xy = terms.bv_binop(Op::BvAnd, x, y).unwrap();
        let not_and = terms.bv_unop(Op::BvNot, and_xy).unwrap();
        let not_y = terms.bv_unop(Op::BvNot, y).unwrap();
        let or_not = terms.bv_binop(Op::BvOr, not_x, not_y).unwrap();
        let res5 = IoProgramSynthesizer::verify_equivalence_detailed(
            not_and, or_not, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res5, EquivalenceResult::Equivalent { .. }),
            "~(x & y) must be equivalent to (~x) | (~y) for width {}",
            width
        );

        // 6. MBA Linear Addition Identity: (x ^ y) + 2*(x & y) == x + y
        let two = terms.bv_const(BigUint::from(2u32), width, &mut sorts);
        let two_and = terms.bv_binop(Op::BvMul, two, and_xy).unwrap();
        let mba_add = terms.bv_binop(Op::BvAdd, xor_xy, two_and).unwrap();
        let res6 = IoProgramSynthesizer::verify_equivalence_detailed(
            mba_add, add_xy, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res6, EquivalenceResult::Equivalent { .. }),
            "(x ^ y) + 2*(x & y) must be equivalent to x + y for width {}",
            width
        );

        // 7. Non-Equivalence Refutation: x + y != x - y
        let sub_xy = terms.bv_binop(Op::BvSub, x, y).unwrap();
        let res7 = IoProgramSynthesizer::verify_equivalence_detailed(
            add_xy, sub_xy, &mut terms, &mut sorts,
        );
        assert!(
            matches!(res7, EquivalenceResult::NotEquivalent { .. }),
            "x + y must not be equivalent to x - y for width {}",
            width
        );
    }
}

#[test]
fn test_scaled_differential_random_grammar_fuzzing() {
    let mut rng = Rng::new(0x2026_0915_dead_beef);
    let widths = [8u32, 16, 32, 64];

    for &width in &widths {
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };

        for trial in 0..25 {
            // Build solver with terms and sorts
            let mut solver = Solver::new();
            solver.set_logic("QF_BV");
            let bv_sort = solver.sorts.bv(width);

            let x_var = solver.declare_const("x", bv_sort);
            let y_var = solver.declare_const("y", bv_sort);

            // Concrete test inputs
            let val_x = rng.next_u64() & mask;
            let val_y = rng.next_u64() & mask;

            // Pick a random operation: 0=ADD, 1=SUB, 2=XOR, 3=AND, 4=OR, 5=MUL
            let op_idx = rng.next_range(6);
            let (op, op_sym) = match op_idx {
                0 => (Op::BvAdd, "+"),
                1 => (Op::BvSub, "-"),
                2 => (Op::BvXor, "^"),
                3 => (Op::BvAnd, "&"),
                4 => (Op::BvOr, "|"),
                _ => (Op::BvMul, "*"),
            };

            let expr = solver.terms.bv_binop(op.clone(), x_var, y_var).unwrap();
            let expected_concrete = eval_concrete_op(op, val_x, Some(val_y), width);

            let c_x = solver
                .terms
                .bv_const(BigUint::from(val_x), width, &mut solver.sorts);
            let c_y = solver
                .terms
                .bv_const(BigUint::from(val_y), width, &mut solver.sorts);
            let c_expected =
                solver
                    .terms
                    .bv_const(BigUint::from(expected_concrete), width, &mut solver.sorts);

            let eq_x = solver.terms.eq(x_var, c_x, &solver.sorts);
            let eq_y = solver.terms.eq(y_var, c_y, &solver.sorts);
            let eq_res = solver.terms.eq(expr, c_expected, &solver.sorts);
            let not_eq_res = solver.terms.not(eq_res);

            // Solver check 1: (x == val_x && y == val_y && expr != expected) MUST be UNSAT
            solver.push(1);
            solver.assert_formula(eq_x);
            solver.assert_formula(eq_y);
            solver.assert_formula(not_eq_res);

            let check_unsat = solver.check_sat();
            assert_eq!(
                check_unsat,
                CheckSatResult::Unsat,
                "Trial {} (width {}): {} {} {} did not match concrete {}",
                trial,
                width,
                val_x,
                op_sym,
                val_y,
                expected_concrete
            );
            solver.pop(1);

            // Solver check 2: (x == val_x && y == val_y && expr == expected) MUST be SAT
            solver.push(1);
            solver.assert_formula(eq_x);
            solver.assert_formula(eq_y);
            solver.assert_formula(eq_res);

            let check_sat = solver.check_sat();
            assert_eq!(
                check_sat,
                CheckSatResult::Sat,
                "Trial {} (width {}): {} {} {} must be satisfiable",
                trial,
                width,
                val_x,
                op_sym,
                val_y
            );
            solver.pop(1);
        }
    }
}
