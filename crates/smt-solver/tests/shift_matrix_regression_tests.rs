//! Comprehensive SMT-LIB shift matrix regression test suite.
//!
//! Validates `bvshl`, `bvlshr`, and `bvashr` across widths:
//! [1, 2, 7, 8, 16, 31, 32, 33, 64]
//! and shift amounts:
//! [0, 1, w - 1, w, w + 1, 2 * w, 255]
//! against the SMT-LIB 2.6 bit-vector standard.

use num_bigint::BigUint;
use num_traits::Zero;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena};
use smt_solver::engine::{CheckSatResult, Solver};

fn mask(w: u32) -> BigUint {
    if w == 0 {
        BigUint::zero()
    } else {
        (BigUint::from(1u32) << w) - 1u32
    }
}

fn reference_shl(val: &BigUint, shift: u64, w: u32) -> BigUint {
    if shift >= w as u64 {
        BigUint::zero()
    } else {
        (val << (shift as usize)) & mask(w)
    }
}

fn reference_lshr(val: &BigUint, shift: u64, w: u32) -> BigUint {
    if shift >= w as u64 {
        BigUint::zero()
    } else {
        (val >> (shift as usize)) & mask(w)
    }
}

fn reference_ashr(val: &BigUint, shift: u64, w: u32) -> BigUint {
    let sign_bit = (val >> (w - 1)) & BigUint::from(1u32);
    let is_neg = sign_bit == BigUint::from(1u32);
    if shift >= w as u64 {
        if is_neg {
            mask(w)
        } else {
            BigUint::zero()
        }
    } else {
        let mut r = (val >> (shift as usize)) & mask(w);
        if is_neg {
            let fill =
                ((BigUint::from(1u32) << (shift as usize)) - 1u32) << (w as usize - shift as usize);
            r = (r | fill) & mask(w);
        }
        r
    }
}

#[test]
fn test_shift_matrix_exhaustive_widths_and_shifts() {
    let widths = [1u32, 2, 7, 8, 16, 31, 32, 33, 64];

    for &w in &widths {
        let mut shifts = vec![0u64, 1, 255];
        if w > 1 {
            shifts.push((w - 1) as u64);
        }
        shifts.push(w as u64);
        shifts.push((w + 1) as u64);
        shifts.push((2 * w) as u64);

        // Filter to valid shift amounts representable in w bits (s < 2^w)
        shifts.retain(|&s| if w >= 64 { true } else { s < (1u64 << w) });
        shifts.sort_unstable();
        shifts.dedup();

        // Sample input patterns for width w
        let mut test_vals = vec![
            BigUint::zero(),
            BigUint::from(1u32) & mask(w),
            mask(w),
            (BigUint::from(1u32) << (w - 1)) & mask(w), // MSB only
        ];
        if w > 2 {
            // Alternating bit pattern: 0x5555...
            let mut alt = BigUint::zero();
            for i in 0..w {
                if i % 2 == 0 {
                    alt |= BigUint::from(1u32) << i;
                }
            }
            test_vals.push(alt & mask(w));
        }

        for val in &test_vals {
            for &s in &shifts {
                // We test BvShl, BvLshr, BvAshr
                let ops = [
                    (Op::BvShl, reference_shl(val, s, w)),
                    (Op::BvLshr, reference_lshr(val, s, w)),
                    (Op::BvAshr, reference_ashr(val, s, w)),
                ];

                for (op, expected) in ops {
                    let mut sorts = SortArena::new();
                    let mut terms = TermArena::new(&mut sorts);

                    let val_term = terms.bv_const(val.clone(), w, &mut sorts);
                    // In SMT-LIB, both arguments to shift must have the same bit-width w
                    let shift_val = BigUint::from(s) & mask(w);
                    let shift_term = terms.bv_const(shift_val, w, &mut sorts);

                    let op_res = terms
                        .bv_binop(op.clone(), val_term, shift_term)
                        .expect("Valid shift term");
                    let expected_term = terms.bv_const(expected.clone(), w, &mut sorts);

                    let mut solver = Solver::new();
                    solver.sorts = sorts;
                    solver.terms = terms;
                    solver.set_logic("QF_BV");

                    let eq = solver.terms.eq(op_res, expected_term, &solver.sorts);
                    let neq = solver.terms.not(eq);
                    solver.assert_formula(neq);

                    let sat_res = solver.check_sat();
                    assert_eq!(
                        sat_res,
                        CheckSatResult::Unsat,
                        "Shift matrix failure for width={}, op={:?}, shift={}, val={:x}: expected={:x}",
                        w,
                        op,
                        s,
                        val,
                        expected
                    );
                }
            }
        }
    }
}
