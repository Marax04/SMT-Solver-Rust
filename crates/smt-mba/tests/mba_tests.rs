use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena};
use smt_mba::synthesis::IoProgramSynthesizer;
use smt_mba::MbaSimplifier;

#[test]
fn test_linear_mba_xor_and() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);

    // (x ^ y) + 2*(x & y) == x + y
    let xor_term = terms.bv_binop(Op::BvXor, x, y).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let two = terms.bv_const(2u32.into(), 32, &mut sorts);
    let two_and = terms.bv_binop(Op::BvMul, two, and_term).unwrap();
    let mba_expr = terms.bv_binop(Op::BvAdd, xor_term, two_and).unwrap();

    let mut simplifier = MbaSimplifier::new();
    let simplified = simplifier.simplify(mba_expr, &mut terms, &mut sorts);

    let term = terms.get(simplified);
    assert_eq!(term.op, Op::BvAdd);
    assert_eq!(term.args.len(), 2);
    assert_eq!(term.args[0], x);
    assert_eq!(term.args[1], y);
}

#[test]
fn test_linear_mba_or_and() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);

    // (x | y) - (x & y) == x ^ y
    let or_term = terms.bv_binop(Op::BvOr, x, y).unwrap();
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let mba_expr = terms.bv_binop(Op::BvSub, or_term, and_term).unwrap();

    let mut simplifier = MbaSimplifier::new();
    let simplified = simplifier.simplify(mba_expr, &mut terms, &mut sorts);

    let term = terms.get(simplified);
    assert_eq!(term.op, Op::BvXor);
    assert_eq!(term.args.len(), 2);
    assert_eq!(term.args[0], x);
    assert_eq!(term.args[1], y);
}

#[test]
fn test_canonicalize_double_negation() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let not_x = terms.intern(Op::BvNot, vec![x], bv32);
    let not_not_x = terms.intern(Op::BvNot, vec![not_x], bv32);

    let mut simplifier = MbaSimplifier::new();
    let simplified = simplifier.simplify(not_not_x, &mut terms, &mut sorts);

    assert_eq!(simplified, x);
}

#[test]
fn test_canonicalize_de_morgan() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);
    let y = terms.var("y", bv32);
    // ~(x & y) => ~x | ~y
    let and_term = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let not_and = terms.intern(Op::BvNot, vec![and_term], bv32);

    let simplified = smt_mba::MbaCanonicalizer::normalize(not_and, &mut terms, &mut sorts);

    let term = terms.get(simplified);
    assert_eq!(term.op, Op::BvOr);
    assert_eq!(term.args.len(), 2);
}

#[test]
fn test_mba_synthesis_linear_identity() {
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
    assert!(
        synthesized.is_some(),
        "Synthesis should find an equivalent simple expression"
    );
    let syn_term = synthesized.unwrap();
    let term = terms.get(syn_term);
    assert_eq!(term.op, Op::BvAdd);
    assert_eq!(term.args[0], x);
    assert_eq!(term.args[1], y);
}

#[test]
fn test_gf2_matrix_rref() {
    use smt_mba::Gf2Matrix;

    // Create a 3x4 augmented matrix [A | b]
    // Row 0: 1 0 1 | 1   (x0 + x2 = 1)
    // Row 1: 0 1 1 | 0   (x1 + x2 = 0)
    // Row 2: 1 1 0 | 1   (x0 + x1 = 1) -> redundant with (row 0 + row 1)
    let mut mat = Gf2Matrix::new(3, 4);
    mat.set(0, 0, true);
    mat.set(0, 2, true);
    mat.set(0, 3, true);

    mat.set(1, 1, true);
    mat.set(1, 2, true);

    mat.set(2, 0, true);
    mat.set(2, 1, true);
    mat.set(2, 3, true);

    let pivots = mat.rref();
    assert_eq!(pivots.len(), 2);
    // Row 2 should now be all zeros
    assert!(!mat.get(2, 0));
    assert!(!mat.get(2, 1));
    assert!(!mat.get(2, 2));
    assert!(!mat.get(2, 3));
}

#[test]
fn test_gf2_mba_5_variables() {
    use smt_mba::Gf2LinearMbaSimplifier;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);

    // Create 5 variables: v0, v1, v2, v3, v4
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
    assert!(
        simplified.is_some(),
        "GF(2) simplifier should handle 5+ variable context"
    );
    let res = simplified.unwrap();
    let term = terms.get(res);
    assert_eq!(term.op, Op::BvXor);
    assert_eq!(term.args.len(), 2);
}

#[test]
fn test_zhegalkin_anf_canonicalize() {
    use num_traits::Zero;
    use smt_mba::ZhegalkinPolynomial;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv32 = sorts.bv(32);
    let x = terms.var("x", bv32);

    // x ^ x == 0
    let x_xor_x = terms.bv_binop(Op::BvXor, x, x).unwrap();
    let simplified = ZhegalkinPolynomial::simplify(x_xor_x, &mut terms, &mut sorts);
    assert!(simplified.is_some());
    let res = simplified.unwrap();
    let term = terms.get(res);
    match term.op {
        Op::BvConst { ref value, .. } => assert!(value.is_zero()),
        _ => panic!("Expected BvConst 0, got {:?}", term.op),
    }
}

#[test]
fn test_gf2_matrix_rref_16_and_32_variables() {
    use smt_mba::Gf2Matrix;

    // 1. Stress test 16x32 augmented matrix over GF(2)
    let n16 = 16;
    let mut mat16 = Gf2Matrix::new(n16, 2 * n16);
    // Fill left side with a non-singular triangular + band matrix
    for i in 0..n16 {
        mat16.set(i, i, true);
        if i + 1 < n16 {
            mat16.set(i, i + 1, true);
        }
        if (i + 3) < n16 {
            mat16.set(i, i + 3, true);
        }
        // Right side identity matrix
        mat16.set(i, n16 + i, true);
    }

    let pivots16 = mat16.rref();
    assert_eq!(
        pivots16.len(),
        n16,
        "16-variable invertible system must have full rank 16"
    );
    // Verify RREF properties: strictly increasing pivots, 1 on pivot, 0 elsewhere in column
    let mut prev_col = None;
    for (row, &col) in pivots16.iter().enumerate() {
        if let Some(prev) = prev_col {
            assert!(col > prev, "Pivots must be strictly increasing");
        }
        prev_col = Some(col);
        assert!(mat16.get(row, col), "Pivot position must be 1");
        for r in 0..n16 {
            if r != row {
                assert!(
                    !mat16.get(r, col),
                    "Column {} must be zero outside pivot row {}",
                    col,
                    row
                );
            }
        }
    }

    // 2. Stress test 32x64 multi-word augmented matrix over GF(2)
    // cols = 64 tests boundary across 64-bit word storage!
    let n32 = 32;
    let mut mat32 = Gf2Matrix::new(n32, 2 * n32);
    for i in 0..n32 {
        mat32.set(i, i, true);
        if i + 1 < n32 {
            mat32.set(i, i + 1, true);
        }
        if i + 5 < n32 {
            mat32.set(i, i + 5, true);
        }
        // Identity in second word block
        mat32.set(i, n32 + i, true);
    }

    let pivots32 = mat32.rref();
    assert_eq!(
        pivots32.len(),
        n32,
        "32-variable multi-word system must have full rank 32"
    );
    let mut prev_col32 = None;
    for (row, &col) in pivots32.iter().enumerate() {
        if let Some(prev) = prev_col32 {
            assert!(col > prev);
        }
        prev_col32 = Some(col);
        assert!(mat32.get(row, col));
        for r in 0..n32 {
            if r != row {
                assert!(!mat32.get(r, col));
            }
        }
    }
}

#[test]
fn test_zhegalkin_exhaustive_semantic_roundtrip() {
    use smt_mba::ZhegalkinPolynomial;
    use smt_solver::model::Model;
    use smt_solver::validator::ModelValidator;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv1 = sorts.bv(1);

    let x = terms.var("x", bv1);
    let y = terms.var("y", bv1);
    let z = terms.var("z", bv1);

    // Test multiple non-trivial boolean functions:
    // f1: Majority(x, y, z) = (x & y) | (y & z) | (x & z)
    let xy = terms.bv_binop(Op::BvAnd, x, y).unwrap();
    let yz = terms.bv_binop(Op::BvAnd, y, z).unwrap();
    let xz = terms.bv_binop(Op::BvAnd, x, z).unwrap();
    let xy_or_yz = terms.bv_binop(Op::BvOr, xy, yz).unwrap();
    let maj = terms.bv_binop(Op::BvOr, xy_or_yz, xz).unwrap();

    // f2: Multiplexer: (x & y) | (~x & z)
    let not_x = terms.intern(Op::BvNot, vec![x], bv1);
    let not_x_z = terms.bv_binop(Op::BvAnd, not_x, z).unwrap();
    let mux = terms.bv_binop(Op::BvOr, xy, not_x_z).unwrap();

    // f3: Complex nested XOR/AND/OR: (x ^ y) | ~(y & z)
    let x_xor_y = terms.bv_binop(Op::BvXor, x, y).unwrap();
    let not_yz = terms.intern(Op::BvNot, vec![yz], bv1);
    let complex = terms.bv_binop(Op::BvOr, x_xor_y, not_yz).unwrap();

    let test_cases = vec![
        ("Majority", maj),
        ("Multiplexer", mux),
        ("Complex_MBA_Bool", complex),
    ];

    for (name, orig_term) in test_cases {
        let simplified =
            ZhegalkinPolynomial::simplify(orig_term, &mut terms, &mut sorts).unwrap_or(orig_term);

        // Exhaustively test all 2^3 = 8 truth table inputs
        let mut validator = ModelValidator::new();
        for vx in [0u32, 1u32] {
            for vy in [0u32, 1u32] {
                for vz in [0u32, 1u32] {
                    let mut model = Model::new();
                    model.insert("x", smt_core::value::Value::new_bv(vx.into(), 1));
                    model.insert("y", smt_core::value::Value::new_bv(vy.into(), 1));
                    model.insert("z", smt_core::value::Value::new_bv(vz.into(), 1));

                    let v_orig = validator
                        .evaluate(orig_term, &model, &terms, &sorts)
                        .expect("Original term should evaluate concretely");
                    let v_simp = validator
                        .evaluate(simplified, &model, &terms, &sorts)
                        .expect("Reconstructed Zhegalkin ANF term should evaluate concretely");

                    assert_eq!(
                        v_orig, v_simp,
                        "Semantic mismatch in {} for input x={}, y={}, z={}",
                        name, vx, vy, vz
                    );
                }
            }
        }
    }
}

#[test]
fn test_gf2_rref_scaling_curve() {
    use smt_mba::Gf2Matrix;
    use std::time::Instant;

    // Statistically sound scaling curve: RREF at 8, 16, 32, 64, 128 variables.
    // To eliminate measurement noise, cold-start timer artifacts, and CPU frequency
    // scaling transients, each size runs:
    //   1. Warm-up phase: 200 iterations discarded
    //   2. Measurement phase: 500 timed iterations
    //   3. Metrics: Mean, Min, Median, and Sample StdDev (in nanoseconds)
    let sizes: &[usize] = &[8, 16, 32, 64, 128];
    const WARMUP_ITERS: usize = 200;
    const BENCH_ITERS: usize = 500;

    println!("\n[GF2 RREF Statistical Scaling Curve (500 iterations after 200 warm-up)]");
    println!(
        "{:>8}  {:>8}  {:>8}  {:>12}  {:>10}  {:>10}  {:>10}",
        "vars (n)", "rows", "cols", "mean (ns)", "min (ns)", "median (ns)", "stddev (ns)"
    );
    println!("{}", "-".repeat(78));

    fn build_band_matrix(n: usize) -> Gf2Matrix {
        let cols = 2 * n; // augmented [A | I]
        let mut mat = Gf2Matrix::new(n, cols);
        for i in 0..n {
            mat.set(i, i, true); // main diagonal
            if i + 1 < n {
                mat.set(i, i + 1, true); // +1 band
            }
            if i + 3 < n {
                mat.set(i, i + 3, true); // +3 band
            }
            // Identity block on the right (columns n..2n)
            mat.set(i, n + i, true);
        }
        mat
    }

    for &n in sizes {
        let cols = 2 * n;

        // 1. Warm-up phase
        for _ in 0..WARMUP_ITERS {
            let mut mat = build_band_matrix(n);
            let _ = mat.rref();
        }

        // 2. Timed measurement phase
        let mut times_ns = Vec::with_capacity(BENCH_ITERS);
        let mut last_mat = build_band_matrix(n);
        let mut last_pivots = Vec::new();

        for _ in 0..BENCH_ITERS {
            let mut mat = build_band_matrix(n);
            let t0 = Instant::now();
            let pivots = mat.rref();
            let elapsed_ns = t0.elapsed().as_nanos() as f64;
            times_ns.push(elapsed_ns);
            last_mat = mat;
            last_pivots = pivots;
        }

        times_ns.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let count = times_ns.len() as f64;
        let mean = times_ns.iter().sum::<f64>() / count;
        let min = times_ns[0];
        let median = times_ns[times_ns.len() / 2];
        let variance = times_ns.iter().map(|&t| (t - mean).powi(2)).sum::<f64>() / (count - 1.0);
        let stddev = variance.sqrt();

        println!(
            "{:>8}  {:>8}  {:>8}  {:>12.1}  {:>10.0}  {:>10.0}  {:>10.1}",
            n, n, cols, mean, min, median, stddev
        );

        // 3. Correctness assertions: must reach full rank
        assert_eq!(
            last_pivots.len(),
            n,
            "n={}: expected full rank {}, got {}",
            n,
            n,
            last_pivots.len()
        );

        // Verify RREF invariants: strict pivot column ordering,
        // 1 on pivot, 0 in every other row of same column.
        let mut prev_col: Option<usize> = None;
        for (row, &col) in last_pivots.iter().enumerate() {
            if let Some(prev) = prev_col {
                assert!(
                    col > prev,
                    "n={}: pivot cols must be strictly increasing",
                    n
                );
            }
            prev_col = Some(col);
            assert!(last_mat.get(row, col), "n={}: pivot position must be 1", n);
            for r in 0..n {
                if r != row {
                    assert!(
                        !last_mat.get(r, col),
                        "n={}: non-pivot entry at ({}, {}) must be 0",
                        n,
                        r,
                        col
                    );
                }
            }
        }
    }
}

#[test]
fn test_zhegalkin_exhaustive_6_variables() {
    use smt_core::term::Op;
    use smt_mba::ZhegalkinPolynomial;
    use smt_solver::model::Model;
    use smt_solver::validator::ModelValidator;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv1 = sorts.bv(1);

    let v = [
        terms.var("a", bv1),
        terms.var("b", bv1),
        terms.var("c", bv1),
        terms.var("d", bv1),
        terms.var("e", bv1),
        terms.var("f", bv1),
    ];

    // f1: 3-variable majority applied to (a,b,c) XOR-combined with parity(d,e,f)
    // Majority(a,b,c) = (a&b) | (b&c) | (a&c)
    let ab = terms.bv_binop(Op::BvAnd, v[0], v[1]).unwrap();
    let bc = terms.bv_binop(Op::BvAnd, v[1], v[2]).unwrap();
    let ac = terms.bv_binop(Op::BvAnd, v[0], v[2]).unwrap();
    let ab_bc = terms.bv_binop(Op::BvOr, ab, bc).unwrap();
    let maj_abc = terms.bv_binop(Op::BvOr, ab_bc, ac).unwrap();

    // Parity(d,e,f) = d ^ e ^ f
    let de = terms.bv_binop(Op::BvXor, v[3], v[4]).unwrap();
    let parity_def = terms.bv_binop(Op::BvXor, de, v[5]).unwrap();

    // Combined: Majority(a,b,c) XOR Parity(d,e,f)
    let combined = terms.bv_binop(Op::BvXor, maj_abc, parity_def).unwrap();

    let simplified =
        ZhegalkinPolynomial::simplify(combined, &mut terms, &mut sorts).unwrap_or(combined);

    let var_names = ["a", "b", "c", "d", "e", "f"];
    let mut validator = ModelValidator::new();
    let mut count = 0u32;

    // Exhaustive: 2^6 = 64 truth table rows
    for bits in 0u32..64 {
        let mut model = Model::new();
        for (i, &name) in var_names.iter().enumerate() {
            let val = (bits >> i) & 1;
            model.insert(name, smt_core::value::Value::new_bv(val.into(), 1));
        }
        let v_orig = validator
            .evaluate(combined, &model, &terms, &sorts)
            .expect("Original 6-var combined term must evaluate");
        let v_simp = validator
            .evaluate(simplified, &model, &terms, &sorts)
            .expect("Zhegalkin-simplified 6-var term must evaluate");
        assert_eq!(
            v_orig, v_simp,
            "6-var semantic mismatch at input bits={:#08b}",
            bits
        );
        count += 1;
    }
    assert_eq!(count, 64, "Must have tested all 2^6 = 64 inputs");
    println!("[Zhegalkin 6-var] {} inputs verified OK", count);
}

#[test]
fn test_zhegalkin_exhaustive_8_variables() {
    use smt_core::term::Op;
    use smt_mba::ZhegalkinPolynomial;
    use smt_solver::model::Model;
    use smt_solver::validator::ModelValidator;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let bv1 = sorts.bv(1);

    let v: Vec<_> = ["a", "b", "c", "d", "e", "f", "g", "h"]
        .iter()
        .map(|&n| terms.var(n, bv1))
        .collect();

    // f: carry-lookahead-style function over 8 bits.
    // P_i = a_i XOR b_i (propagate); G_i = a_i AND b_i (generate)
    // Here we use v[0..3] as "a" bits and v[4..7] as "b" bits.
    // Output: XOR of all 4 generate bits XOR all 4 propagate bits.
    let mut expr = {
        let p0 = terms.bv_binop(Op::BvXor, v[0], v[4]).unwrap();
        let p1 = terms.bv_binop(Op::BvXor, v[1], v[5]).unwrap();
        let p2 = terms.bv_binop(Op::BvXor, v[2], v[6]).unwrap();
        let p3 = terms.bv_binop(Op::BvXor, v[3], v[7]).unwrap();
        let g0 = terms.bv_binop(Op::BvAnd, v[0], v[4]).unwrap();
        let g1 = terms.bv_binop(Op::BvAnd, v[1], v[5]).unwrap();
        let g2 = terms.bv_binop(Op::BvAnd, v[2], v[6]).unwrap();
        let g3 = terms.bv_binop(Op::BvAnd, v[3], v[7]).unwrap();

        let p_all = {
            let t = terms.bv_binop(Op::BvXor, p0, p1).unwrap();
            let t = terms.bv_binop(Op::BvXor, t, p2).unwrap();
            terms.bv_binop(Op::BvXor, t, p3).unwrap()
        };
        let g_all = {
            let t = terms.bv_binop(Op::BvXor, g0, g1).unwrap();
            let t = terms.bv_binop(Op::BvXor, t, g2).unwrap();
            terms.bv_binop(Op::BvXor, t, g3).unwrap()
        };
        terms.bv_binop(Op::BvXor, p_all, g_all).unwrap()
    };

    // Wrap in a non-trivial outer function: NOT(expr) XOR (v[0] AND v[7])
    let not_expr = terms.intern(Op::BvNot, vec![expr], bv1);
    let corner = terms.bv_binop(Op::BvAnd, v[0], v[7]).unwrap();
    expr = terms.bv_binop(Op::BvXor, not_expr, corner).unwrap();

    let simplified = ZhegalkinPolynomial::simplify(expr, &mut terms, &mut sorts).unwrap_or(expr);

    let var_names = ["a", "b", "c", "d", "e", "f", "g", "h"];
    let mut validator = ModelValidator::new();
    let mut count = 0u32;

    // Exhaustive: 2^8 = 256 truth table rows
    for bits in 0u32..256 {
        let mut model = Model::new();
        for (i, &name) in var_names.iter().enumerate() {
            let val = (bits >> i) & 1;
            model.insert(name, smt_core::value::Value::new_bv(val.into(), 1));
        }
        let v_orig = validator
            .evaluate(expr, &model, &terms, &sorts)
            .expect("Original 8-var term must evaluate");
        let v_simp = validator
            .evaluate(simplified, &model, &terms, &sorts)
            .expect("Zhegalkin-simplified 8-var term must evaluate");
        assert_eq!(
            v_orig, v_simp,
            "8-var semantic mismatch at input bits={:#010b}",
            bits
        );
        count += 1;
    }
    assert_eq!(count, 256, "Must have tested all 2^8 = 256 inputs");
    println!("[Zhegalkin 8-var] {} inputs verified OK", count);
}
