//! Real-world Opaque Predicate benchmarks from obfuscation literature (OLLVM, Tigress, Crackmes).
//!
//! Validates contextual classification and symbolic path condition trace folding against
//! standard obfuscation patterns used in real-world binaries.

use smt_core::term::Op;
use smt_solver::engine::Solver;
use smt_solver::opaque::{OpaqueClassification, TraceBranch};

#[test]
fn test_real_world_ollvm_consecutive_product_even() {
    // OLLVM Bogus Control Flow invariant:
    // For any integer x: x * (x + 1) is always even, i.e., (x * (x + 1)) & 1 == 0.
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    let one = solver.terms.bv_const(1u32.into(), 32, &mut solver.sorts);
    let x_plus_1 = solver.terms.bv_binop(Op::BvAdd, x, one).unwrap();
    let prod = solver.terms.bv_binop(Op::BvMul, x, x_plus_1).unwrap();
    let bit0 = solver.terms.bv_binop(Op::BvAnd, prod, one).unwrap();
    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);
    let is_even = solver.terms.eq(bit0, zero, &solver.sorts);

    let classification = solver.check_opaque(is_even);
    assert_eq!(
        classification,
        OpaqueClassification::AlwaysTrue,
        "x*(x+1) & 1 == 0 is an unconditional invariant in OLLVM bogus control flow"
    );
}

#[test]
fn test_real_world_tigress_collatz_bit_invariant() {
    // Tigress Obfuscator invariant:
    // For any x, let odd = (x | 1).
    // odd * 3 + 1 is always even -> ((x | 1) * 3 + 1) & 1 == 0.
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    let x = solver.declare_const("x", bv32);
    solver.set_logic("QF_BV");

    let one = solver.terms.bv_const(1u32.into(), 32, &mut solver.sorts);
    let three = solver.terms.bv_const(3u32.into(), 32, &mut solver.sorts);
    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);

    let odd_x = solver.terms.bv_binop(Op::BvOr, x, one).unwrap();
    let three_x = solver.terms.bv_binop(Op::BvMul, odd_x, three).unwrap();
    let collatz_step = solver.terms.bv_binop(Op::BvAdd, three_x, one).unwrap();
    let lsb = solver.terms.bv_binop(Op::BvAnd, collatz_step, one).unwrap();
    let is_even = solver.terms.eq(lsb, zero, &solver.sorts);

    let classification = solver.check_opaque(is_even);
    assert_eq!(
        classification,
        OpaqueClassification::AlwaysTrue,
        "((x | 1)*3 + 1) & 1 == 0 must be recognized as invariant AlwaysTrue"
    );
}

#[test]
fn test_real_world_crackme_contextual_key_trace_pruning() {
    // Real crackme trace pattern:
    // In block 0: key_len must be 16: assert(len == 16)
    // In block 1: key[0] is validated via hash/XOR: assert(key[0] ^ 0x5a == 0x12) -> key[0] == 0x48
    // In block 2: Obfuscator inserts opaque dispatch:
    //   Branch 1: if (key[0] == 0x48) -> jump to real decrypt loop
    //   Branch 2: if (key[0] == 0x00) -> jump to fake crash/bomb routine
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    let key0 = solver.declare_const("key0", bv8);
    let len = solver.declare_const("len", bv32);

    let len16 = solver.terms.bv_const(16u32.into(), 32, &mut solver.sorts);
    let pc_len = solver.terms.eq(len, len16, &solver.sorts);

    let mask = solver.terms.bv_const(0x5au32.into(), 8, &mut solver.sorts);
    let xor_term = solver.terms.bv_binop(Op::BvXor, key0, mask).unwrap();
    let target = solver.terms.bv_const(0x12u32.into(), 8, &mut solver.sorts);
    let pc_key = solver.terms.eq(xor_term, target, &solver.sorts);

    let h_byte = solver.terms.bv_const(0x48u32.into(), 8, &mut solver.sorts);
    let p_real = solver.terms.eq(key0, h_byte, &solver.sorts);

    let zero_byte = solver.terms.bv_const(0x00u32.into(), 8, &mut solver.sorts);
    let p_bomb = solver.terms.eq(key0, zero_byte, &solver.sorts);

    let pc = vec![pc_len, pc_key];

    let class_real = solver.check_opaque_contextual(&pc, p_real);
    assert_eq!(
        class_real,
        OpaqueClassification::AlwaysTrue,
        "key0 == 0x48 is contextually AlwaysTrue under PC"
    );

    let class_bomb = solver.check_opaque_contextual(&pc, p_bomb);
    assert_eq!(
        class_bomb,
        OpaqueClassification::AlwaysFalse,
        "key0 == 0x00 is contextually AlwaysFalse under PC"
    );

    let trace = vec![
        TraceBranch {
            block_id: 10,
            predicate: pc_key,
            taken: true,
        },
        TraceBranch {
            block_id: 20,
            predicate: p_bomb,
            taken: false,
        },
        TraceBranch {
            block_id: 30,
            predicate: p_real,
            taken: true,
        },
    ];

    let folded = solver.fold_trace(&trace);
    assert_eq!(folded.reachable_blocks, vec![10, 20, 30]);
    assert_eq!(folded.eliminated_dead_edges, vec![(20, true), (30, false)]);
    assert_eq!(
        folded.classifications,
        vec![
            (10, OpaqueClassification::Dynamic),
            (20, OpaqueClassification::AlwaysFalse),
            (30, OpaqueClassification::AlwaysTrue),
        ]
    );
}

// =============================================================================
// TIGRESS REALISTIC CORPUS
// Patterns derived from published Tigress C Diversifier/Obfuscator output
// (Collberg et al., https://tigress.cs.arizona.edu/). Unlike hand-crafted clean
// formulas, these tests embed auxiliary state variables, redundant operations,
// and intermediate XOR/hash chains that match real obfuscator output structure.
// =============================================================================

#[test]
fn test_tigress_bogus_dispatch_with_auxiliary_counter() {
    // Tigress `addOpaquePredicates` pattern: bogus conditional dispatch
    // embedded inside a loop that uses an auxiliary counter.
    //
    // Invariant: (loop_iter & 0xFF) * ((loop_iter & 0xFF) + 1) & 1 == 0
    //
    // Tigress wraps with: OR-0 to loop_iter (cosmetic), AND-mask for byte truncation.
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    let loop_iter = solver.declare_const("loop_iter", bv32);
    let _aux_cnt = solver.declare_const("aux_cnt", bv32);

    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);
    let one = solver.terms.bv_const(1u32.into(), 32, &mut solver.sorts);
    let mask_ff = solver.terms.bv_const(0xFFu32.into(), 32, &mut solver.sorts);

    let iter_masked = solver.terms.bv_binop(Op::BvOr, loop_iter, zero).unwrap();
    let iter_byte = solver
        .terms
        .bv_binop(Op::BvAnd, iter_masked, mask_ff)
        .unwrap();
    let iter_p1 = solver.terms.bv_binop(Op::BvAdd, iter_byte, one).unwrap();
    let product = solver
        .terms
        .bv_binop(Op::BvMul, iter_byte, iter_p1)
        .unwrap();
    let lsb = solver.terms.bv_binop(Op::BvAnd, product, one).unwrap();
    let dispatch_cond = solver.terms.eq(lsb, zero, &solver.sorts);

    let classification = solver.check_opaque(dispatch_cond);
    assert_eq!(
        classification,
        OpaqueClassification::AlwaysTrue,
        "Tigress bogus dispatch with auxiliary counter must be AlwaysTrue"
    );
}

#[test]
fn test_tigress_hash_then_compare_opaque_with_xor_chain() {
    // Tigress `hashFunction` opaque predicate pattern.
    // secret is constrained to 0xDEAD by prior block; hash_out is pre-computable.
    // hash_out = ((0xDEAD ^ 0xBEEF) + 0x1234) & 0xFFFF = 0x7276
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    let secret = solver.declare_const("secret", bv32);
    let v_dead = solver
        .terms
        .bv_const(0xDEADu32.into(), 32, &mut solver.sorts);
    let v_beef = solver
        .terms
        .bv_const(0xBEEFu32.into(), 32, &mut solver.sorts);
    let v_1234 = solver
        .terms
        .bv_const(0x1234u32.into(), 32, &mut solver.sorts);
    let v_ffff = solver
        .terms
        .bv_const(0xFFFFu32.into(), 32, &mut solver.sorts);
    let v_7276 = solver
        .terms
        .bv_const(0x7276u32.into(), 32, &mut solver.sorts);
    let v_zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);

    let pc_secret = solver.terms.eq(secret, v_dead, &solver.sorts);

    let xored = solver.terms.bv_binop(Op::BvXor, secret, v_beef).unwrap();
    let added = solver.terms.bv_binop(Op::BvAdd, xored, v_1234).unwrap();
    let hash_out = solver.terms.bv_binop(Op::BvAnd, added, v_ffff).unwrap();

    let p_true = solver.terms.eq(hash_out, v_7276, &solver.sorts);
    let p_false = solver.terms.eq(hash_out, v_zero, &solver.sorts);

    let pc = vec![pc_secret];

    let class_true = solver.check_opaque_contextual(&pc, p_true);
    assert_eq!(
        class_true,
        OpaqueClassification::AlwaysTrue,
        "Tigress hash-then-compare: hash(0xDEAD)==0x7276 must be AlwaysTrue"
    );

    let class_false = solver.check_opaque_contextual(&pc, p_false);
    assert_eq!(
        class_false,
        OpaqueClassification::AlwaysFalse,
        "Tigress hash-then-compare: hash(0xDEAD)==0 must be AlwaysFalse"
    );
}

#[test]
fn test_tigress_nested_mba_invariant_with_side_effect_intermediates() {
    // Tigress `addOpaquePredicates` with MBA-obfuscated invariants.
    // Pattern from: Eyrolles et al., "Defeating MBA-based Obfuscation", SPRO 2016.
    //
    // Invariant: ((x + (x ^ x)) - x) == 0  i.e.  0 == 0
    // Side-effect vars tmp1, tmp2 are declared and constrained but do NOT affect x.
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    let x = solver.declare_const("x", bv32);
    let tmp1_var = solver.declare_const("tmp1", bv32);
    let tmp2_var = solver.declare_const("tmp2", bv32);

    let mask_a = solver
        .terms
        .bv_const(0xAAAAAAAAu32.into(), 32, &mut solver.sorts);
    let mask_5 = solver
        .terms
        .bv_const(0x55555555u32.into(), 32, &mut solver.sorts);
    let zero = solver.terms.bv_const(0u32.into(), 32, &mut solver.sorts);

    let tmp1_actual = solver.terms.bv_binop(Op::BvAnd, x, mask_a).unwrap();
    let pc_tmp1 = solver.terms.eq(tmp1_var, tmp1_actual, &solver.sorts);

    let tmp2_actual = solver.terms.bv_binop(Op::BvOr, x, mask_5).unwrap();
    let pc_tmp2 = solver.terms.eq(tmp2_var, tmp2_actual, &solver.sorts);

    let x_xor_x = solver.terms.bv_binop(Op::BvXor, x, x).unwrap();
    let x_plus_0 = solver.terms.bv_binop(Op::BvAdd, x, x_xor_x).unwrap();
    let result = solver.terms.bv_binop(Op::BvSub, x_plus_0, x).unwrap();
    let dispatch_cond = solver.terms.eq(result, zero, &solver.sorts);

    let pc = vec![pc_tmp1, pc_tmp2];

    let classification = solver.check_opaque_contextual(&pc, dispatch_cond);
    assert_eq!(
        classification,
        OpaqueClassification::AlwaysTrue,
        "Tigress MBA invariant with side-effect intermediates must be contextually AlwaysTrue"
    );
}
