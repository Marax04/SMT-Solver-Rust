use smt_core::term::Op;
use smt_solver::crypto::{CryptoAlgorithm, AES_SBOX, SHA256_K};
use smt_solver::engine::Solver;

#[test]
fn test_crypto_fingerprint_aes_sbox() {
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    solver.set_logic("QF_BV");

    // Insert 12 distinct AES S-box constants
    let mut terms_to_assert = Vec::new();
    for &b in &AES_SBOX[..12] {
        let c = solver.terms.bv_const((b as u32).into(), 8, &mut solver.sorts);
        let var = solver.declare_const(&format!("sbox_const_{:02x}", b), bv8);
        let eq = solver.terms.eq(var, c, &solver.sorts);
        terms_to_assert.push(eq);
    }
    let conj = solver.terms.and(terms_to_assert, &solver.sorts);
    solver.assert_formula(conj);

    let matches = solver.scan_crypto();
    let aes_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::AesForwardSbox);
    assert!(aes_match.is_some(), "Should detect AES forward S-box from constants");
    let aes = aes_match.unwrap();
    assert!(aes.confidence > 0.0);
    assert!(aes.matched_terms.len() >= 12);
}

#[test]
fn test_crypto_fingerprint_sha256_constants() {
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    // Insert 8 SHA-256 round constants
    for (i, &k) in SHA256_K.iter().take(8).enumerate() {
        let c = solver.terms.bv_const(k.into(), 32, &mut solver.sorts);
        let var = solver.declare_const(&format!("k_{}", i), bv32);
        let eq = solver.terms.eq(var, c, &solver.sorts);
        solver.assert_formula(eq);
    }

    let matches = solver.scan_crypto();
    let sha_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::Sha256RoundConstants);
    assert!(sha_match.is_some(), "Should detect SHA-256 K constants");
}

#[test]
fn test_crypto_fingerprint_rc4_ksa() {
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    let arr_sort = solver.sorts.array(bv8, bv8);
    let s0 = solver.declare_const("S0", arr_sort);
    solver.set_logic("QF_ABV");

    // Create S[0]=0, S[1]=1, ..., S[9]=9 chain
    let mut curr_arr = s0;
    for i in 0..10u32 {
        let idx = solver.terms.bv_const(i.into(), 8, &mut solver.sorts);
        let val = solver.terms.bv_const(i.into(), 8, &mut solver.sorts);
        curr_arr = solver.terms.intern(Op::Store, vec![curr_arr, idx, val], arr_sort);
    }
    let s_final = solver.declare_const("S_final", arr_sort);
    let eq = solver.terms.eq(s_final, curr_arr, &solver.sorts);
    solver.assert_formula(eq);

    let matches = solver.scan_crypto();
    let rc4_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::Rc4KsaPattern);
    assert!(rc4_match.is_some(), "Should detect RC4 KSA identity store pattern");
}

#[test]
fn test_crypto_structural_arx_round_detection() {
    // Test structural ARX detection WITHOUT any literal MD5/SHA table constants
    let mut solver = Solver::new();
    let bv32 = solver.sorts.bv(32);
    solver.set_logic("QF_BV");

    let a0 = solver.declare_const("a0", bv32);
    let b0 = solver.declare_const("b0", bv32);
    let d0 = solver.declare_const("d0", bv32);

    // Quarter-round step 1: a1 = a0 + b0
    let a1 = solver.terms.bv_binop(Op::BvAdd, a0, b0).unwrap();
    // d1 = (d0 ^ a1) <<< 16
    let d0_xor_a1 = solver.terms.bv_binop(Op::BvXor, d0, a1).unwrap();
    let r16 = solver.terms.intern(Op::BvRotateLeft(16), vec![d0_xor_a1], bv32);

    // Quarter-round step 2: (a1 ^ r16) <<< 12
    let next_xor = solver.terms.bv_binop(Op::BvXor, a1, r16).unwrap();
    let next_add = solver.terms.bv_binop(Op::BvAdd, next_xor, b0).unwrap();
    let r12 = solver.terms.intern(Op::BvRotateLeft(12), vec![next_add], bv32);

    let final_var = solver.declare_const("res", bv32);
    let eq = solver.terms.eq(final_var, r12, &solver.sorts);
    solver.assert_formula(eq);

    let matches = solver.scan_crypto();
    let arx_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::ArxRoundStructure);
    assert!(
        arx_match.is_some(),
        "Should detect structural ARX quarter-round dataflow even without known constants"
    );
}

#[test]
fn test_crypto_structural_aes_xtime_spn_detection() {
    // Test structural AES xtime / Galois Field reduction WITHOUT literal S-box
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    solver.set_logic("QF_BV");

    let byte_in = solver.declare_const("state_byte", bv8);
    let one = solver.terms.bv_const(1u32.into(), 8, &mut solver.sorts);
    let shl_byte = solver.terms.bv_binop(Op::BvShl, byte_in, one).unwrap();

    let poly_1b = solver.terms.bv_const(0x1bu32.into(), 8, &mut solver.sorts);
    let xtime = solver.terms.bv_binop(Op::BvXor, shl_byte, poly_1b).unwrap();

    let byte_out = solver.declare_const("xtime_out", bv8);
    let eq = solver.terms.eq(byte_out, xtime, &solver.sorts);
    solver.assert_formula(eq);

    let matches = solver.scan_crypto();
    let spn_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::AesSpnRoundStructure);
    assert!(
        spn_match.is_some(),
        "Should detect AES Galois Field polynomial reduction xtime even without S-box"
    );
}

#[test]
fn test_crypto_pipeline_normalize_then_scan_mba_hidden_constants() {
    // Validates the normalize-then-scan pipeline ordering in scan_crypto().
    //
    // An MBA-obfuscated assertion hides AES S-Box constants behind a zero-identity:
    //   assert(var == (sbox_val XOR 0) )  -- the XOR-0 masks the literal sbox_val
    //   In raw AST form, the constant 0x63 (first AES S-Box byte) is embedded inside
    //   a BvXor node, not directly as a BvConst.
    //
    // Before the pipeline fix: scan_crypto() would scan the raw arena and miss the
    //   value because it's wrapped in BvXor(const, zero) — only the BvConst nodes
    //   are indexed, and the wrapping expression is not folded away.
    //
    // After the fix: ConstantFolder is applied first, folding (val XOR 0) -> val,
    //   exposing the AES S-Box constants to the pattern matcher.
    use smt_solver::crypto::CryptoAlgorithm;
    let mut solver = Solver::new();
    let bv8 = solver.sorts.bv(8);
    solver.set_logic("QF_BV");

    // Insert 10 AES S-Box bytes, each wrapped in an identity: (sbox_val XOR 0)
    // The XOR-0 is a constant-foldable identity but hides the literal in the raw AST.
    let zero8 = solver.terms.bv_const(0u32.into(), 8, &mut solver.sorts);
    for (i, &b) in AES_SBOX.iter().take(10).enumerate() {
        let sbox_const = solver.terms.bv_const((b as u32).into(), 8, &mut solver.sorts);
        // Wrap: sbox_val XOR 0  (foldable identity, hides the constant)
        let disguised = solver.terms.bv_binop(Op::BvXor, sbox_const, zero8).unwrap();
        let var = solver.declare_const(&format!("hidden_{:02x}_{}", b, i), bv8);
        let eq = solver.terms.eq(var, disguised, &solver.sorts);
        solver.assert_formula(eq);
    }

    // scan_crypto() must now normalize (fold constants) before scanning.
    // After normalization: (sbox_val XOR 0) folds to sbox_val, and the scanner
    // finds the AES S-Box constants.
    let matches = solver.scan_crypto();
    let aes_match = matches
        .iter()
        .find(|m| m.algorithm == CryptoAlgorithm::AesForwardSbox);
    assert!(
        aes_match.is_some(),
        "Pipeline fix (normalize-then-scan): AES S-Box constants wrapped in XOR-0 \
         must be detectable AFTER constant folding. Without the fix, this would return None."
    );
    let aes = aes_match.unwrap();
    assert!(
        aes.confidence > 0.0,
        "Matched AES S-Box detection must have positive confidence score"
    );
}
