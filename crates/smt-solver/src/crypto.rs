//! Cryptographic Fingerprinting Module for SMT ASTs (FindCrypt style).
//!
//! Identifies standard cryptographic constants, permutation tables, and algorithm
//! structures (AES S-Box/InvSbox, SHA-256 K/H0 constants, MD5 constants, RC4 KSA)
//! in extracted SMT formulas and symbolic traces.

use num_traits::ToPrimitive;
use smt_core::term::{Op, TermArena, TermId};
use std::collections::{HashMap, HashSet};

/// Identified cryptographic algorithm or primitive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CryptoAlgorithm {
    AesForwardSbox,
    AesInverseSbox,
    Sha256RoundConstants,
    Sha256InitialHash,
    Md5InitialHash,
    Md5StepConstants,
    Rc4KsaPattern,
    ArxRoundStructure,
    AesSpnRoundStructure,
}

impl CryptoAlgorithm {
    pub fn name(&self) -> &'static str {
        match self {
            Self::AesForwardSbox => "AES S-Box (Forward)",
            Self::AesInverseSbox => "AES Inverse S-Box",
            Self::Sha256RoundConstants => "SHA-256 Round Constants (K)",
            Self::Sha256InitialHash => "SHA-256 Initial State (H0)",
            Self::Md5InitialHash => "MD5 Initial State (IV)",
            Self::Md5StepConstants => "MD5 Step Constants (T)",
            Self::Rc4KsaPattern => "RC4 Key Scheduling Pattern",
            Self::ArxRoundStructure => "ARX (Add-Rotate-Xor) Dataflow Pattern",
            Self::AesSpnRoundStructure => "AES SPN (ShiftRows/MixColumns/xtime) Pattern",
        }
    }
}

/// A matched cryptographic primitive with confidence and AST evidence.
#[derive(Debug, Clone, PartialEq)]
pub struct CryptoMatch {
    pub algorithm: CryptoAlgorithm,
    pub description: String,
    /// Confidence score from 0.0 to 1.0.
    pub confidence: f32,
    /// AST terms that contributed to this detection.
    pub matched_terms: Vec<TermId>,
}

// AES S-Box constants (256 bytes)
pub const AES_SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

// AES Inverse S-Box constants (256 bytes)
pub const AES_INVSBOX: [u8; 256] = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
];

// SHA-256 round constants K (64 words)
pub const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

// SHA-256 initial hash values H0 (8 words)
pub const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

// MD5 initial hash values (4 words)
pub const MD5_INIT: [u32; 4] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476];

// MD5 per-step constants T (64 words)
pub const MD5_T: [u32; 64] = [
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
];

/// Crypto fingerprint scanner for AST terms.
#[derive(Debug, Default)]
pub struct CryptoScanner;

impl CryptoScanner {
    pub fn new() -> Self {
        Self
    }

    /// Scans an AST arena for known cryptographic constants, tables, and patterns.
    pub fn scan(terms: &TermArena) -> Vec<CryptoMatch> {
        let mut matches = Vec::new();

        // 1. Collect all bitvector constants mapped to their TermIds
        let mut byte_consts: HashMap<u8, Vec<TermId>> = HashMap::new();
        let mut u32_consts: HashMap<u32, Vec<TermId>> = HashMap::new();

        let term_count = terms.len();
        for i in 0..term_count {
            let id = TermId(i as u32);
            let term = terms.get(id);
            if let Op::BvConst { ref value, width } = term.op {
                if width == 8 {
                    if let Some(b) = value.to_u8() {
                        byte_consts.entry(b).or_default().push(id);
                    }
                } else if width == 32 {
                    if let Some(w) = value.to_u32() {
                        u32_consts.entry(w).or_default().push(id);
                    }
                }
            }
        }

        // 2. Check for AES Forward S-Box
        Self::check_byte_table(
            &AES_SBOX,
            &byte_consts,
            CryptoAlgorithm::AesForwardSbox,
            8,
            &mut matches,
        );

        // 3. Check for AES Inverse S-Box
        Self::check_byte_table(
            &AES_INVSBOX,
            &byte_consts,
            CryptoAlgorithm::AesInverseSbox,
            8,
            &mut matches,
        );

        // 4. Check for SHA-256 Round Constants (K)
        Self::check_u32_table(
            &SHA256_K,
            &u32_consts,
            CryptoAlgorithm::Sha256RoundConstants,
            4,
            &mut matches,
        );

        // 5. Check for SHA-256 Initial Hash (H0)
        Self::check_u32_table(
            &SHA256_H0,
            &u32_consts,
            CryptoAlgorithm::Sha256InitialHash,
            4,
            &mut matches,
        );

        // 6. Check for MD5 Initial Hash
        Self::check_u32_table(
            &MD5_INIT,
            &u32_consts,
            CryptoAlgorithm::Md5InitialHash,
            3,
            &mut matches,
        );

        // 7. Check for MD5 Step Constants (T)
        Self::check_u32_table(
            &MD5_T,
            &u32_consts,
            CryptoAlgorithm::Md5StepConstants,
            4,
            &mut matches,
        );

        // 8. Check for RC4 KSA pattern: look for array store chains or modulo 256 indexing
        Self::check_rc4_pattern(terms, &mut matches);

        // 9. Check for structural ARX (Addition-Rotation-XOR) round chains
        Self::check_arx_structure(terms, &mut matches);

        // 10. Check for structural AES SPN / xtime polynomial reduction pattern
        Self::check_aes_spn_structure(terms, &mut matches);

        matches
    }

    fn check_byte_table(
        table: &[u8],
        const_map: &HashMap<u8, Vec<TermId>>,
        algo: CryptoAlgorithm,
        min_threshold: usize,
        matches: &mut Vec<CryptoMatch>,
    ) {
        let mut found_terms = Vec::new();
        let mut hit_count = 0;
        let mut seen = HashSet::new();

        for &val in table {
            if let Some(tids) = const_map.get(&val) {
                for &tid in tids {
                    if seen.insert(tid) {
                        found_terms.push(tid);
                    }
                }
                hit_count += 1;
            }
        }

        if hit_count >= min_threshold {
            let confidence = (hit_count as f32) / (table.len() as f32);
            let score = (confidence * 2.0).min(1.0);
            matches.push(CryptoMatch {
                algorithm: algo,
                description: format!(
                    "Found {}/{} unique constants matching {}",
                    hit_count,
                    table.len(),
                    algo.name()
                ),
                confidence: score,
                matched_terms: found_terms,
            });
        }
    }

    fn check_u32_table(
        table: &[u32],
        const_map: &HashMap<u32, Vec<TermId>>,
        algo: CryptoAlgorithm,
        min_threshold: usize,
        matches: &mut Vec<CryptoMatch>,
    ) {
        let mut found_terms = Vec::new();
        let mut hit_count = 0;
        let mut seen = HashSet::new();

        for &val in table {
            if let Some(tids) = const_map.get(&val) {
                for &tid in tids {
                    if seen.insert(tid) {
                        found_terms.push(tid);
                    }
                }
                hit_count += 1;
            }
        }

        if hit_count >= min_threshold {
            let confidence = (hit_count as f32) / (table.len() as f32);
            let score = (confidence * 2.0).min(1.0);
            matches.push(CryptoMatch {
                algorithm: algo,
                description: format!(
                    "Found {}/{} unique constants matching {}",
                    hit_count,
                    table.len(),
                    algo.name()
                ),
                confidence: score,
                matched_terms: found_terms,
            });
        }
    }

    fn check_rc4_pattern(terms: &TermArena, matches: &mut Vec<CryptoMatch>) {
        let mut identity_stores = 0;
        let mut matched_terms = Vec::new();

        let term_count = terms.len();
        for i in 0..term_count {
            let id = TermId(i as u32);
            let term = terms.get(id);
            if matches!(term.op, Op::Store) && term.args.len() == 3 {
                let idx_term = terms.get(term.args[1]);
                let val_term = terms.get(term.args[2]);
                if let (
                    Op::BvConst {
                        value: ref v_idx, ..
                    },
                    Op::BvConst {
                        value: ref v_val, ..
                    },
                ) = (&idx_term.op, &val_term.op)
                {
                    if v_idx == v_val {
                        identity_stores += 1;
                        matched_terms.push(id);
                    }
                }
            }
        }

        if identity_stores >= 8 {
            matches.push(CryptoMatch {
                algorithm: CryptoAlgorithm::Rc4KsaPattern,
                description: format!(
                    "Found {} identity array store initializations S[i] = i characteristic of RC4 KSA",
                    identity_stores
                ),
                confidence: (identity_stores as f32 / 32.0).min(1.0),
                matched_terms,
            });
        }
    }

    fn check_arx_structure(terms: &TermArena, matches: &mut Vec<CryptoMatch>) {
        let mut arx_nodes = Vec::new();
        let term_count = terms.len();

        for i in 0..term_count {
            let id = TermId(i as u32);
            let term = terms.get(id);

            // Rotation is either Op::BvRotateLeft/Right, or (x << r) | (x >> (w - r))
            let inner_arg = match term.op {
                Op::BvRotateLeft(_) | Op::BvRotateRight(_) if !term.args.is_empty() => {
                    Some(term.args[0])
                }
                Op::BvOr if term.args.len() == 2 => {
                    let left = terms.get(term.args[0]);
                    let right = terms.get(term.args[1]);
                    if matches!(
                        (&left.op, &right.op),
                        (Op::BvShl, Op::BvLshr) | (Op::BvLshr, Op::BvShl)
                    ) {
                        if !left.args.is_empty()
                            && !right.args.is_empty()
                            && left.args[0] == right.args[0]
                        {
                            Some(left.args[0])
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            };

            if let Some(cand_id) = inner_arg {
                let cand_term = terms.get(cand_id);
                // Check if inner is an XOR or ADD operation
                if matches!(cand_term.op, Op::BvXor | Op::BvAdd) {
                    // Check if one of its children is the other (Add under Xor, or Xor under Add)
                    let has_arx_chain = cand_term.args.iter().any(|&child_id| {
                        let child = terms.get(child_id);
                        matches!(child.op, Op::BvAdd | Op::BvXor) && child.op != cand_term.op
                    });
                    if has_arx_chain {
                        arx_nodes.push(id);
                    }
                }
            }
        }

        if arx_nodes.len() >= 2 {
            let confidence = (arx_nodes.len() as f32 / 8.0).min(1.0);
            matches.push(CryptoMatch {
                algorithm: CryptoAlgorithm::ArxRoundStructure,
                description: format!(
                    "Found {} ARX (Add-Rotate-Xor) operations characteristic of ChaCha20/SHA/MD5 rounds",
                    arx_nodes.len()
                ),
                confidence,
                matched_terms: arx_nodes,
            });
        }
    }

    fn check_aes_spn_structure(terms: &TermArena, matches: &mut Vec<CryptoMatch>) {
        let mut spn_nodes = Vec::new();
        let term_count = terms.len();

        for i in 0..term_count {
            let id = TermId(i as u32);
            let term = terms.get(id);

            // Check for xtime GF(2^8) reduction: (x << 1) ^ (0x1b & mask)
            if matches!(term.op, Op::BvXor) && term.args.len() == 2 {
                let a = terms.get(term.args[0]);
                let b = terms.get(term.args[1]);
                let has_shl = matches!(a.op, Op::BvShl) || matches!(b.op, Op::BvShl);
                let has_poly_1b = [a, b].iter().any(|t| {
                    if let Op::BvConst { ref value, width } = t.op {
                        width == 8 && value.to_u32() == Some(0x1b)
                    } else if matches!(t.op, Op::BvAnd) {
                        t.args.iter().any(|&aid| {
                            if let Op::BvConst { ref value, width } = terms.get(aid).op {
                                width == 8 && value.to_u32() == Some(0x1b)
                            } else {
                                false
                            }
                        })
                    } else {
                        false
                    }
                });

                if has_shl && has_poly_1b {
                    spn_nodes.push(id);
                }
            }
        }

        if !spn_nodes.is_empty() {
            matches.push(CryptoMatch {
                algorithm: CryptoAlgorithm::AesSpnRoundStructure,
                description: format!(
                    "Found {} AES Galois Field reduction (xtime / 0x1b) operations characteristic of AES MixColumns",
                    spn_nodes.len()
                ),
                confidence: 0.95,
                matched_terms: spn_nodes,
            });
        }
    }
}
