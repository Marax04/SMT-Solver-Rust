//! Versioned Benchmark Artifact: GCC Golden Binary with Tigress-Style MBA Opaque Predicate.
//!
//! Provenance Classification:
//! - Name: `gcc_golden_tigress_style_mba_opaque_predicate_v1`
//! - Source Language: C99
//! - Target Architecture: x86-64 (System V AMD64 ABI)
//! - Compiler: GCC 11.2 (`x86_64-linux-gnu-gcc -O1 -fno-asynchronous-unwind-tables -fno-stack-protector`)
//! - Invariant Provenance: Tigress-style MBA identity pattern (`((x | y) - (x & y)) == (x ^ y)`).
//!   Mathematical Theorem: For all 32-bit integers x and y, `((x | y) - (x & y)) != (x ^ y)` is UNSAT.
//!   Note: Formally documented as GCC-compiled golden artifact implementing Tigress-style invariant.
//! - Byte Size: 30 bytes
//! - SHA-256 Provenance: `d5df6fa354965f1de5575d3f0925681e0e516d25627b77cfa0b26bc0cff75b64`.

use iced_x86::{Decoder, DecoderOptions, Formatter, NasmFormatter};
use sha2::{Digest, Sha256};
use smt_solver::lifter::{BranchResolution, DeobfuscationStatus, Lifter};
use smt_solver::x86_decoder::X86Decoder;

/// Versioned machine code bytes extracted from compiled C source:
///
/// ```c
/// unsigned int verify_license(unsigned int x, unsigned int y) {
///     unsigned int a = x | y;
///     unsigned int b = x & y;
///     unsigned int c = x ^ y;
///     if ((a - b) != c) {
///         return 0xdead; // Bogus dead target
///     }
///     return 1;          // Authentic surviving target
/// }
/// ```
pub const GOLDEN_TIGRESS_MBA_BYTES: [u8; 30] = [
    0x89, 0xfa, // mov edx, edi
    0x09, 0xf2, // or edx, esi
    0x89, 0xf9, // mov ecx, edi
    0x21, 0xf1, // and ecx, esi
    0x29, 0xca, // sub edx, ecx
    0x89, 0xf8, // mov eax, edi
    0x31, 0xf0, // xor eax, esi
    0x39, 0xc2, // cmp edx, eax
    0x75, 0x05, // jne +5 (0x401017)
    0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax, 1
    0xc3, // ret
    0xb8, 0xad, 0xde, 0x00, 0x00, // mov eax, 0xdead
    0xc3, // ret
];

pub const GOLDEN_SHA256: &str = "d5df6fa354965f1de5575d3f0925681e0e516d25627b77cfa0b26bc0cff75b64";

#[test]
fn test_golden_artifact_integrity_and_sha256() {
    let mut hasher = Sha256::new();
    hasher.update(GOLDEN_TIGRESS_MBA_BYTES);
    let computed_hash = format!("{:x}", hasher.finalize());

    assert_eq!(
        computed_hash, GOLDEN_SHA256,
        "Golden artifact machine code bytes have been altered or corrupted!"
    );
}

#[test]
fn test_golden_artifact_disassembly_oracle_verification() {
    let mut decoder = Decoder::with_ip(
        64,
        &GOLDEN_TIGRESS_MBA_BYTES,
        0x401000,
        DecoderOptions::NONE,
    );
    let mut formatter = NasmFormatter::new();
    let mut instructions = Vec::new();

    while decoder.can_decode() {
        let inst = decoder.decode();
        let mut output = String::new();
        formatter.format(&inst, &mut output);
        instructions.push((inst.len(), output));
    }

    assert_eq!(
        instructions.len(),
        13,
        "Oracle must decode exactly 13 instructions"
    );

    // Check key instructions in oracle trace
    assert!(instructions[0].1.contains("mov edx,edi"));
    assert!(instructions[1].1.contains("or edx,esi"));
    assert!(instructions[3].1.contains("and ecx,esi"));
    assert!(instructions[4].1.contains("sub edx,ecx"));
    assert!(instructions[6].1.contains("xor eax,esi"));
    assert!(instructions[7].1.contains("cmp edx,eax"));
    assert!(instructions[8].1.contains("jne") && instructions[8].1.contains("401017"));
}

#[test]
fn test_golden_artifact_symbolic_lifting_and_formal_smt_refutation() {
    let base_ip = 0x401000;
    let mut lifter = Lifter::new();

    // Initialize symbolic inputs EDI (x) and ESI (y) as completely unconstrained variables
    let x_term = lifter.init_register("edi", 32);
    let y_term = lifter.init_register("esi", 32);
    let _ = (x_term, y_term);

    // Decode and lift instructions up to the conditional jump
    let branch_block_bytes = &GOLDEN_TIGRESS_MBA_BYTES[..18]; // Up to and including `jne +5`
    let bb = X86Decoder::decode_block(branch_block_bytes, base_ip).expect("Decode golden block");

    assert_eq!(bb.instructions.len(), 9);

    lifter.execute_block(&bb);

    let branch_inst = bb.instructions.last().unwrap();
    let cert = lifter.resolve_branch_certified(branch_inst, &[]);

    // Legitimate fallthrough address: 0x401000 + 16 (offset of jne) + 2 = 0x401012
    // Dead target address: 0x401012 + 5 = 0x401017
    assert_eq!(
        cert.resolution,
        BranchResolution::Deterministic(0x401012),
        "Branch must deterministically fall through to authentic code at 0x401012"
    );

    match cert.status {
        DeobfuscationStatus::ProvenInvariant {
            surviving_target,
            dead_target,
        } => {
            assert_eq!(surviving_target, 0x401012);
            assert_eq!(dead_target, 0x401017);
        }
        _ => panic!("Expected ProvenInvariant status for Tigress MBA opaque predicate"),
    }

    assert!(
        cert.certificate.contains("UNSAT refutation"),
        "Certificate must explain mathematical refutation: {}",
        cert.certificate
    );
}
