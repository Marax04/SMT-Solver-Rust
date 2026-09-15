//! End-to-end integration test against real compiled Tigress ELF64 binary.
//!
//! Loads `fixtures/tigress_linear_mba_opaque.elf`, extracts machine code at `0x401000`,
//! decodes instructions, performs symbolic lifting and SMT refutation of the MBA opaque predicate,
//! proves control-flow invariance, prunes the bogus branch, and verifies deterministic forensic replay.

use smt_solver::binary_loader::{BinaryFormat, BinaryLoader};
use smt_solver::explain::DeobfuscationExplainer;
use smt_solver::lifter::{BranchResolution, DeobfuscationStatus, IrInstruction, Lifter};
use smt_solver::provenance::{BlockProvenanceArtifact, ProvenanceConfidence};
use smt_solver::replay::ReplayEngine;
use smt_solver::x86_decoder::X86Decoder;
use std::fs;
use std::path::PathBuf;

#[test]
fn test_real_tigress_elf64_binary_end_to_end_analysis() {
    let mut manifest_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_path.pop(); // crates/
    manifest_path.pop(); // root
    let fixture_path = manifest_path
        .join("fixtures")
        .join("tigress_linear_mba_opaque.elf");

    let raw_bytes = fs::read(&fixture_path).unwrap_or_else(|e| {
        panic!(
            "Failed to read Tigress binary fixture at {:?}: {}",
            fixture_path, e
        );
    });

    // 1. Cryptographic SHA-256 verification
    let computed_hash = BlockProvenanceArtifact::compute_sha256(&raw_bytes);
    assert_eq!(
        computed_hash, "58aaac042f31cecb6fcd74cc8b54b6a0a88a8747fe3ff6f7e8168afd4ece85d4",
        "Fixture SHA-256 must match recorded specification"
    );

    // 2. Binary Loader Ingestion
    let (format, image) = BinaryLoader::load_process_image(&raw_bytes, None)
        .expect("BinaryLoader must load valid ELF64 fixture");
    assert!(
        matches!(format, BinaryFormat::Elf64(_)),
        "Binary format must be recognized as ELF64"
    );
    assert_eq!(
        image.entry_point, 0x401000,
        "Entry point must be at 0x401000"
    );
    assert_eq!(
        image.segments[0].base_vaddr, 0x400000,
        "Segment base must be at 0x400000"
    );

    // 3. Machine Code Extraction
    let entry_bytes = image
        .extract_code_at(0x401000, 64)
        .expect("Must extract code at entry point");
    assert!(!entry_bytes.is_empty());

    // 4. x86-64 Instruction Decoding
    let bb = X86Decoder::decode_block(&entry_bytes, image.entry_point)
        .expect("X86Decoder must decode entry point basic block");
    assert_eq!(bb.address, 0x401000);
    assert!(!bb.instructions.is_empty());

    // 5. Symbolic Lifting & Path Execution
    let mut lifter = Lifter::new();
    for inst in &bb.instructions {
        lifter.step(inst);
    }

    // 6. Branch Pruning & Certified Resolution
    let terminator = bb
        .instructions
        .last()
        .cloned()
        .unwrap_or(IrInstruction::Nop);
    let cert = lifter.resolve_branch_certified(&terminator, &[]);

    // Ground truth: (x ^ y) + 2*(x & y) == x + y is an identity, so JZ +5 is ALWAYS taken
    assert_eq!(
        cert.resolution,
        BranchResolution::Deterministic(0x401022),
        "Branch resolution must be formally certified as deterministic to 0x401022"
    );
    assert!(
        matches!(
            cert.status,
            DeobfuscationStatus::ProvenInvariant {
                surviving_target: 0x401022,
                dead_target: 0x40101d,
            }
        ),
        "Status must be ProvenInvariant with dead target 0x40101d pruned"
    );

    // 7. Audit Provenance Generation
    let disasm: Vec<String> = bb.instructions.iter().map(|i| format!("{:?}", i)).collect();
    let artifact = BlockProvenanceArtifact::new(
        &raw_bytes,
        bb.address,
        &entry_bytes[..29],
        disasm,
        cert.resolution,
        cert.status,
        ProvenanceConfidence::Proven,
    );

    // 8. Natural-Language Explainability
    let narrative = DeobfuscationExplainer::explain(&artifact);
    assert!(
        narrative.contains("Formally Certified"),
        "Explanation must highlight formal certification"
    );
    assert!(
        narrative.contains("Control Flow Invariance"),
        "Explanation must describe opaque predicate invariant"
    );

    // 9. Deterministic Replay Verification
    let replay_result =
        ReplayEngine::replay(&artifact).expect("ReplayEngine must execute successfully");
    assert!(
        replay_result.is_reproducible,
        "Analysis must be 100% reproducible"
    );
    assert!(
        replay_result.binary_hash_matched,
        "Binary SHA-256 hash must match"
    );
    assert!(replay_result.resolution_matched, "Resolution must match");
    assert!(replay_result.status_matched, "Status must match");
}
