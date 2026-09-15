//! Tests for the deobfuscation audit trail and provenance artifact generation.

use smt_solver::lifter::{BranchResolution, DeobfuscationStatus};
use smt_solver::provenance::BlockProvenanceArtifact;
use smt_solver::synthesis::EquivalenceMetadata;

#[test]
fn test_provenance_artifact_markdown_and_json_generation() {
    let raw_bytes = vec![0x31, 0xc0, 0x85, 0xc0, 0x74, 0x05];
    let hash = BlockProvenanceArtifact::compute_sha256(&raw_bytes);
    assert_eq!(hash.len(), 64);

    let artifact = BlockProvenanceArtifact {
        binary_sha256: hash.clone(),
        block_vaddr: 0x401000,
        raw_bytes: raw_bytes.clone(),
        disassembly: vec![
            "xor eax, eax".to_string(),
            "test eax, eax".to_string(),
            "jz +5".to_string(),
        ],
        path_conditions: vec!["true".to_string()],
        original_condition_term: "(= (bvand eax eax) 0)".to_string(),
        simplified_condition_term: "true".to_string(),
        resolution: BranchResolution::Deterministic(0x40100b),
        deobfuscation_status: DeobfuscationStatus::ProvenInvariant {
            surviving_target: 0x40100b,
            dead_target: 0x401006,
        },
        metadata: EquivalenceMetadata {
            solving_time_ms: 2,
            logic: "QF_BV".to_string(),
            budget_exhausted: false,
            model_validated: true,
            oracle_agreed: Some(true),
            proof_available: true,
        },
        counterexample_model: None,
        applied_rewrites: vec![
            "xor-self-to-zero".to_string(),
            "and-zero-identity".to_string(),
        ],
    };

    // 1. Verify Markdown report
    let md = artifact.to_markdown();
    assert!(md.contains("# Deobfuscation Audit Artifact — Block 0x401000"));
    assert!(md.contains(&format!("- **Binary SHA-256**: `{}`", hash)));
    assert!(md.contains("## Disassembly"));
    assert!(md.contains("xor eax, eax"));
    assert!(md.contains("## Branch Resolution & Deobfuscation Status"));
    assert!(md.contains("Deterministic(4198411)"));
    assert!(md.contains("## Applied Rewrites"));
    assert!(md.contains("xor-self-to-zero"));

    // 2. Verify JSON report
    let json = artifact.to_json();
    assert!(json.contains(&format!("\"binary_sha256\": \"{}\"", hash)));
    assert!(json.contains("\"block_vaddr\": \"0x401000\""));
    assert!(json.contains("\"logic\": \"QF_BV\""));
    assert!(json.contains("\"solving_time_ms\": 2"));
    assert!(json.contains("\"applied_rewrites\": [\"xor-self-to-zero\", \"and-zero-identity\"]"));
}
