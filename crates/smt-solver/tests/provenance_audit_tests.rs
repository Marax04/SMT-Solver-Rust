//! Tests for the deobfuscation audit trail and provenance artifact generation.

use smt_solver::lifter::{BranchResolution, DeobfuscationStatus};
use smt_solver::provenance::{BlockProvenanceArtifact, ProvenanceConfidence};
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
        confidence: ProvenanceConfidence::Proven,
        solver_version: "0.1.0".to_string(),
        git_commit: "35b5d74".to_string(),
        backend: "smt-solver-cdcl-qf-bv".to_string(),
        random_seed: 42,
        timeout_ms: 10000,
        memory_budget_mb: 512,
        conflicts_count: 0,
        propagations_count: 14,
        formula_sha256: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            .to_string(),
        pre_simplification_ir_sha256:
            "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08".to_string(),
        post_simplification_ir_sha256:
            "5e884898da28047151d0e56f8dc6292773603d0d6aabbdd62a11ef721d1542d8".to_string(),
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
        double_check: None,
    };

    // 1. Verify Markdown report
    let md = artifact.to_markdown();
    assert!(md.contains("# Deobfuscation Audit Artifact — Block 0x401000"));
    assert!(md.contains(&format!("- **Binary SHA-256**: `{}`", hash)));
    assert!(md.contains("- **Confidence**: `Proven`"));
    assert!(md.contains("- **Solver Version**: `0.1.0`"));
    assert!(md.contains("- **Git Commit**: `35b5d74`"));
    assert!(md.contains("## Disassembly"));
    assert!(md.contains("xor eax, eax"));
    assert!(md.contains("## Branch Resolution & Deobfuscation Status"));
    assert!(md.contains("Deterministic(4198411)"));
    assert!(md.contains("## Applied Rewrites"));
    assert!(md.contains("xor-self-to-zero"));

    // 2. Verify JSON report
    let json = artifact.to_json();
    assert!(json.contains(&format!(r#""binary_sha256": "{}""#, hash)));
    assert!(json.contains(r#""block_vaddr": "0x401000""#));
    assert!(json.contains(r#""confidence": "Proven""#));
    assert!(json.contains(r#""git_commit": "35b5d74""#));
    assert!(json.contains(r#""logic": "QF_BV""#));
    assert!(json.contains(r#""conflicts_count": 0"#));

    // 3. Verify DeobfuscationExplainer
    let explanation = smt_solver::explain::DeobfuscationExplainer::explain(&artifact);
    assert!(explanation.contains("Deobfuscation Narrative: Block at 0x401000"));
    assert!(explanation.contains("Formally Certified"));
    assert!(explanation.contains("Control Flow Invariance"));

    // 4. Verify ReplayEngine
    let replay_result =
        smt_solver::replay::ReplayEngine::replay(&artifact).expect("Replay must run");
    assert!(replay_result.is_reproducible);
    assert_eq!(replay_result.decoded_instruction_count, 3);
    assert!(replay_result.resolution_matched);
}
