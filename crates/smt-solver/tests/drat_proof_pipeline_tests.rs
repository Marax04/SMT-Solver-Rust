//! End-to-end integration test validating DRAT proof certificates via algorithmic RUP checking.

use smt_sat::{DratChecker, DratVerificationResult, SatSolver, Var};
use smt_solver::provenance::{BlockProvenanceArtifact, ProofCertificateCheckResult};

#[test]
fn test_solver_drat_proof_generation_and_rup_verification() {
    let mut sat = SatSolver::new();
    sat.enable_drat(true);

    let v1 = Var(0);
    let v2 = Var(1);

    // Unsatisfiable clause set:
    // (v1 | v2), (!v1 | v2), (v1 | !v2), (!v1 | !v2)
    let c1 = vec![v1.to_lit(), v2.to_lit()];
    let c2 = vec![!v1.to_lit(), v2.to_lit()];
    let c3 = vec![v1.to_lit(), !v2.to_lit()];
    let c4 = vec![!v1.to_lit(), !v2.to_lit()];

    sat.add_clause(c1.clone());
    sat.add_clause(c2.clone());
    sat.add_clause(c3.clone());
    sat.add_clause(c4.clone());

    let result = sat.solve();
    assert_eq!(result, smt_sat::LBool::False, "Formula must be UNSAT");

    let proof_str = sat.proof.to_string();
    assert!(
        !proof_str.is_empty(),
        "DRAT proof certificate must be generated"
    );

    // Independently verify proof using DratChecker (Reverse Unit Propagation)
    let original_clauses = vec![c1, c2, c3, c4];
    let mut checker = DratChecker::new(original_clauses);
    let verification_result = checker.verify_proof(&proof_str);

    assert_eq!(
        verification_result,
        DratVerificationResult::Valid,
        "DRAT proof certificate must strictly satisfy Reverse Unit Propagation derivation to empty clause 0"
    );

    let proof_check = ProofCertificateCheckResult {
        checker_engine: "smt_sat::DratChecker (Reverse Unit Propagation)".to_string(),
        is_valid: true,
        empty_clause_derived: true,
        verified_steps_count: proof_str.lines().filter(|l| !l.trim().is_empty()).count(),
        diagnostic: "Proof certificate verified empty clause derivation with valid RUP steps"
            .to_string(),
    };

    let raw_bytes = vec![0x31, 0xc0];
    let mut artifact = BlockProvenanceArtifact::new(
        &raw_bytes,
        0x401000,
        &raw_bytes,
        vec!["xor eax, eax".to_string()],
        smt_solver::lifter::BranchResolution::Deterministic(0x401002),
        smt_solver::lifter::DeobfuscationStatus::ProvenInvariant {
            surviving_target: 0x401002,
            dead_target: 0x401000,
        },
        smt_solver::provenance::ProvenanceConfidence::Proven,
    );
    artifact.proof_check = Some(proof_check);

    let md = artifact.to_markdown();
    assert!(md.contains("DRAT Proof Certificate Check"));
    assert!(md.contains("Reverse Unit Propagation"));
    assert!(md.contains("valid=true"));

    let narrative = smt_solver::explain::DeobfuscationExplainer::explain(&artifact);
    assert!(narrative.contains("DRAT Proof Certificate Check"));
    assert!(narrative.contains("Validated independently"));
}
