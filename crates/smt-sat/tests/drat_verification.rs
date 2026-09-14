use smt_sat::{SatSolver, Var};

#[test]
fn test_drat_proof_format_and_empty_clause() {
    let mut solver = SatSolver::new();
    solver.enable_drat(true);

    // UNSAT formula: (x1) & (!x1)
    let v1 = Var(0);
    solver.add_clause(vec![v1.to_lit()]);
    solver.add_clause(vec![!v1.to_lit()]);

    let res = solver.solve();
    assert_eq!(res, smt_sat::LBool::False);

    let proof_str = solver.proof.to_string();
    assert!(!proof_str.is_empty(), "DRAT proof must not be empty on UNSAT");

    let lines: Vec<&str> = proof_str.lines().map(|l| l.trim()).filter(|l| !l.is_empty()).collect();
    for line in &lines {
        assert!(
            line.ends_with(" 0") || line == &"0",
            "Every DRAT clause line must terminate with literal 0: '{}'",
            line
        );
    }

    // Must end with the empty clause "0"
    assert_eq!(
        lines.last().copied(),
        Some("0"),
        "The last line of a DRAT proof must be the empty clause '0'"
    );

    // Algorithmic RUP verification using DratChecker
    let original_clauses = vec![vec![v1.to_lit()], vec![!v1.to_lit()]];
    let mut checker = smt_sat::DratChecker::new(original_clauses);
    let result = checker.verify_proof(&proof_str);
    assert_eq!(
        result,
        smt_sat::DratVerificationResult::Valid,
        "DRAT proof must pass algorithmic Reverse Unit Propagation check"
    );
}

#[test]
fn test_drat_checker_rup_rejection_of_invalid_step() {
    let v1 = Var(0);
    let v2 = Var(1);
    // Formula: (v1 | v2) -> SAT, cannot derive (!v1) or (!v2) without proof
    let original_clauses = vec![vec![v1.to_lit(), v2.to_lit()]];
    let mut checker = smt_sat::DratChecker::new(original_clauses);

    // Bogus proof claiming (!v1) is a valid RUP derivation
    // In DIMACS: -1 0
    let bogus_proof = "-1 0\n0\n";
    let result = checker.verify_proof(bogus_proof);
    match result {
        smt_sat::DratVerificationResult::RupFailure { line, clause } => {
            assert_eq!(line, 1);
            assert_eq!(clause, vec![!v1.to_lit()]);
        }
        _ => panic!("Expected RupFailure on invalid step, got {:?}", result),
    }
}

#[test]
fn test_drat_checker_multi_step_resolution_and_deletion() {
    let x1 = Var(0);
    let x2 = Var(1);

    // Initial unsatisfiable formula:
    // (x1 | x2) & (!x1 | x2) & (x1 | !x2) & (!x1 | !x2)
    let original_clauses = vec![
        vec![x1.to_lit(), x2.to_lit()],
        vec![!x1.to_lit(), x2.to_lit()],
        vec![x1.to_lit(), !x2.to_lit()],
        vec![!x1.to_lit(), !x2.to_lit()],
    ];

    let mut checker = smt_sat::DratChecker::new(original_clauses);

    // Formulate a multi-step DRAT proof certificate with learned lemmas and clause deletions:
    // 1. Derive resolvent lemma: (x2)
    // 2. Delete redundant original clause: d (x1 | x2)
    // 3. Derive resolvent lemma: (!x2)
    // 4. Derive empty clause: 0
    let drat_script = "\
2 0
d 1 2 0
-2 0
0
";

    let result = checker.verify_proof(drat_script);
    assert_eq!(
        result,
        smt_sat::DratVerificationResult::Valid,
        "Multi-step DRAT certificate with deletion must verify successfully"
    );
}


