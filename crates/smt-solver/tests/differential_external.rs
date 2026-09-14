use smt_solver::engine::Solver;
use std::process::Command;

/// Attempts to invoke an external SMT solver (z3 or cvc5) on an SMT-LIB2 script.
/// Returns Some(result) if the external tool is installed, or None if unavailable.
fn run_external_smt(solver_bin: &str, smt_script: &str) -> Option<String> {
    // Check if the binary is callable
    let version_arg = if solver_bin == "z3" {
        "--version"
    } else {
        "--version"
    };
    if Command::new(solver_bin).arg(version_arg).output().is_err() {
        return None;
    }

    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join(format!("diff_test_{}_{}.smt2", solver_bin, std::process::id()));
    if std::fs::write(&file_path, smt_script).is_err() {
        return None;
    }

    let output = if solver_bin == "z3" {
        Command::new("z3")
            .arg("-smt2")
            .arg(&file_path)
            .output()
            .ok()?
    } else {
        Command::new("cvc5")
            .arg("--lang=smt2")
            .arg(&file_path)
            .output()
            .ok()?
    };

    let _ = std::fs::remove_file(&file_path);
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_lowercase();
    if stdout.contains("sat") && !stdout.contains("unsat") {
        Some("sat".to_string())
    } else if stdout.contains("unsat") {
        Some("unsat".to_string())
    } else if stdout.contains("unknown") {
        Some("unknown".to_string())
    } else {
        None
    }
}

fn check_external_differential(test_name: &str, script: &str, expected_fallback: &str) {
    let t_start = std::time::Instant::now();
    let mut solver = Solver::new();
    let res = solver.execute_script(script).expect("Script should parse");
    let our_res = res.join(" ").trim().to_lowercase();

    // Count (check-sat) calls as a proxy for formula complexity
    let formula_count = script.matches("(check-sat)").count();

    if let Some(z3_res) = run_external_smt("z3", script) {
        let elapsed = t_start.elapsed();
        println!(
            "[DIFFERENTIAL: {}] Z3 mode | {} formula(s) | {:.2}ms",
            test_name, formula_count, elapsed.as_secs_f64() * 1000.0
        );
        assert_eq!(
            our_res, z3_res,
            "Differential mismatch with Z3 on {}",
            test_name
        );
    } else if let Some(cvc5_res) = run_external_smt("cvc5", script) {
        let elapsed = t_start.elapsed();
        println!(
            "[DIFFERENTIAL: {}] cvc5 mode | {} formula(s) | {:.2}ms",
            test_name, formula_count, elapsed.as_secs_f64() * 1000.0
        );
        assert_eq!(
            our_res, cvc5_res,
            "Differential mismatch with cvc5 on {}",
            test_name
        );
    } else {
        let is_ci = std::env::var("CI").is_ok();
        let is_strict = std::env::var("STRICT_DIFFERENTIAL").is_ok();

        // CI auto-detection: fail fast rather than silently degrading to self-consistency.
        // Any CI system (GitHub Actions, GitLab CI, CircleCI, etc.) sets CI=true by convention.
        if is_ci && !is_strict {
            panic!(
                "[DIFFERENTIAL: {}] Running in a CI environment (CI env var is set) \
                 but STRICT_DIFFERENTIAL=1 is NOT set. \
                 External solvers (z3/cvc5) are unavailable — this differential test \
                 would silently degrade to self-consistency mode, providing no cross-validation. \
                 FIX: Add `STRICT_DIFFERENTIAL: \"1\"` to your CI workflow AND ensure z3 or cvc5 \
                 is installed (e.g., `apt-get install z3` or use the z3-solver Python package).",
                test_name
            );
        }

        if is_strict {
            panic!(
                "[DIFFERENTIAL: {}] STRICT_DIFFERENTIAL is enabled, but neither z3 nor cvc5 was found in PATH!",
                test_name
            );
        }
        let elapsed = t_start.elapsed();
        println!(
            "[DIFFERENTIAL: {}] Notice: External solvers absent in PATH — \
             self-consistency validation only | {} formula(s) | {:.2}ms",
            test_name, formula_count, elapsed.as_secs_f64() * 1000.0
        );
        assert_eq!(our_res, expected_fallback);
    }
}

#[test]
fn test_differential_smt_qf_bv() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvxor x y) (_ bv42 8)))
(assert (= (bvand x y) (_ bv0 8)))
(check-sat)
"#;
    check_external_differential("test_differential_smt_qf_bv", script, "sat");
}

#[test]
fn test_differential_smt_qf_bv_unsat_contradiction() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(assert (= (bvadd x (_ bv1 16)) x))
(check-sat)
"#;
    check_external_differential("test_differential_smt_qf_bv_unsat_contradiction", script, "unsat");
}

#[test]
fn test_differential_smt_qf_uf_congruence() {
    let script = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(assert (= a b))
(assert (distinct (f a) (f b)))
(check-sat)
"#;
    check_external_differential("test_differential_smt_qf_uf_congruence", script, "unsat");
}

#[test]
fn test_differential_smt_qf_lra_feasibility() {
    let script = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 10.0))
(assert (<= x 5.0))
(check-sat)
"#;
    check_external_differential("test_differential_smt_qf_lra_feasibility", script, "unsat");
}

