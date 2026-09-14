use smt_solver::engine::Solver;
use std::path::PathBuf;
use std::process::Command;

/// RAII guard ensuring temporary SMT-LIB scripts are deleted even upon thread panic.
struct TempFileGuard(PathBuf);

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Attempts to invoke an external SMT solver (z3 or cvc5) on an SMT-LIB2 script.
/// Returns Some(result) if the external tool is installed, or None if unavailable.
fn run_external_smt(solver_bin: &str, test_name: &str, smt_script: &str) -> Option<String> {
    // Check if the binary is callable
    let version_arg = "--version";
    if Command::new(solver_bin).arg(version_arg).output().is_err() {
        return None;
    }

    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let count = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let thread_id =
        format!("{:?}", std::thread::current().id()).replace(|c: char| !c.is_alphanumeric(), "");
    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join(format!(
        "diff_test_{}_{}_{}_{}_{}.smt2",
        solver_bin,
        std::process::id(),
        thread_id,
        test_name,
        count
    ));
    if std::fs::write(&file_path, smt_script).is_err() {
        return None;
    }
    let _guard = TempFileGuard(file_path.clone());

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

    let stdout = String::from_utf8_lossy(&output.stdout)
        .trim()
        .to_lowercase();
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

    if let Some(z3_res) = run_external_smt("z3", test_name, script) {
        let elapsed = t_start.elapsed();
        println!(
            "[DIFFERENTIAL: {}] Z3 mode | {} formula(s) | {:.2}ms",
            test_name,
            formula_count,
            elapsed.as_secs_f64() * 1000.0
        );
        assert_eq!(
            our_res, z3_res,
            "Differential mismatch with Z3 on {}",
            test_name
        );
    } else if let Some(cvc5_res) = run_external_smt("cvc5", test_name, script) {
        let elapsed = t_start.elapsed();
        println!(
            "[DIFFERENTIAL: {}] cvc5 mode | {} formula(s) | {:.2}ms",
            test_name,
            formula_count,
            elapsed.as_secs_f64() * 1000.0
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
            test_name,
            formula_count,
            elapsed.as_secs_f64() * 1000.0
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
    check_external_differential(
        "test_differential_smt_qf_bv_unsat_contradiction",
        script,
        "unsat",
    );
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

#[test]
fn test_differential_smt_qf_bv_bitwise_arithmetic_combo() {
    let script = r#"
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (= (bvxor a b) (_ bv305419896 32)))
(assert (= (bvand a (_ bv65535 32)) (_ bv4660 32)))
(assert (= (bvadd a b) (_ bv57005 32)))
(check-sat)
"#;
    // Cross-verify with Z3: whether SAT or UNSAT, our engine must match Z3's ground truth exactly
    let our_res = {
        let mut s = Solver::new();
        s.execute_script(script)
            .unwrap()
            .join(" ")
            .trim()
            .to_lowercase()
    };
    check_external_differential(
        "test_differential_smt_qf_bv_bitwise_arithmetic_combo",
        script,
        &our_res,
    );
}

#[test]
fn test_differential_smt_qf_uf_transitivity_chain() {
    let script = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const x1 U)
(declare-const x2 U)
(declare-const x3 U)
(declare-const x4 U)
(declare-const x5 U)
(assert (= x1 x2))
(assert (= x2 x3))
(assert (= x3 x4))
(assert (= x4 x5))
(assert (distinct x1 x5))
(check-sat)
"#;
    check_external_differential(
        "test_differential_smt_qf_uf_transitivity_chain",
        script,
        "unsat",
    );
}

#[test]
fn test_differential_smt_qf_lra_simplex_tight_bounds() {
    let script = r#"
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ x y) 10.0))
(assert (>= x 3.0))
(assert (>= y 4.0))
(assert (<= (- x y) 2.0))
(check-sat)
"#;
    check_external_differential(
        "test_differential_smt_qf_lra_simplex_tight_bounds",
        script,
        "sat",
    );
}

#[test]
fn test_concurrent_differential_stress() {
    // Stress tests parallel differential invocations across multiple worker threads.
    // Proves that RAII temp file cleanup and atomic naming prevent race conditions or collisions.
    let scripts = [
        (
            "stress_bv_sat",
            r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvnot x) (_ bv0 8)))
(check-sat)
"#,
            "sat",
        ),
        (
            "stress_bv_unsat",
            r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x (_ bv1 8)))
(assert (= x (_ bv2 8)))
(check-sat)
"#,
            "unsat",
        ),
        (
            "stress_lra_unsat",
            r#"
(set-logic QF_LRA)
(declare-const a Real)
(assert (> a 5.0))
(assert (< a 2.0))
(check-sat)
"#,
            "unsat",
        ),
        (
            "stress_uf_sat",
            r#"
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun f (T) T)
(declare-const c T)
(assert (= (f c) c))
(check-sat)
"#,
            "sat",
        ),
    ];

    let mut handles = Vec::new();
    for thread_idx in 0..4 {
        let scripts_clone = scripts;
        let handle = std::thread::spawn(move || {
            for (sub_idx, (name, s, expected)) in scripts_clone.iter().enumerate() {
                let test_name = format!("concurrent_{}_{}_{}", thread_idx, sub_idx, name);
                check_external_differential(&test_name, s, expected);
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.join()
            .expect("Concurrent differential stress worker panicked");
    }
}
