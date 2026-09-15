//! Natural-language explainability engine for deobfuscated basic blocks and branches.
//!
//! Translates formal SMT refutations, MBA algebraic reductions, and branch pruning
//! decisions into human-readable narrative reports for security analysts and reverse engineers.

use crate::lifter::BranchResolution;
use crate::provenance::{BlockProvenanceArtifact, OracleConcordance, ProvenanceConfidence};

/// Explains deobfuscation results and SMT refutations in clear, structured narrative prose.
pub struct DeobfuscationExplainer;

impl DeobfuscationExplainer {
    /// Generates a human-readable explanation of the analysis for a given block provenance artifact.
    ///
    /// # Example
    /// ```rust
    /// use smt_solver::explain::DeobfuscationExplainer;
    /// use smt_solver::provenance::{BlockProvenanceArtifact, ProvenanceConfidence};
    /// use smt_solver::lifter::{BranchResolution, DeobfuscationStatus};
    ///
    /// let artifact = BlockProvenanceArtifact::new(
    ///     &[0x90],
    ///     0x401000,
    ///     &[0x90],
    ///     vec!["nop".to_string()],
    ///     BranchResolution::Deterministic(0x401001),
    ///     DeobfuscationStatus::ProvenInvariant { surviving_target: 0x401001, dead_target: 0 },
    ///     ProvenanceConfidence::Proven,
    /// );
    /// let narrative = DeobfuscationExplainer::explain(&artifact);
    /// assert!(narrative.contains("Formally Certified"));
    /// ```
    pub fn explain(artifact: &BlockProvenanceArtifact) -> String {
        let mut out = String::new();

        out.push_str(&format!(
            "### Deobfuscation Narrative: Block at {:#x}\n\n",
            artifact.block_vaddr
        ));

        // 1. Confidence & Safety Assessment
        match artifact.confidence {
            ProvenanceConfidence::Proven => {
                out.push_str("> [!NOTE]\n> **Formally Certified**: This result is mathematically proven with zero unmapped memory over-approximations.\n\n");
            }
            ProvenanceConfidence::OverApproximated => {
                out.push_str("> [!WARNING]\n> **Over-Approximation Detected**: Analysis relied on exploratory unmapped memory reads. Treat as an invariant hypothesis, not a strict formal proof.\n\n");
            }
            ProvenanceConfidence::FaultDetected => {
                out.push_str("> [!CAUTION]\n> **Memory Access Fault**: The basic block triggered an illegal memory access or permission violation during execution.\n\n");
            }
            ProvenanceConfidence::ResourceExhausted => {
                out.push_str("> [!WARNING]\n> **Budget Exhausted**: The analysis exceeded time, store-chain, or AST complexity budgets. Branch resolution could not be fully proven.\n\n");
            }
            ProvenanceConfidence::Heuristic => {
                out.push_str("> [!NOTE]\n> **Heuristic Classification**: Result was identified via syntactic or algebraic patterns without complete SMT refutation.\n\n");
            }
            ProvenanceConfidence::Unknown => {
                out.push_str("> [!WARNING]\n> **Inconclusive Result**: Solver could not definitively determine satisfiability.\n\n");
            }
        }

        // 2. Control Flow Analysis
        match artifact.resolution {
            BranchResolution::Deterministic(target) => {
                out.push_str(&format!(
                    "1. **Control Flow Invariance**: The conditional branch at this block is **invariant**. Control unconditionally transfers to `{:#x}`.\n",
                    target
                ));
                out.push_str("2. **Dead Code Elimination**: The alternate branch target is unsatisfiable (UNSAT) under the block's path constraints and can be safely pruned from the Control Flow Graph.\n");
            }
            BranchResolution::Conditional {
                true_target,
                false_target,
            } => {
                out.push_str(&format!(
                    "1. **Dynamic Branching**: The branch is genuinely dynamic. Both the True branch (`{:#x}`) and the False branch (`{:#x}`) are feasible under different concrete input assignments.\n",
                    true_target, false_target
                ));
            }
            BranchResolution::MemoryFault(kind, addr) => {
                out.push_str(&format!(
                    "1. **Execution Fault**: A `{:?}` occurred at address `{:#x}` before the branch terminator could be safely evaluated.\n",
                    kind, addr
                ));
            }
            BranchResolution::BudgetExhausted => {
                out.push_str("1. **Resource Budget Exhausted**: Path exploration or symbolic store-chain depth limits were reached.\n");
            }
            BranchResolution::Unreachable => {
                out.push_str("1. **Unreachable Block**: Both outgoing branch paths are mathematically unsatisfiable under active path conditions.\n");
            }
        }

        // 3. Algebraic Simplifications
        if !artifact.applied_rewrites.is_empty() {
            out.push_str("\n3. **Algebraic Rewrites Applied**:\n");
            for rw in &artifact.applied_rewrites {
                out.push_str(&format!("   - `{}`\n", rw));
            }
        }

        // 4. Double-Check Oracle Verification
        if let Some(dc) = &artifact.double_check {
            out.push_str("\n4. **Independent Oracle Verification**:\n");
            match dc.concordance {
                OracleConcordance::Concordant => {
                    out.push_str(&format!(
                        "   - Verified concordant with external solver `{}` in {} ms.\n",
                        dc.external_solver, dc.external_solving_time_ms
                    ));
                }
                OracleConcordance::Discordant => {
                    out.push_str(&format!(
                        "   - **DISCORDANCE DETECTED** with external solver `{}`! Please inspect counterexample.\n",
                        dc.external_solver
                    ));
                }
                OracleConcordance::ExternalTimeout => {
                    out.push_str(&format!(
                        "   - External solver `{}` timed out after {} ms.\n",
                        dc.external_solver, dc.external_solving_time_ms
                    ));
                }
                OracleConcordance::ExternalUnavailable => {
                    out.push_str(
                        "   - External reference solver was not found on the system PATH.\n",
                    );
                }
            }
        }

        out
    }
}
