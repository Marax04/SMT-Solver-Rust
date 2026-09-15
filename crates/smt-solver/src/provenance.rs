//! Deobfuscation audit trail and proof artifact generator.
//!
//! Captures comprehensive provenance for deobfuscated binary basic blocks,
//! including SHA-256 binary hash, virtual address, raw instruction bytes,
//! disassembly oracle output, path conditions, AST transformations,
//! SMT solver diagnostics, and model counterexamples.

use crate::lifter::{BranchResolution, DeobfuscationStatus};
use crate::synthesis::EquivalenceMetadata;
use sha2::{Digest, Sha256};

/// Confidence classification for audit provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceConfidence {
    /// Formally proven invariant by SMT refutation with zero over-approximations.
    Proven,
    /// Result derived under permissive memory or external over-approximation.
    OverApproximated,
    /// Pattern or algebraic heuristic without complete refutation.
    Heuristic,
    /// Memory violation or execution fault detected.
    FaultDetected,
    /// Resource budget exhausted (e.g. store chain or timeout).
    ResourceExhausted,
    /// Unknown / inconclusive.
    Unknown,
}

/// Formally verified provenance artifact recording a deobfuscated block and branch resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockProvenanceArtifact {
    pub binary_sha256: String,
    pub block_vaddr: u64,
    pub raw_bytes: Vec<u8>,
    pub disassembly: Vec<String>,
    pub path_conditions: Vec<String>,
    pub original_condition_term: String,
    pub simplified_condition_term: String,
    pub resolution: BranchResolution,
    pub deobfuscation_status: DeobfuscationStatus,
    pub confidence: ProvenanceConfidence,
    pub solver_version: String,
    pub git_commit: String,
    pub backend: String,
    pub random_seed: u64,
    pub timeout_ms: u64,
    pub memory_budget_mb: u64,
    pub conflicts_count: u64,
    pub propagations_count: u64,
    pub formula_sha256: String,
    pub pre_simplification_ir_sha256: String,
    pub post_simplification_ir_sha256: String,
    pub metadata: EquivalenceMetadata,
    pub counterexample_model: Option<String>,
    pub applied_rewrites: Vec<String>,
}

impl BlockProvenanceArtifact {
    /// Computes the SHA-256 hash of a binary buffer as a lowercase hex string.
    pub fn compute_sha256(bytes: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        let result = hasher.finalize();
        format!("{:x}", result)
    }

    /// Formats the audit artifact as a human-readable GitHub-flavored markdown report.
    pub fn to_markdown(&self) -> String {
        let mut md = String::new();
        md.push_str(&format!(
            "# Deobfuscation Audit Artifact — Block {:#x}\n\n",
            self.block_vaddr
        ));
        md.push_str(&format!("- **Confidence**: `{:?}`\n", self.confidence));
        md.push_str(&format!("- **Binary SHA-256**: `{}`\n", self.binary_sha256));
        md.push_str(&format!(
            "- **Block Virtual Address**: `{:#x}`\n",
            self.block_vaddr
        ));
        md.push_str(&format!(
            "- **Raw Bytes ({} bytes)**: `{:02x?}`\n",
            self.raw_bytes.len(),
            self.raw_bytes
        ));
        md.push_str(&format!(
            "- **Solver Version**: `{}`\n",
            self.solver_version
        ));
        md.push_str(&format!("- **Git Commit**: `{}`\n", self.git_commit));
        md.push_str(&format!("- **Backend Engine**: `{}`\n", self.backend));
        md.push_str(&format!("- **Random Seed**: `{}`\n", self.random_seed));
        md.push_str(&format!(
            "- **Timeout / Memory Budget**: `{} ms / {} MB`\n",
            self.timeout_ms, self.memory_budget_mb
        ));
        md.push_str(&format!(
            "- **CDCL Conflicts / Propagations**: `{} / {}`\n",
            self.conflicts_count, self.propagations_count
        ));
        md.push_str(&format!(
            "- **Formula SHA-256**: `{}`\n",
            self.formula_sha256
        ));
        md.push_str(&format!(
            "- **Pre-Simplification IR SHA-256**: `{}`\n",
            self.pre_simplification_ir_sha256
        ));
        md.push_str(&format!(
            "- **Post-Simplification IR SHA-256**: `{}`\n",
            self.post_simplification_ir_sha256
        ));
        md.push_str(&format!(
            "- **Solving Duration**: `{} ms`\n",
            self.metadata.solving_time_ms
        ));
        md.push_str(&format!("- **SMT Logic**: `{}`\n", self.metadata.logic));
        md.push_str(&format!(
            "- **Proof Available**: `{}`\n",
            self.metadata.proof_available
        ));
        md.push_str(&format!(
            "- **Model Validated**: `{}`\n\n",
            self.metadata.model_validated
        ));

        md.push_str("## Disassembly\n```asm\n");
        for line in &self.disassembly {
            md.push_str(&format!("{}\n", line));
        }
        md.push_str("```\n\n");

        md.push_str("## Branch Resolution & Deobfuscation Status\n");
        md.push_str(&format!(
            "- **Status**: `{:?}`\n",
            self.deobfuscation_status
        ));
        md.push_str(&format!("- **Resolution**: `{:?}`\n\n", self.resolution));

        md.push_str("## Symbolic Condition\n");
        md.push_str(&format!(
            "- **Original Term**: `{}`\n",
            self.original_condition_term
        ));
        md.push_str(&format!(
            "- **Simplified Term**: `{}`\n\n",
            self.simplified_condition_term
        ));

        if !self.applied_rewrites.is_empty() {
            md.push_str("## Applied Rewrites\n");
            for rw in &self.applied_rewrites {
                md.push_str(&format!("- {}\n", rw));
            }
            md.push('\n');
        }

        if let Some(ref model) = self.counterexample_model {
            md.push_str("## Counterexample Model\n```text\n");
            md.push_str(model);
            md.push_str("\n```\n");
        }

        md
    }

    /// Serializes the provenance artifact into structured JSON.
    pub fn to_json(&self) -> String {
        let hex_bytes: Vec<String> = self
            .raw_bytes
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect();
        let disasm_json: Vec<String> = self
            .disassembly
            .iter()
            .map(|d| format!("\"{}\"", d.replace('"', "\\\"")))
            .collect();
        let path_conds_json: Vec<String> = self
            .path_conditions
            .iter()
            .map(|p| format!("\"{}\"", p.replace('"', "\\\"")))
            .collect();
        let rewrites_json: Vec<String> = self
            .applied_rewrites
            .iter()
            .map(|r| format!("\"{}\"", r.replace('"', "\\\"")))
            .collect();

        format!(
            "{{\n  \"binary_sha256\": \"{}\",\n  \"block_vaddr\": \"{:#x}\",\n  \"confidence\": \"{:?}\",\n  \"solver_version\": \"{}\",\n  \"git_commit\": \"{}\",\n  \"backend\": \"{}\",\n  \"random_seed\": {},\n  \"timeout_ms\": {},\n  \"memory_budget_mb\": {},\n  \"conflicts_count\": {},\n  \"propagations_count\": {},\n  \"formula_sha256\": \"{}\",\n  \"pre_simplification_ir_sha256\": \"{}\",\n  \"post_simplification_ir_sha256\": \"{}\",\n  \"raw_bytes\": [{}],\n  \"disassembly\": [{}],\n  \"path_conditions\": [{}],\n  \"original_condition\": \"{}\",\n  \"simplified_condition\": \"{}\",\n  \"resolution\": \"{:?}\",\n  \"status\": \"{:?}\",\n  \"solving_time_ms\": {},\n  \"logic\": \"{}\",\n  \"counterexample\": {},\n  \"applied_rewrites\": [{}]\n}}",
            self.binary_sha256,
            self.block_vaddr,
            self.confidence,
            self.solver_version,
            self.git_commit,
            self.backend,
            self.random_seed,
            self.timeout_ms,
            self.memory_budget_mb,
            self.conflicts_count,
            self.propagations_count,
            self.formula_sha256,
            self.pre_simplification_ir_sha256,
            self.post_simplification_ir_sha256,
            hex_bytes.iter().map(|b| format!("\"{}\"", b)).collect::<Vec<_>>().join(", "),
            disasm_json.join(", "),
            path_conds_json.join(", "),
            self.original_condition_term.replace('"', "\\\""),
            self.simplified_condition_term.replace('"', "\\\""),
            self.resolution,
            self.deobfuscation_status,
            self.metadata.solving_time_ms,
            self.metadata.logic,
            self.counterexample_model.as_ref().map(|m| format!("\"{}\"", m.replace('"', "\\\"").replace('\n', "\\n"))).unwrap_or_else(|| "null".to_string()),
            rewrites_json.join(", ")
        )
    }
}
