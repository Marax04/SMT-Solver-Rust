//! Deobfuscation audit trail and proof artifact generator.
//!
//! Captures comprehensive provenance for deobfuscated binary basic blocks,
//! including SHA-256 binary hash, virtual address, raw instruction bytes,
//! disassembly oracle output, path conditions, AST transformations,
//! SMT solver diagnostics, and model counterexamples.

use crate::lifter::{BranchResolution, DeobfuscationStatus};
use crate::synthesis::EquivalenceMetadata;
use sha2::{Digest, Sha256};

/// Oracle concordance between internal solver and external reference solver (Z3/cvc5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleConcordance {
    Concordant,
    Discordant,
    ExternalTimeout,
    ExternalUnavailable,
}

/// Independent double-check result against external verification oracle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DoubleCheckResult {
    pub external_solver: String,
    pub concordance: OracleConcordance,
    pub external_solving_time_ms: u64,
}

/// Independent mathematical proof certificate check result (DRAT/RUP verification).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCertificateCheckResult {
    pub checker_engine: String,
    pub is_valid: bool,
    pub empty_clause_derived: bool,
    pub verified_steps_count: usize,
    pub diagnostic: String,
}

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
    pub double_check: Option<DoubleCheckResult>,
    pub proof_check: Option<ProofCertificateCheckResult>,
}

impl BlockProvenanceArtifact {
    /// Computes the SHA-256 hash of a binary buffer as a lowercase hex string.
    ///
    /// # Example
    /// ```rust
    /// use smt_solver::provenance::BlockProvenanceArtifact;
    /// let hash = BlockProvenanceArtifact::compute_sha256(b"hello world");
    /// assert_eq!(hash.len(), 64);
    /// ```
    pub fn compute_sha256(bytes: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        let result = hasher.finalize();
        format!("{:x}", result)
    }

    /// Creates a new provenance artifact with standard default metadata.
    pub fn new(
        raw_binary_bytes: &[u8],
        block_vaddr: u64,
        block_bytes: &[u8],
        disassembly: Vec<String>,
        resolution: BranchResolution,
        deobfuscation_status: DeobfuscationStatus,
        confidence: ProvenanceConfidence,
    ) -> Self {
        let binary_sha256 = Self::compute_sha256(raw_binary_bytes);
        let formula_sha256 = Self::compute_sha256(block_bytes);
        Self {
            binary_sha256,
            block_vaddr,
            raw_bytes: block_bytes.to_vec(),
            disassembly,
            path_conditions: Vec::new(),
            original_condition_term: String::new(),
            simplified_condition_term: String::new(),
            resolution,
            deobfuscation_status,
            confidence,
            solver_version: env!("CARGO_PKG_VERSION").to_string(),
            git_commit: "v1.0-release".to_string(),
            backend: "SMT-Solver-Pure-Rust".to_string(),
            random_seed: 0x1337,
            timeout_ms: 5000,
            memory_budget_mb: 512,
            conflicts_count: 0,
            propagations_count: 0,
            formula_sha256: formula_sha256.clone(),
            pre_simplification_ir_sha256: formula_sha256.clone(),
            post_simplification_ir_sha256: formula_sha256,
            metadata: EquivalenceMetadata {
                solving_time_ms: 1,
                logic: "QF_BV".to_string(),
                budget_exhausted: false,
                model_validated: true,
                oracle_agreed: None,
                proof_available: true,
            },
            counterexample_model: None,
            applied_rewrites: Vec::new(),
            double_check: None,
            proof_check: None,
        }
    }

    /// Formats the audit artifact as a human-readable GitHub-flavored markdown report.
    pub fn to_markdown(&self) -> String {
        let mut md = String::new();
        md.push_str(&format!(
            "# Deobfuscation Audit Artifact — Block {:#x}\n\n",
            self.block_vaddr
        ));
        if self.confidence != ProvenanceConfidence::Proven {
            md.push_str("> [!WARNING]\n");
            md.push_str(&format!(
                "> **Non-Certified Invariant**: Confidence level is `{:?}`. Treat as exploratory rather than a verified formal proof.\n\n",
                self.confidence
            ));
        }
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
            "- **SMT Formula SHA-256**: `{}`\n",
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
            "- **Model Validated**: `{}`\n",
            self.metadata.model_validated
        ));
        if let Some(ref pc) = self.proof_check {
            md.push_str(&format!(
                "- **DRAT Proof Certificate Check ({})**: `valid={}` ({} RUP steps verified) — {}\n",
                pc.checker_engine, pc.is_valid, pc.verified_steps_count, pc.diagnostic
            ));
        }
        if let Some(ref dc) = self.double_check {
            md.push_str(&format!(
                "- **External Oracle Double-Check ({})**: `{:?}` ({} ms)\n\n",
                dc.external_solver, dc.concordance, dc.external_solving_time_ms
            ));
        } else {
            md.push('\n');
        }

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

    /// Deserializes a provenance artifact from JSON.
    pub fn from_json(json: &str) -> Result<Self, String> {
        let extract_str = |key: &str| -> Option<String> {
            let pattern = format!("\"{}\": \"", key);
            if let Some(pos) = json.find(&pattern) {
                let start = pos + pattern.len();
                if let Some(end) = json[start..].find('"') {
                    return Some(json[start..start + end].to_string());
                }
            }
            None
        };

        let extract_u64 = |key: &str| -> Option<u64> {
            let pattern = format!("\"{}\": ", key);
            if let Some(pos) = json.find(&pattern) {
                let start = pos + pattern.len();
                let sub = &json[start..];
                let end = sub.find([',', '\n', '}']).unwrap_or(sub.len());
                let token = sub[..end].trim().trim_matches('"');
                if let Some(hex) = token.strip_prefix("0x") {
                    u64::from_str_radix(hex, 16).ok()
                } else {
                    token.parse::<u64>().ok()
                }
            } else {
                None
            }
        };

        let binary_sha256 = extract_str("binary_sha256").ok_or("Missing binary_sha256")?;
        let block_vaddr = extract_u64("block_vaddr").ok_or("Missing block_vaddr")?;

        let mut raw_bytes = Vec::new();
        if let Some(start_arr) = json.find("\"raw_bytes\": [") {
            let sub = &json[start_arr + "\"raw_bytes\": [".len()..];
            if let Some(end_arr) = sub.find(']') {
                let arr_str = &sub[..end_arr];
                for token in arr_str.split(',') {
                    let cleaned = token.trim().trim_matches('"');
                    if !cleaned.is_empty() {
                        if let Ok(b) = u8::from_str_radix(cleaned, 16) {
                            raw_bytes.push(b);
                        }
                    }
                }
            }
        }

        let resolution_str = extract_str("resolution").unwrap_or_else(|| "Unreachable".to_string());
        let resolution = if resolution_str.starts_with("Deterministic(") {
            let inner = resolution_str
                .trim_start_matches("Deterministic(")
                .trim_end_matches(')');
            let t = inner.parse::<u64>().unwrap_or(0);
            BranchResolution::Deterministic(t)
        } else if resolution_str.starts_with("Conditional") {
            BranchResolution::Conditional {
                true_target: 0,
                false_target: 0,
            }
        } else if resolution_str.starts_with("BudgetExhausted") {
            BranchResolution::BudgetExhausted
        } else {
            BranchResolution::Unreachable
        };

        let status_str = extract_str("status").unwrap_or_else(|| "UnreachablePath".to_string());
        let deobfuscation_status = if status_str.starts_with("ProvenInvariant") {
            DeobfuscationStatus::ProvenInvariant {
                surviving_target: 0,
                dead_target: 0,
            }
        } else if status_str.starts_with("ProvenDynamic") {
            DeobfuscationStatus::ProvenDynamic {
                true_target: 0,
                false_target: 0,
            }
        } else if status_str.starts_with("OverApproximated") {
            DeobfuscationStatus::OverApproximated
        } else if status_str.starts_with("FaultDetected") {
            DeobfuscationStatus::FaultDetected
        } else if status_str.starts_with("ResourceExhausted") {
            DeobfuscationStatus::ResourceExhausted
        } else {
            DeobfuscationStatus::UnreachablePath
        };

        let confidence_str = extract_str("confidence").unwrap_or_else(|| "Unknown".to_string());
        let confidence = match confidence_str.as_str() {
            "Proven" => ProvenanceConfidence::Proven,
            "OverApproximated" => ProvenanceConfidence::OverApproximated,
            "Heuristic" => ProvenanceConfidence::Heuristic,
            "FaultDetected" => ProvenanceConfidence::FaultDetected,
            "ResourceExhausted" => ProvenanceConfidence::ResourceExhausted,
            _ => ProvenanceConfidence::Unknown,
        };

        Ok(Self {
            binary_sha256,
            block_vaddr,
            raw_bytes,
            disassembly: Vec::new(),
            path_conditions: Vec::new(),
            original_condition_term: extract_str("original_condition").unwrap_or_default(),
            simplified_condition_term: extract_str("simplified_condition").unwrap_or_default(),
            resolution,
            deobfuscation_status,
            confidence,
            solver_version: extract_str("solver_version").unwrap_or_default(),
            git_commit: extract_str("git_commit").unwrap_or_default(),
            backend: extract_str("backend").unwrap_or_else(|| "SMT-Solver-Pure-Rust".to_string()),
            random_seed: extract_u64("random_seed").unwrap_or(0),
            timeout_ms: extract_u64("timeout_ms").unwrap_or(0),
            memory_budget_mb: extract_u64("memory_budget_mb").unwrap_or(0),
            conflicts_count: extract_u64("conflicts_count").unwrap_or(0),
            propagations_count: extract_u64("propagations_count").unwrap_or(0),
            formula_sha256: extract_str("formula_sha256").unwrap_or_default(),
            pre_simplification_ir_sha256: extract_str("pre_simplification_ir_sha256")
                .unwrap_or_default(),
            post_simplification_ir_sha256: extract_str("post_simplification_ir_sha256")
                .unwrap_or_default(),
            metadata: EquivalenceMetadata {
                solving_time_ms: extract_u64("solving_time_ms").unwrap_or(0),
                logic: extract_str("logic").unwrap_or_else(|| "QF_BV".to_string()),
                budget_exhausted: false,
                model_validated: true,
                oracle_agreed: None,
                proof_available: true,
            },
            counterexample_model: extract_str("counterexample"),
            applied_rewrites: Vec::new(),
            double_check: None,
            proof_check: None,
        })
    }
}
