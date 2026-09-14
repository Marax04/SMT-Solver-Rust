//! Algorithmic DRAT (Deletion Resolution Asymmetric Tautology) Proof Verifier.
//!
//! Independently verifies that learned and deleted clauses in a DRAT certificate
//! satisfy Reverse Unit Propagation (RUP) against the active clause database,
//! establishing mathematically rigorous proof of UNSAT.

use crate::lit::{Lit, Var};
use std::collections::HashMap;

/// Verification outcome of a DRAT proof certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratVerificationResult {
    /// Proof successfully verified and derived the empty clause via valid RUP steps.
    Valid,
    /// A step in the proof failed Reverse Unit Propagation.
    RupFailure { line: usize, clause: Vec<Lit> },
    /// The proof did not derive the empty clause.
    MissingEmptyClause,
    /// Syntax error parsing the DRAT text.
    ParseError { line: usize, reason: String },
}

/// Standalone DRAT / RUP proof checker.
pub struct DratChecker {
    clauses: Vec<Vec<Lit>>,
}

impl DratChecker {
    /// Creates a checker initialized with the original problem clauses.
    pub fn new(original_clauses: Vec<Vec<Lit>>) -> Self {
        Self {
            clauses: original_clauses,
        }
    }

    /// Verifies a DRAT proof certificate text.
    pub fn verify_proof(&mut self, proof_text: &str) -> DratVerificationResult {
        let mut derived_empty_clause = false;

        for (line_idx, line) in proof_text.lines().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('c') {
                continue;
            }

            let is_deletion = trimmed.starts_with('d') || trimmed.starts_with("d ");
            let content = if is_deletion {
                trimmed[1..].trim()
            } else {
                trimmed
            };

            let mut lits = Vec::new();
            for token in content.split_whitespace() {
                if let Ok(num) = token.parse::<i32>() {
                    if num == 0 {
                        break;
                    }
                    lits.push(Lit::from_dimacs(num));
                } else {
                    return DratVerificationResult::ParseError {
                        line: line_num,
                        reason: format!("Invalid literal token '{}'", token),
                    };
                }
            }

            if is_deletion {
                self.delete_clause(&lits);
            } else {
                if !self.check_rup(&lits) {
                    return DratVerificationResult::RupFailure {
                        line: line_num,
                        clause: lits,
                    };
                }

                if lits.is_empty() {
                    derived_empty_clause = true;
                    break;
                }

                self.clauses.push(lits);
            }
        }

        if derived_empty_clause {
            DratVerificationResult::Valid
        } else {
            DratVerificationResult::MissingEmptyClause
        }
    }

    fn delete_clause(&mut self, lits: &[Lit]) {
        let mut sorted_lits = lits.to_vec();
        sorted_lits.sort();
        if let Some(pos) = self.clauses.iter().position(|c| {
            let mut sc = c.clone();
            sc.sort();
            sc == sorted_lits
        }) {
            self.clauses.swap_remove(pos);
        }
    }

    /// Checks if assuming the negation of all literals in `candidate` produces a conflict
    /// via unit propagation on the active clause database.
    pub fn check_rup(&self, candidate: &[Lit]) -> bool {
        let mut assignments: HashMap<Var, bool> = HashMap::new();

        // 1. Negate all literals in candidate
        for &lit in candidate {
            let var = lit.var();
            let val = lit.is_neg(); // Negating lit: if pos -> false, if neg -> true
            if let Some(&existing) = assignments.get(&var) {
                if existing != val {
                    return true;
                }
            } else {
                assignments.insert(var, val);
            }
        }

        // 2. Unit propagation loop
        loop {
            let mut propagated = false;

            for clause in &self.clauses {
                let mut unassigned = Vec::new();
                let mut satisfied = false;
                let mut false_count = 0;

                for &lit in clause {
                    let var = lit.var();
                    match assignments.get(&var) {
                        Some(&assigned_val) => {
                            let lit_val = if lit.is_pos() { assigned_val } else { !assigned_val };
                            if lit_val {
                                satisfied = true;
                                break;
                            } else {
                                false_count += 1;
                            }
                        }
                        None => {
                            unassigned.push(lit);
                        }
                    }
                }

                if satisfied {
                    continue;
                }

                if false_count == clause.len() {
                    return true;
                }

                if unassigned.len() == 1 && false_count + 1 == clause.len() {
                    let unit_lit = unassigned[0];
                    let var = unit_lit.var();
                    let val = unit_lit.is_pos();
                    assignments.insert(var, val);
                    propagated = true;
                    break;
                }
            }

            if !propagated {
                break;
            }
        }

        false
    }
}
