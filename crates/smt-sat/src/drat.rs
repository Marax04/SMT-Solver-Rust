//! DRAT (Deletion Resolution Asymmetric Tautology) proof emission.

use crate::lit::Lit;
use std::fmt::Write;

/// Traces DRAT proofs for independent external verification of UNSAT answers.
#[derive(Debug, Clone, Default)]
pub struct DratProof {
    enabled: bool,
    buffer: String,
}

impl DratProof {
    /// Creates a proof tracer.
    pub fn new(enabled: bool) -> Self {
        Self {
            enabled,
            buffer: String::with_capacity(4096),
        }
    }

    /// Appends a learned clause to the proof trace.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        if !self.enabled {
            return;
        }
        for lit in lits {
            let _ = write!(self.buffer, "{} ", lit.to_dimacs());
        }
        self.buffer.push_str("0\n");
    }

    /// Appends a deleted clause to the proof trace.
    pub fn delete_clause(&mut self, lits: &[Lit]) {
        if !self.enabled {
            return;
        }
        self.buffer.push_str("d ");
        for lit in lits {
            let _ = write!(self.buffer, "{} ", lit.to_dimacs());
        }
        self.buffer.push_str("0\n");
    }

    /// Returns the proof certificate text.
    pub fn text(&self) -> &str {
        &self.buffer
    }

    /// Clears the proof buffer.
    pub fn clear(&mut self) {
        self.buffer.clear();
    }
}

impl std::fmt::Display for DratProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.buffer)
    }
}
