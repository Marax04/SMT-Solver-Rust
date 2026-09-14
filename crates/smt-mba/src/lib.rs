//! Mixed Boolean-Arithmetic (MBA) Deobfuscation and Simplification Engine.
//!
//! Provides dedicated algorithms for simplifying obfuscated MBA expressions:
//! - Truth table vector space reduction (MBA-Blast / SiMBA style)
//! - Algebraic canonicalization (De Morgan, idempotence, double negation)
//! - I/O-guided program synthesis (Syntia style) with SMT equivalence oracles

pub mod canonicalize;
pub mod gf2;
pub mod linear_mba;
pub mod truth_table;
pub mod zhegalkin;

pub use canonicalize::MbaCanonicalizer;
pub use gf2::Gf2Matrix;
pub use linear_mba::LinearMbaSimplifier;
pub use truth_table::TruthTable;
pub use zhegalkin::{Monomial, ZhegalkinPolynomial};

use smt_core::sort::SortArena;
use smt_core::term::{TermArena, TermId};

/// Unified MBA algebraic simplifier pipeline (pure algebra).
#[derive(Debug, Default)]
pub struct MbaSimplifier;

impl MbaSimplifier {
    pub fn new() -> Self {
        Self
    }

    /// Simplifies an expression using algebraic canonicalization, linear MBA reduction, and Zhegalkin ANF.
    pub fn simplify(
        &mut self,
        term_id: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> TermId {
        // Step 1: Algebraic canonicalization
        let canonical = MbaCanonicalizer::normalize(term_id, terms, sorts);

        // Step 2: Linear MBA reduction via truth tables (up to 4 vars)
        if let Some(simplified) = LinearMbaSimplifier::simplify(canonical, terms, sorts) {
            return simplified;
        }

        // Step 3: Zhegalkin Normal Form canonicalization for bitwise/boolean polynomials
        if let Some(simplified) = ZhegalkinPolynomial::simplify(canonical, terms, sorts) {
            return simplified;
        }

        canonical
    }
}
