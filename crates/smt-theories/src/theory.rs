//! Core Theory Solver interface.

use smt_core::term::TermId;
use smt_sat::Lit;

/// Dedicated theory solver interface for specialized theories.
pub trait Theory {
    /// Informs the theory that literal `lit` (representing `term`) was asserted.
    fn assert_term(&mut self, lit: Lit, term: TermId);

    /// Checks consistency of the current theory facts.
    ///
    /// Returns `Ok(())` if consistent, or `Err(conflict_clause)` if inconsistent.
    fn check(&mut self) -> Result<(), Vec<Lit>>;

    /// Returns implied literals and their justification clauses.
    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)>;

    /// Pushes a new backtracking level.
    fn push(&mut self);

    /// Pops the top backtracking level.
    fn pop(&mut self);

    /// Resets all solver state.
    fn reset(&mut self);
}
