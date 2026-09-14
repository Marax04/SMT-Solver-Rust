//! CDCL(T) Theory callback interface.

use crate::lit::Lit;

/// Trait defining the bidirectional interaction contract between the SAT core and Theory solvers.
pub trait TheoryCallback {
    /// Informs the theory that a boolean literal mapped to a theory atom has been assigned on the trail.
    fn assert_lit(&mut self, lit: Lit);

    /// Checks whether the current theory state is consistent.
    ///
    /// If consistent, returns `Ok(())`.
    /// If inconsistent, returns `Err(conflict_clause)` containing a minimal set of literals
    /// that caused the theory conflict.
    fn check(&mut self) -> Result<(), Vec<Lit>>;

    /// Queries the theory for any implicit literal propagations.
    ///
    /// Returns a list of pairs `(implied_lit, reason_lits)` where `reason_lits => implied_lit`.
    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)>;

    /// Pushes a new backtracking scope.
    fn push(&mut self);

    /// Pops the top backtracking scope.
    fn pop(&mut self);
}

/// A no-op dummy theory implementation for pure boolean SAT solving.
#[derive(Debug, Clone, Default)]
pub struct NoOpTheory;

impl TheoryCallback for NoOpTheory {
    fn assert_lit(&mut self, _lit: Lit) {}
    fn check(&mut self) -> Result<(), Vec<Lit>> {
        Ok(())
    }
    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)> {
        Vec::new()
    }
    fn push(&mut self) {}
    fn pop(&mut self) {}
}
