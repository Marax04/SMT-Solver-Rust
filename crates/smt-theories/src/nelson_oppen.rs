//! Nelson-Oppen & CDCL(T) Multi-Theory Coordinator.

use crate::array::ArraySolver;
use crate::euf::EufSolver;
use crate::simplex::SimplexSolver;
use crate::theory::Theory;
use smt_core::sort::SortArena;
use smt_core::term::{TermArena, TermId};
use smt_sat::{Lit, TheoryCallback};
use std::collections::HashMap;

/// Central CDCL(T) Theory Coordinator implementing `TheoryCallback` for the SAT solver.
#[derive(Debug)]
pub struct TheoryCoordinator<'a> {
    pub euf: EufSolver<'a>,
    pub simplex: SimplexSolver<'a>,
    pub array: ArraySolver<'a>,
    var_to_term: HashMap<smt_sat::Var, (Lit, TermId)>,
    pub shared_terms: Vec<TermId>,
}

impl<'a> TheoryCoordinator<'a> {
    /// Creates a new coordinator managing all specialized theories.
    pub fn new(arena: &'a TermArena, sorts: &'a SortArena) -> Self {
        Self {
            euf: EufSolver::new(arena),
            simplex: SimplexSolver::new(arena),
            array: ArraySolver::new(sorts),
            var_to_term: HashMap::with_capacity(512),
            shared_terms: Vec::with_capacity(64),
        }
    }

    /// Registers a mapping from SAT literal to intermediate TermId.
    pub fn register_lit_term(&mut self, lit: Lit, term: TermId) {
        self.var_to_term.insert(lit.var(), (lit, term));
    }

    /// Registers a shared variable between multiple theories.
    pub fn register_shared_term(&mut self, term: TermId) {
        if !self.shared_terms.contains(&term) {
            self.shared_terms.push(term);
        }
    }
}

impl<'a> TheoryCallback for TheoryCoordinator<'a> {
    fn assert_lit(&mut self, assigned_lit: Lit) {
        if let Some(&(_reg_lit, term)) = self.var_to_term.get(&assigned_lit.var()) {
            self.euf.assert_term(assigned_lit, term);
            self.simplex.assert_term(assigned_lit, term);
            self.array.assert_term(assigned_lit, term);
        }
    }

    fn check(&mut self) -> Result<(), Vec<Lit>> {
        // Initial theory checks
        self.euf.check()?;
        self.simplex.check()?;
        self.array.check()?;

        // Cross-theory equality sharing (Nelson-Oppen arrangement propagation)
        for i in 0..self.shared_terms.len() {
            for j in (i + 1)..self.shared_terms.len() {
                let ti = self.shared_terms[i];
                let tj = self.shared_terms[j];

                // 1. Check if EUF has deduced ti == tj
                if self.euf.find(ti) == self.euf.find(tj) {
                    let vi = self.simplex.get_or_create_var(ti, false);
                    let vj = self.simplex.get_or_create_var(tj, false);
                    let val_i = self.simplex.get_value(vi);
                    let val_j = self.simplex.get_value(vj);
                    if val_i != val_j {
                        self.simplex.check()?;
                    }
                } else {
                    // 2. Check if Simplex has deduced ti == tj
                    let vi = self.simplex.get_or_create_var(ti, false);
                    let vj = self.simplex.get_or_create_var(tj, false);
                    if self.simplex.is_equal_entailed(vi, vj) {
                        self.euf.merge(ti, tj, None);
                    }
                }
            }
        }

        // Re-check EUF after shared equality propagation
        self.euf.check()?;

        Ok(())
    }

    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)> {
        let mut props = Vec::new();
        props.extend(self.euf.propagate());
        props.extend(self.simplex.propagate());
        props.extend(self.array.propagate());
        props
    }

    fn push(&mut self) {
        self.euf.push();
        self.simplex.push();
        self.array.push();
    }

    fn pop(&mut self) {
        self.euf.pop();
        self.simplex.pop();
        self.array.pop();
    }
}
