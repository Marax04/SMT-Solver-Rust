//! Theory of Arrays with lazy read-over-write axiom instantiation.

use crate::theory::Theory;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_sat::Lit;
use std::collections::HashSet;

/// Array theory solver managing read-over-write axiom expansion.
#[derive(Debug, Clone)]
pub struct ArraySolver<'a> {
    pub sorts: &'a SortArena,
    /// Instantiated axioms cache: (array, store_idx, select_idx)
    instantiated: HashSet<(TermId, TermId, TermId)>,
    /// Axiom clauses generated to be asserted into SAT solver.
    pending_axioms: Vec<TermId>,
    scopes: Vec<usize>,
    inst_history: Vec<(TermId, TermId, TermId)>,
    /// Maximum lazy axiom instantiations allowed to prevent combinatorial explosion.
    pub max_axioms: usize,
}

impl<'a> ArraySolver<'a> {
    /// Creates a new Array solver.
    pub fn new(sorts: &'a SortArena) -> Self {
        Self {
            sorts,
            instantiated: HashSet::with_capacity(256),
            pending_axioms: Vec::with_capacity(128),
            scopes: Vec::with_capacity(32),
            inst_history: Vec::with_capacity(256),
            max_axioms: 10_000,
        }
    }

    /// Scans a term for array operations and registers read-over-write axioms.
    pub fn scan_term(&mut self, id: TermId, arena: &mut TermArena) {
        if self.instantiated.len() >= self.max_axioms {
            return;
        }
        let term = arena.get(id).clone();
        if let Op::Select = term.op {
            let arr = term.args[0];
            let select_idx = term.args[1];

            // If base array is a store: (select (store a store_idx val) select_idx)
            let arr_term = arena.get(arr).clone();
            if let Op::Store = arr_term.op {
                let base_arr = arr_term.args[0];
                let store_idx = arr_term.args[1];
                let val = arr_term.args[2];

                let key = (base_arr, store_idx, select_idx);
                if !self.instantiated.contains(&key) {
                    if self.instantiated.len() >= self.max_axioms {
                        return;
                    }
                    self.instantiated.insert(key);
                    self.inst_history.push(key);

                    // Axiom 1: (= select_idx store_idx) => (= (select (store a store_idx val) select_idx) val)
                    let idx_eq = arena.eq(select_idx, store_idx, self.sorts);
                    let select_store = arena.select(arr, select_idx, self.sorts).unwrap();
                    let val_eq = arena.eq(select_store, val, self.sorts);
                    let ax1 = arena.implies(idx_eq, val_eq, self.sorts);
                    self.pending_axioms.push(ax1);

                    // Axiom 2: (not (= select_idx store_idx)) => (= (select (store a store_idx val) select_idx) (select a select_idx))
                    let not_idx_eq = arena.not(idx_eq);
                    let select_base = arena.select(base_arr, select_idx, self.sorts).unwrap();
                    let base_eq = arena.eq(select_store, select_base, self.sorts);
                    let ax2 = arena.implies(not_idx_eq, base_eq, self.sorts);
                    self.pending_axioms.push(ax2);
                }
            }
        }

        for &arg in &term.args {
            self.scan_term(arg, arena);
        }
    }

    /// Pops pending generated axioms to be asserted in the preprocessor / SAT solver.
    pub fn take_pending_axioms(&mut self) -> Vec<TermId> {
        std::mem::take(&mut self.pending_axioms)
    }
}

impl<'a> Theory for ArraySolver<'a> {
    fn assert_term(&mut self, _lit: Lit, _term: TermId) {}

    fn check(&mut self) -> Result<(), Vec<Lit>> {
        Ok(())
    }

    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)> {
        Vec::new()
    }

    fn push(&mut self) {
        self.scopes.push(self.inst_history.len());
    }

    fn pop(&mut self) {
        if let Some(target) = self.scopes.pop() {
            while self.inst_history.len() > target {
                let key = self.inst_history.pop().unwrap();
                self.instantiated.remove(&key);
            }
        }
    }

    fn reset(&mut self) {
        self.instantiated.clear();
        self.pending_axioms.clear();
        self.scopes.clear();
        self.inst_history.clear();
    }
}
