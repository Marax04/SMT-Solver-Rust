//! Two-Watched Literals (2WL) watcher structure.

use crate::clause::ClauseId;
use crate::lit::Lit;

/// A watcher record attached to a watched literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Watcher {
    /// Clause ID being watched.
    pub clause: ClauseId,
    /// Blocker literal: if this literal is already True under current assignment,
    /// the clause is satisfied and we don't need to read the clause from memory.
    pub blocker: Lit,
}

impl Watcher {
    /// Creates a new watcher.
    #[inline]
    pub fn new(clause: ClauseId, blocker: Lit) -> Self {
        Self { clause, blocker }
    }
}

/// Watch lists mapping each literal to its watchers.
#[derive(Debug, Clone, Default)]
pub struct WatchList {
    watches: Vec<Vec<Watcher>>,
}

impl WatchList {
    /// Creates a new empty watch list.
    pub fn new() -> Self {
        Self {
            watches: Vec::with_capacity(1024),
        }
    }

    /// Ensures capacity for variables up to `max_var`.
    pub fn ensure_var(&mut self, var_count: usize) {
        let required = var_count * 2;
        if self.watches.len() < required {
            self.watches.resize(required, Vec::new());
        }
    }

    /// Adds a watcher for a literal.
    #[inline]
    pub fn add(&mut self, lit: Lit, watcher: Watcher) {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        self.watches[idx].push(watcher);
    }

    /// Access watchers for a literal.
    #[inline]
    pub fn get(&self, lit: Lit) -> &[Watcher] {
        let idx = lit.index();
        if idx < self.watches.len() {
            &self.watches[idx]
        } else {
            &[]
        }
    }

    /// Mutably access watchers for a literal.
    #[inline]
    pub fn get_mut(&mut self, lit: Lit) -> &mut Vec<Watcher> {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        &mut self.watches[idx]
    }
}
