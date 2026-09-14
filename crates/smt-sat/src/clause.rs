//! Clause storage and Arena representation.

use crate::lit::Lit;
use std::ops::{Index, IndexMut};

/// Unique identifier for a clause within the `ClauseArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(pub u32);

/// A disjunctive clause of literals.
#[derive(Debug, Clone)]
pub struct Clause {
    /// Literals contained in the clause.
    pub lits: Vec<Lit>,
    /// Literal Block Distance (used by Glucose-style restarts and clause DB reduction).
    pub lbd: u32,
    /// Dynamic activity score for learned clause eviction.
    pub activity: f64,
    /// Whether this clause was learned during conflict analysis.
    pub learned: bool,
    /// Marked as dead / deleted in database management.
    pub deleted: bool,
}

impl Clause {
    /// Creates an original (problem) clause.
    pub fn new_original(lits: Vec<Lit>) -> Self {
        Self {
            lits,
            lbd: 0,
            activity: 0.0,
            learned: false,
            deleted: false,
        }
    }

    /// Creates a learned clause from conflict analysis.
    pub fn new_learned(lits: Vec<Lit>, lbd: u32) -> Self {
        Self {
            lits,
            lbd,
            activity: 0.0,
            learned: true,
            deleted: false,
        }
    }

    /// Number of literals.
    #[inline]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// True if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
}

impl Index<usize> for Clause {
    type Output = Lit;

    #[inline]
    fn index(&self, idx: usize) -> &Self::Output {
        &self.lits[idx]
    }
}

impl IndexMut<usize> for Clause {
    #[inline]
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        &mut self.lits[idx]
    }
}

/// Contiguous arena for all active and learned clauses.
#[derive(Debug, Clone, Default)]
pub struct ClauseArena {
    clauses: Vec<Clause>,
}

impl ClauseArena {
    /// Creates a new clause arena.
    pub fn new() -> Self {
        Self {
            clauses: Vec::with_capacity(1024),
        }
    }

    /// Allocates an original clause.
    pub fn alloc_original(&mut self, lits: Vec<Lit>) -> ClauseId {
        let id = ClauseId(self.clauses.len() as u32);
        self.clauses.push(Clause::new_original(lits));
        id
    }

    /// Allocates a learned clause.
    pub fn alloc_learned(&mut self, lits: Vec<Lit>, lbd: u32) -> ClauseId {
        let id = ClauseId(self.clauses.len() as u32);
        self.clauses.push(Clause::new_learned(lits, lbd));
        id
    }

    /// Returns a reference to a clause.
    #[inline]
    pub fn get(&self, id: ClauseId) -> &Clause {
        &self.clauses[id.0 as usize]
    }

    /// Returns a mutable reference to a clause.
    #[inline]
    pub fn get_mut(&mut self, id: ClauseId) -> &mut Clause {
        &mut self.clauses[id.0 as usize]
    }

    /// Returns the total number of allocated clauses (including deleted).
    #[inline]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Returns true if arena is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Iterates over all clause IDs.
    pub fn iter_ids(&self) -> impl Iterator<Item = ClauseId> {
        (0..self.clauses.len() as u32).map(ClauseId)
    }
}
