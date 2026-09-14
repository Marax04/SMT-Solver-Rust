//! Assignment trail, decision levels, and propagation queues.

use crate::clause::ClauseId;
use crate::lit::{LBool, Lit, Var};

/// Reason why a literal was assigned on the trail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// Decision made by branching heuristic.
    Decision,
    /// Top-level unit clause or assumption.
    Unit,
    /// Implication deduced from clause unit propagation.
    Clause(ClauseId),
    /// Implication deduced by a theory solver.
    Theory(u32),
}

/// Metadata stored per variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VarData {
    /// Decision level at which this variable was assigned.
    pub level: u32,
    /// Explanation/reason for assignment.
    pub reason: Reason,
}

/// The trail data structure managing variable assignments, decision levels, and phase saving.
#[derive(Debug, Clone)]
pub struct Trail {
    /// Current assignment state of each variable.
    assigns: Vec<LBool>,
    /// Per-variable level and reason.
    var_data: Vec<VarData>,
    /// Saved polarity for phase saving heuristic.
    phase: Vec<bool>,
    /// Chronological list of assigned literals.
    pub trail: Vec<Lit>,
    /// Limits marking the beginning of each decision level in the trail.
    pub trail_lim: Vec<usize>,
    /// Queue head for Boolean Constraint Propagation (BCP).
    pub qhead: usize,
}

impl Default for Trail {
    fn default() -> Self {
        Self::new()
    }
}

impl Trail {
    /// Creates a new empty trail.
    pub fn new() -> Self {
        Self {
            assigns: Vec::with_capacity(1024),
            var_data: Vec::with_capacity(1024),
            phase: Vec::with_capacity(1024),
            trail: Vec::with_capacity(1024),
            trail_lim: Vec::with_capacity(64),
            qhead: 0,
        }
    }

    /// Ensures structures have allocated capacity for `var_count` variables.
    pub fn ensure_var(&mut self, var_count: usize) {
        if self.assigns.len() < var_count {
            self.assigns.resize(var_count, LBool::Undef);
            self.var_data.resize(
                var_count,
                VarData {
                    level: 0,
                    reason: Reason::Unit,
                },
            );
            self.phase.resize(var_count, false);
        }
    }

    /// Returns the current decision level.
    #[inline]
    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// Value of a variable.
    #[inline]
    pub fn var_value(&self, var: Var) -> LBool {
        self.assigns[var.index()]
    }

    /// Returns true if the variable is assigned.
    #[inline]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.var_value(var).is_defined()
    }

    /// Value of a literal.
    #[inline]
    pub fn lit_value(&self, lit: Lit) -> LBool {
        let val = self.var_value(lit.var());
        if lit.is_pos() {
            val
        } else {
            !val
        }
    }

    /// Decision level at which variable was assigned.
    #[inline]
    pub fn level_of(&self, var: Var) -> u32 {
        self.var_data[var.index()].level
    }

    /// Reason why variable was assigned.
    #[inline]
    pub fn reason_of(&self, var: Var) -> Reason {
        self.var_data[var.index()].reason
    }

    /// Saved phase (last polarity assigned).
    #[inline]
    pub fn saved_phase(&self, var: Var) -> bool {
        self.phase[var.index()]
    }

    /// Starts a new decision level.
    pub fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    /// Assigns a literal with reason and decision level.
    pub fn assign(&mut self, lit: Lit, reason: Reason) {
        let var = lit.var();
        let idx = var.index();
        assert_eq!(self.assigns[idx], LBool::Undef, "Variable already assigned");

        self.assigns[idx] = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };
        self.phase[idx] = lit.is_neg();
        self.var_data[idx] = VarData {
            level: self.decision_level(),
            reason,
        };
        self.trail.push(lit);
    }

    /// Backtracks to the specified decision level, notifying `on_unassign` of each unassigned variable.
    pub fn backtrack_to_with<F: FnMut(Var)>(&mut self, level: u32, mut on_unassign: F) {
        if self.decision_level() > level {
            let target_len = self.trail_lim[level as usize];
            while self.trail.len() > target_len {
                let lit = self.trail.pop().unwrap();
                let var = lit.var();
                self.assigns[var.index()] = LBool::Undef;
                on_unassign(var);
            }
            self.qhead = target_len;
            self.trail_lim.truncate(level as usize);
        }
    }

    /// Backtracks to the specified decision level.
    pub fn backtrack_to(&mut self, level: u32) {
        self.backtrack_to_with(level, |_| {});
    }

    /// Pops the next unpropagated literal from the queue.
    #[inline]
    pub fn next_unpropagated(&mut self) -> Option<Lit> {
        if self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            Some(lit)
        } else {
            None
        }
    }

    /// True if there are literals waiting to be propagated.
    #[inline]
    pub fn has_unpropagated(&self) -> bool {
        self.qhead < self.trail.len()
    }
}
