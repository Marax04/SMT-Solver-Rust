//! CDCL SAT Solver Core with 2-Watched Literals, 1-UIP, Restarts, and Theory Interfacing.

use crate::clause::{ClauseArena, ClauseId};
use crate::drat::DratProof;
use crate::lit::{LBool, Lit, Var};
use crate::restart::RestartStrategy;
use crate::theory::{NoOpTheory, TheoryCallback};
use crate::trail::{Reason, Trail};
use crate::vsids::Vsids;
use crate::watch::{WatchList, Watcher};
use std::collections::HashSet;

/// Solver statistics.
#[derive(Debug, Clone, Default)]
pub struct SolverStats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub restarts: u64,
    pub clauses_learned: u64,
    pub clauses_deleted: u64,
}

/// Scope checkpoint for incremental solving push/pop.
#[derive(Debug, Clone)]
struct Scope {
    clause_count: usize,
}

/// The core CDCL Boolean SAT Solver.
#[derive(Debug, Clone)]
pub struct SatSolver {
    pub arena: ClauseArena,
    pub watches: WatchList,
    pub trail: Trail,
    pub vsids: Vsids,
    pub restarts: RestartStrategy,
    pub proof: DratProof,
    pub stats: SolverStats,
    pub ok: bool,
    num_vars: usize,
    max_learned: usize,
    pub max_conflicts: Option<u64>,
    pub max_propagations: Option<u64>,
    scopes: Vec<Scope>,
    model: Vec<LBool>,
}

impl Default for SatSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolver {
    /// Creates a new SAT solver instance.
    /// Creates a new CDCL SAT solver instance.
    ///
    /// # Example
    /// ```rust
    /// use smt_sat::SatSolver;
    /// let solver = SatSolver::new();
    /// assert_eq!(solver.num_vars(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            arena: ClauseArena::new(),
            watches: WatchList::new(),
            trail: Trail::new(),
            vsids: Vsids::new(),
            restarts: RestartStrategy::new(),
            proof: DratProof::new(false),
            stats: SolverStats::default(),
            ok: true,
            num_vars: 0,
            max_learned: 4000,
            max_conflicts: None,
            max_propagations: None,
            scopes: Vec::new(),
            model: Vec::new(),
        }
    }

    /// Enables DRAT proof generation.
    pub fn enable_drat(&mut self, enable: bool) {
        self.proof = DratProof::new(enable);
    }

    /// Allocates a new variable in the solver.
    pub fn new_var(&mut self) -> Var {
        let v = Var(self.num_vars as u32);
        self.num_vars += 1;
        self.watches.ensure_var(self.num_vars);
        self.trail.ensure_var(self.num_vars);
        self.vsids.ensure_var(self.num_vars);
        v
    }

    /// Returns the total number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Adds an original clause to the solver.
    pub fn add_clause(&mut self, mut lits: Vec<Lit>) -> bool {
        if !self.ok {
            return false;
        }

        assert_eq!(
            self.trail.decision_level(),
            0,
            "Clauses must be added at level 0"
        );

        for &lit in &lits {
            while lit.var().index() >= self.num_vars {
                self.new_var();
            }
        }

        // Clean clause: remove False literals, check for True literals or tautologies
        lits.sort_by_key(|l| l.0);
        lits.dedup();

        let mut cleaned = Vec::with_capacity(lits.len());
        for &lit in &lits {
            let val = self.trail.lit_value(lit);
            if val.is_true() {
                // Clause is satisfied at level 0, discard
                return true;
            }
            if val.is_false() {
                // Falsified literal at level 0 can never satisfy clause
                continue;
            }
            // Check for complementary literal (tautology: x or !x)
            if cleaned.iter().any(|&c: &Lit| c == !lit) {
                return true;
            }
            cleaned.push(lit);
        }

        if cleaned.is_empty() {
            // Empty clause at level 0 => UNSAT
            self.proof.add_clause(&[]);
            self.ok = false;
            return false;
        }

        if cleaned.len() == 1 {
            // Unit clause at level 0
            let unit = cleaned[0];
            self.trail.assign(unit, Reason::Unit);
            if self.bcp().is_err() {
                self.proof.add_clause(&[]);
                self.ok = false;
                return false;
            }
            return true;
        }

        let cid = self.arena.alloc_original(cleaned);
        let c = self.arena.get(cid);
        let lit0 = c[0];
        let lit1 = c[1];
        self.watches.add(!lit0, Watcher::new(cid, lit1));
        self.watches.add(!lit1, Watcher::new(cid, lit0));

        true
    }

    /// Adds a learned clause during conflict analysis.
    fn add_learned_clause(&mut self, lits: Vec<Lit>, lbd: u32) -> ClauseId {
        self.proof.add_clause(&lits);
        let cid = self.arena.alloc_learned(lits, lbd);
        let c = self.arena.get(cid);
        let lit0 = c[0];
        let lit1 = c[1];
        self.watches.add(!lit0, Watcher::new(cid, lit1));
        self.watches.add(!lit1, Watcher::new(cid, lit0));
        self.stats.clauses_learned += 1;
        cid
    }

    /// Boolean Constraint Propagation (2-Watched Literals).
    pub fn bcp(&mut self) -> Result<(), ClauseId> {
        while let Some(p) = self.trail.next_unpropagated() {
            self.stats.propagations += 1;

            let watchers = std::mem::take(self.watches.get_mut(p));
            let mut keep_watchers = Vec::with_capacity(watchers.len());

            let mut conflict: Option<ClauseId> = None;
            let false_lit = !p;

            for (w_idx, w) in watchers.iter().enumerate() {
                if conflict.is_some() {
                    keep_watchers.push(*w);
                    continue;
                }

                if self.arena.get(w.clause).deleted {
                    continue;
                }

                // Blocker inspection optimization
                if self.trail.lit_value(w.blocker).is_true() {
                    keep_watchers.push(*w);
                    continue;
                }

                // Inspect clause
                let clause = self.arena.get_mut(w.clause);

                // Make sure false_lit is at clause[1]
                if clause[0] == false_lit {
                    clause[0] = clause[1];
                    clause[1] = false_lit;
                }

                let first_lit = clause[0];
                if self.trail.lit_value(first_lit).is_true() {
                    // Already satisfied
                    keep_watchers.push(Watcher::new(w.clause, first_lit));
                    continue;
                }

                // Search for a new literal to watch starting at index 2
                let mut found_new_watch = false;
                for i in 2..clause.len() {
                    let cand = clause[i];
                    if !self.trail.lit_value(cand).is_false() {
                        // Swap with clause[1]
                        clause[1] = cand;
                        clause[i] = false_lit;
                        self.watches.add(!cand, Watcher::new(w.clause, first_lit));
                        found_new_watch = true;
                        break;
                    }
                }

                if found_new_watch {
                    continue;
                }

                // No other literal can be watched; clause is either unit or conflicting
                keep_watchers.push(Watcher::new(w.clause, first_lit));

                let first_val = self.trail.lit_value(first_lit);
                if first_val.is_false() {
                    // Conflict found
                    conflict = Some(w.clause);
                    // Retain all remaining watchers
                    for remaining in &watchers[w_idx + 1..] {
                        keep_watchers.push(*remaining);
                    }
                    break;
                } else if !first_val.is_defined() {
                    // Unit propagation
                    self.trail.assign(first_lit, Reason::Clause(w.clause));
                }
            }

            *self.watches.get_mut(p) = keep_watchers;

            if let Some(conf_cid) = conflict {
                return Err(conf_cid);
            }
        }
        Ok(())
    }

    /// 1-UIP Conflict Analysis.
    fn analyze_conflict(&mut self, conflict_cid: ClauseId) -> (Vec<Lit>, u32, u32) {
        self.stats.conflicts += 1;
        let mut learned: Vec<Lit> = Vec::new();
        // Reserve slot 0 for 1-UIP literal
        learned.push(Lit(0));

        let current_level = self.trail.decision_level();
        let mut seen = vec![false; self.num_vars];
        let mut path_count = 0;
        let mut backtrack_level = 0;

        let mut current_lits: Vec<Lit> = self.arena.get(conflict_cid).lits.clone();
        let mut trail_idx = self.trail.trail.len();

        loop {
            for lit in current_lits {
                let var = lit.var();
                if !seen[var.index()] {
                    seen[var.index()] = true;
                    self.vsids.bump_var(var);

                    let lvl = self.trail.level_of(var);
                    if lvl == current_level {
                        path_count += 1;
                    } else if lvl > 0 {
                        learned.push(lit);
                        if lvl > backtrack_level {
                            backtrack_level = lvl;
                        }
                    }
                }
            }

            // Find next literal on trail at current decision level
            let mut next_lit = None;
            while trail_idx > 0 {
                trail_idx -= 1;
                let lit = self.trail.trail[trail_idx];
                if seen[lit.var().index()] {
                    next_lit = Some(lit);
                    break;
                }
            }

            let lit = match next_lit {
                Some(l) => l,
                None => break,
            };

            let var = lit.var();
            seen[var.index()] = false;
            path_count -= 1;

            if path_count == 0 {
                // 1-UIP found! The asserting literal must evaluate to true, so it is !lit
                learned[0] = !lit;
                break;
            }

            match self.trail.reason_of(var) {
                Reason::Clause(cid) => {
                    current_lits = self
                        .arena
                        .get(cid)
                        .lits
                        .iter()
                        .copied()
                        .filter(|&l| l.var() != var)
                        .collect();
                }
                _ => {
                    break;
                }
            }
        }

        // Compute LBD (Literal Block Distance)
        let mut levels = HashSet::new();
        for &lit in &learned {
            levels.insert(self.trail.level_of(lit.var()));
        }
        let lbd = levels.len().max(1) as u32;

        self.vsids.decay();

        (learned, backtrack_level, lbd)
    }

    /// Clause database management: evicts redundant learned clauses.
    fn reduce_db(&mut self) {
        let mut learned_cids: Vec<ClauseId> = Vec::new();
        for id in self.arena.iter_ids() {
            let c = self.arena.get(id);
            if c.learned && !c.deleted && c.len() > 2 {
                learned_cids.push(id);
            }
        }

        if learned_cids.len() < self.max_learned {
            return;
        }

        // Sort by LBD descending and activity ascending
        learned_cids.sort_by(|&a, &b| {
            let ca = self.arena.get(a);
            let cb = self.arena.get(b);
            cb.lbd.cmp(&ca.lbd).then_with(|| {
                ca.activity
                    .partial_cmp(&cb.activity)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
        });

        let to_remove = learned_cids.len() / 2;
        let mut removed = 0;

        for &cid in &learned_cids {
            if removed >= to_remove {
                break;
            }
            let c = self.arena.get(cid);
            // Protect high quality clauses (LBD <= 2) and current reasons on trail
            if c.lbd <= 2 {
                continue;
            }

            let first_lit = c[0];
            if self.trail.var_value(first_lit.var()).is_defined()
                && self.trail.reason_of(first_lit.var()) == Reason::Clause(cid)
            {
                continue;
            }

            self.proof.delete_clause(&c.lits);
            self.arena.get_mut(cid).deleted = true;
            removed += 1;
            self.stats.clauses_deleted += 1;
        }

        self.max_learned += 500;
    }

    /// Solves the SAT formula without theories.
    pub fn solve(&mut self) -> LBool {
        let mut noop = NoOpTheory;
        self.solve_with_theory(&mut noop, &[])
    }

    /// Solves under temporary assumptions.
    pub fn solve_with_assumptions(&mut self, assumptions: &[Lit]) -> LBool {
        let mut noop = NoOpTheory;
        self.solve_with_theory(&mut noop, assumptions)
    }

    fn backtrack_to(&mut self, level: u32) {
        let vsids = &mut self.vsids;
        self.trail.backtrack_to_with(level, |v| vsids.insert(v));
    }

    /// Core CDCL(T) solving algorithm with theory callback integration.
    pub fn solve_with_theory<T: TheoryCallback>(
        &mut self,
        theory: &mut T,
        assumptions: &[Lit],
    ) -> LBool {
        if !self.ok {
            return LBool::False;
        }

        self.backtrack_to(0);

        if self.bcp().is_err() {
            self.ok = false;
            return LBool::False;
        }

        for &lit in &self.trail.trail {
            theory.assert_lit(lit);
        }

        let is_assumption_run = !assumptions.is_empty();
        if is_assumption_run {
            self.push();
        }

        let res = self.solve_internal(theory, assumptions, is_assumption_run);

        if res == LBool::True {
            self.model = (0..self.num_vars)
                .map(|v| self.trail.var_value(Var(v as u32)))
                .collect();
        } else {
            self.model.clear();
        }

        if is_assumption_run {
            self.pop();
        } else {
            self.backtrack_to(0);
        }

        res
    }

    fn solve_internal<T: TheoryCallback>(
        &mut self,
        theory: &mut T,
        assumptions: &[Lit],
        is_assumption_run: bool,
    ) -> LBool {
        let mut current_assumption_idx = 0;

        loop {
            if let Some(max_c) = self.max_conflicts {
                if self.stats.conflicts >= max_c {
                    return LBool::Undef;
                }
            }
            if let Some(max_p) = self.max_propagations {
                if self.stats.propagations >= max_p {
                    return LBool::Undef;
                }
            }

            let old_trail_len = self.trail.trail.len();

            // 1. Boolean unit propagation
            match self.bcp() {
                Err(conflict_cid) => {
                    if self.trail.decision_level() == 0 {
                        self.proof.add_clause(&[]);
                        if !is_assumption_run {
                            self.ok = false;
                        }
                        return LBool::False;
                    }

                    let (learned_lits, backtrack_level, lbd) = self.analyze_conflict(conflict_cid);
                    if is_assumption_run && backtrack_level < assumptions.len() as u32 {
                        return LBool::False;
                    }
                    while self.trail.decision_level() > backtrack_level {
                        self.backtrack_to(self.trail.decision_level() - 1);
                        theory.pop();
                    }

                    if self.restarts.record_conflict(lbd) {
                        while self.trail.decision_level() > 0 {
                            self.backtrack_to(self.trail.decision_level() - 1);
                            theory.pop();
                        }
                    }

                    self.reduce_db();

                    if learned_lits.len() == 1 {
                        self.proof.add_clause(&learned_lits);
                        self.trail.assign(learned_lits[0], Reason::Unit);
                        theory.assert_lit(learned_lits[0]);
                    } else {
                        let learned_cid = self.add_learned_clause(learned_lits.clone(), lbd);
                        self.trail
                            .assign(learned_lits[0], Reason::Clause(learned_cid));
                        theory.assert_lit(learned_lits[0]);
                    }
                    continue;
                }
                Ok(()) => {
                    for &lit in &self.trail.trail[old_trail_len..] {
                        theory.assert_lit(lit);
                    }
                }
            }

            // 2. Theory checking & propagation
            if let Err(theory_conflict_lits) = theory.check() {
                if self.trail.decision_level() == 0 {
                    if !is_assumption_run {
                        self.ok = false;
                    }
                    return LBool::False;
                }
                let cid = self.arena.alloc_learned(theory_conflict_lits, 2);
                let (learned_lits, backtrack_level, lbd) = self.analyze_conflict(cid);
                if is_assumption_run && backtrack_level < assumptions.len() as u32 {
                    return LBool::False;
                }
                while self.trail.decision_level() > backtrack_level {
                    self.backtrack_to(self.trail.decision_level() - 1);
                    theory.pop();
                }

                if learned_lits.len() == 1 {
                    self.trail.assign(learned_lits[0], Reason::Unit);
                    theory.assert_lit(learned_lits[0]);
                } else {
                    let learned_cid = self.add_learned_clause(learned_lits.clone(), lbd);
                    self.trail
                        .assign(learned_lits[0], Reason::Clause(learned_cid));
                    theory.assert_lit(learned_lits[0]);
                }
                continue;
            }

            // 3. Theory-driven propagations
            let theory_props = theory.propagate();
            for (prop_lit, reason_lits) in theory_props {
                if !self.trail.lit_value(prop_lit).is_defined() {
                    let mut clause_lits = reason_lits;
                    clause_lits.push(prop_lit);
                    let cid = self.arena.alloc_learned(clause_lits, 2);
                    self.trail.assign(prop_lit, Reason::Clause(cid));
                    theory.assert_lit(prop_lit);
                }
            }

            // 4. Decision phase (Assumptions first, then VSIDS)
            if current_assumption_idx < assumptions.len() {
                let p = assumptions[current_assumption_idx];
                current_assumption_idx += 1;
                let val = self.trail.lit_value(p);
                if val.is_false() {
                    // Contradictory assumption => UNSAT under assumptions
                    return LBool::False;
                } else if val.is_true() {
                    // Already true, continue to next assumption
                    continue;
                } else {
                    self.trail.new_decision_level();
                    theory.push();
                    self.trail.assign(p, Reason::Decision);
                    theory.assert_lit(p);
                    self.stats.decisions += 1;
                    continue;
                }
            }

            // VSIDS decision variable selection
            match self.vsids.select_decision_var(&self.trail) {
                Some(next_var) => {
                    self.trail.new_decision_level();
                    theory.push();
                    // Phase saving: reuse previous polarity
                    let phase = self.trail.saved_phase(next_var);
                    let lit = Lit::new(next_var, phase);
                    self.trail.assign(lit, Reason::Decision);
                    theory.assert_lit(lit);
                    self.stats.decisions += 1;
                }
                None => {
                    // All variables assigned with no conflicts -> SAT!
                    return LBool::True;
                }
            }
        }
    }

    /// Queries the model value of a variable.
    pub fn model_value(&self, var: Var) -> LBool {
        self.model.get(var.index()).copied().unwrap_or(LBool::Undef)
    }

    /// Queries the model value of a literal taking polarity into account.
    pub fn model_lit(&self, lit: Lit) -> LBool {
        let v_val = self.model_value(lit.var());
        if lit.is_pos() {
            v_val
        } else {
            !v_val
        }
    }

    /// Pushes an incremental solver scope.
    pub fn push(&mut self) {
        self.scopes.push(Scope {
            clause_count: self.arena.len(),
        });
    }

    /// Pops the top incremental scope.
    pub fn pop(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            self.backtrack_to(0);
            self.max_learned = 4000;
            // Mark newer clauses as deleted
            for id in scope.clause_count..self.arena.len() {
                self.arena.get_mut(ClauseId(id as u32)).deleted = true;
            }
        }
    }
}
