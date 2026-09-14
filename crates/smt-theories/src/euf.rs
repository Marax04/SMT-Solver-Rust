//! Centralized Equality Engine & Congruence Closure for EUF.

use crate::theory::Theory;
use smt_core::term::{Op, TermArena, TermId};
use smt_sat::Lit;
use std::collections::{HashMap, HashSet, VecDeque};

/// Undo record for backtracking union-find mutations.
#[derive(Debug, Clone)]
enum UndoAction {
    Link {
        child: TermId,
        old_parent: TermId,
        old_rank: u32,
    },
    RemoveProofEdge {
        a: TermId,
        b: TermId,
    },
    AddLookup {
        sig: (String, Vec<TermId>),
        old_val: Option<TermId>,
    },
    AddDisequality,
}

/// Congruence Closure / Equality Engine.
#[derive(Debug, Clone)]
pub struct EufSolver<'a> {
    pub arena: &'a TermArena,
    parent: HashMap<TermId, TermId>,
    rank: HashMap<TermId, u32>,
    /// Proof explanation undirected adjacency list: term -> list of (neighbor, reason).
    proof_adj: HashMap<TermId, Vec<(TermId, Option<Lit>)>>,
    /// Function use-lists: maps representative to terms containing it as an argument.
    use_list: HashMap<TermId, Vec<TermId>>,
    /// Congruence signature table: maps (func_name, canonical_args) to TermId.
    sig_lookup: HashMap<(String, Vec<TermId>), TermId>,
    /// Asserted disequalities: (term_a, term_b, reason_lit).
    disequalities: Vec<(TermId, TermId, Lit)>,
    /// Backtracking undo trail.
    undo_trail: Vec<UndoAction>,
    /// Scope limits for undo trail.
    scopes: Vec<usize>,
}

impl<'a> EufSolver<'a> {
    /// Creates a new EUF solver referencing the term arena.
    pub fn new(arena: &'a TermArena) -> Self {
        Self {
            arena,
            parent: HashMap::with_capacity(512),
            rank: HashMap::with_capacity(512),
            proof_adj: HashMap::with_capacity(512),
            use_list: HashMap::with_capacity(512),
            sig_lookup: HashMap::with_capacity(512),
            disequalities: Vec::with_capacity(128),
            undo_trail: Vec::with_capacity(512),
            scopes: Vec::with_capacity(32),
        }
    }

    /// Finds the canonical representative of a term.
    pub fn find(&self, mut t: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&t) {
            if p == t {
                break;
            }
            t = p;
        }
        t
    }

    /// Registers a term and initializes its signature and use-lists.
    pub fn register_term(&mut self, id: TermId) {
        if self.parent.contains_key(&id) {
            return;
        }
        self.parent.insert(id, id);
        self.rank.insert(id, 0);

        let term = self.arena.get(id);
        if let Op::Apply(func_name) = &term.op {
            for &arg in &term.args {
                self.register_term(arg);
                self.use_list.entry(arg).or_default().push(id);
            }
            let sig = self.compute_sig(func_name, &term.args);
            if let Some(&other_app) = self.sig_lookup.get(&sig) {
                if other_app != id && self.find(other_app) != self.find(id) {
                    self.merge(other_app, id, None);
                }
            } else {
                let old_val = self.sig_lookup.insert(sig.clone(), id);
                self.undo_trail.push(UndoAction::AddLookup { sig, old_val });
            }
        }
    }

    fn compute_sig(&self, func_name: &str, args: &[TermId]) -> (String, Vec<TermId>) {
        let rep_args: Vec<TermId> = args.iter().map(|&a| self.find(a)).collect();
        (func_name.to_string(), rep_args)
    }

    /// Merges equivalence classes of  and  with optional justification literal.
    pub fn merge(&mut self, a: TermId, b: TermId, reason: Option<Lit>) {
        self.register_term(a);
        self.register_term(b);

        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a == root_b {
            return;
        }

        // Add undirected edge to proof graph for explanations
        self.proof_adj.entry(a).or_default().push((b, reason));
        self.proof_adj.entry(b).or_default().push((a, reason));
        self.undo_trail.push(UndoAction::RemoveProofEdge { a, b });

        let rank_a = *self.rank.get(&root_a).unwrap_or(&0);
        let rank_b = *self.rank.get(&root_b).unwrap_or(&0);

        let (parent_node, child_node) = if rank_a >= rank_b {
            (root_a, root_b)
        } else {
            (root_b, root_a)
        };

        let old_parent = *self.parent.get(&child_node).unwrap();
        let old_rank = *self.rank.get(&parent_node).unwrap();

        self.parent.insert(child_node, parent_node);
        if rank_a == rank_b {
            self.rank.insert(parent_node, old_rank + 1);
        }

        self.undo_trail.push(UndoAction::Link {
            child: child_node,
            old_parent,
            old_rank,
        });

        // Update use-lists and propagate induced congruences
        let child_uses = self.use_list.get(&child_node).cloned().unwrap_or_default();
        let mut induced_merges = Vec::new();

        for &app_id in &child_uses {
            let app_term = self.arena.get(app_id);
            if let Op::Apply(func_name) = &app_term.op {
                let sig = self.compute_sig(func_name, &app_term.args);
                if let Some(&other_app) = self.sig_lookup.get(&sig) {
                    if other_app != app_id && self.find(other_app) != self.find(app_id) {
                        induced_merges.push((other_app, app_id));
                    }
                } else {
                    let old_val = self.sig_lookup.insert(sig.clone(), app_id);
                    self.undo_trail.push(UndoAction::AddLookup { sig, old_val });
                }
            }
        }

        // Merge use-list of child into parent
        self.use_list.entry(parent_node).or_default().extend(child_uses);

        // Recursively merge induced congruences
        for (f1, f2) in induced_merges {
            self.merge(f1, f2, None);
        }
    }

    /// Traces path between two terms in the proof graph to produce a conflict explanation clause.
    pub fn explain(&self, start: TermId, target: TermId) -> Vec<Lit> {
        let mut conflict = Vec::new();
        let mut visited_pairs = HashSet::new();
        self.explain_rec(start, target, &mut conflict, &mut visited_pairs);
        conflict.sort();
        conflict.dedup();
        conflict
    }

    fn explain_rec(
        &self,
        start: TermId,
        target: TermId,
        conflict: &mut Vec<Lit>,
        visited_pairs: &mut HashSet<(TermId, TermId)>,
    ) {
        if start == target || visited_pairs.contains(&(start, target)) {
            return;
        }
        visited_pairs.insert((start, target));

        // BFS to find shortest path from start to target in proof_adj
        let mut visited = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(start);
        visited.insert(start, None);

        while let Some(curr) = queue.pop_front() {
            if curr == target {
                break;
            }
            if let Some(neighbors) = self.proof_adj.get(&curr) {
                for &(next, reason) in neighbors {
                    if !visited.contains_key(&next) {
                        visited.insert(next, Some((curr, reason)));
                        queue.push_back(next);
                    }
                }
            }
        }

        let mut curr = target;
        while let Some(Some((prev, reason))) = visited.get(&curr) {
            if let Some(lit) = reason {
                conflict.push(!*lit);
            } else {
                // Congruence between curr and prev
                let term_curr = self.arena.get(curr);
                let term_prev = self.arena.get(*prev);
                if let (Op::Apply(f1), Op::Apply(f2)) = (&term_curr.op, &term_prev.op) {
                    if f1 == f2 && term_curr.args.len() == term_prev.args.len() {
                        for i in 0..term_curr.args.len() {
                            self.explain_rec(term_curr.args[i], term_prev.args[i], conflict, visited_pairs);
                        }
                    }
                }
            }
            curr = *prev;
        }
    }
}

impl<'a> Theory for EufSolver<'a> {
    fn assert_term(&mut self, lit: Lit, term: TermId) {
        let op = self.arena.op_of(term).clone();
        let args = self.arena.args_of(term);
        match op {
            Op::Eq if args.len() == 2 => {
                if lit.is_pos() {
                    self.merge(args[0], args[1], Some(lit));
                } else {
                    self.register_term(args[0]);
                    self.register_term(args[1]);
                    self.disequalities.push((args[0], args[1], lit));
                    self.undo_trail.push(UndoAction::AddDisequality);
                }
            }
            Op::Distinct => {
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        self.register_term(args[i]);
                        self.register_term(args[j]);
                        self.disequalities.push((args[i], args[j], lit));
                        self.undo_trail.push(UndoAction::AddDisequality);
                    }
                }
            }
            _ => {}
        }
    }

    fn check(&mut self) -> Result<(), Vec<Lit>> {
        for &(a, b, diseq_lit) in &self.disequalities {
            if self.find(a) == self.find(b) {
                // Inconsistency: a == b according to union-find, but a != b was asserted!
                let mut conflict = self.explain(a, b);
                conflict.push(!diseq_lit);
                return Err(conflict);
            }
        }
        Ok(())
    }

    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)> {
        Vec::new()
    }

    fn push(&mut self) {
        self.scopes.push(self.undo_trail.len());
    }

    fn pop(&mut self) {
        if let Some(target_len) = self.scopes.pop() {
            while self.undo_trail.len() > target_len {
                match self.undo_trail.pop().unwrap() {
                    UndoAction::Link { child, old_parent, old_rank } => {
                        self.parent.insert(child, old_parent);
                        if let Some(&p) = self.parent.get(&child) {
                            self.rank.insert(p, old_rank);
                        }
                    }
                    UndoAction::RemoveProofEdge { a, b } => {
                        if let Some(edges) = self.proof_adj.get_mut(&a) {
                            if let Some(pos) = edges.iter().rposition(|&(target, _)| target == b) {
                                edges.remove(pos);
                            }
                        }
                        if let Some(edges) = self.proof_adj.get_mut(&b) {
                            if let Some(pos) = edges.iter().rposition(|&(target, _)| target == a) {
                                edges.remove(pos);
                            }
                        }
                    }
                    UndoAction::AddLookup { sig, old_val } => {
                        if let Some(val) = old_val {
                            self.sig_lookup.insert(sig, val);
                        } else {
                            self.sig_lookup.remove(&sig);
                        }
                    }
                    UndoAction::AddDisequality => {
                        self.disequalities.pop();
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.proof_adj.clear();
        self.use_list.clear();
        self.sig_lookup.clear();
        self.disequalities.clear();
        self.undo_trail.clear();
        self.scopes.clear();
    }
}
