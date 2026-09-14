//! VSIDS (Variable State Independent Decaying Sum) branching heuristic.

use crate::lit::Var;
use crate::trail::Trail;

/// VSIDS decision heuristic managing variable activities and priority selection.
#[derive(Debug, Clone)]
pub struct Vsids {
    /// Activity score per variable.
    activity: Vec<f64>,
    /// Activity increment factor.
    var_inc: f64,
    /// Decay factor (typically 0.95).
    var_decay: f64,
    /// Binary heap containing variables prioritized by activity.
    heap: Vec<Var>,
    /// Map from Var to its position in the heap (or usize::MAX if not in heap).
    heap_pos: Vec<usize>,
}

impl Default for Vsids {
    fn default() -> Self {
        Self::new()
    }
}

impl Vsids {
    /// Creates a new VSIDS manager.
    pub fn new() -> Self {
        Self {
            activity: Vec::with_capacity(1024),
            var_inc: 1.0,
            var_decay: 0.95,
            heap: Vec::with_capacity(1024),
            heap_pos: Vec::with_capacity(1024),
        }
    }

    /// Ensures structures can accommodate `var_count` variables.
    pub fn ensure_var(&mut self, var_count: usize) {
        let old_count = self.activity.len();
        if old_count < var_count {
            self.activity.resize(var_count, 0.0);
            self.heap_pos.resize(var_count, usize::MAX);
            for v in old_count..var_count {
                self.insert(Var(v as u32));
            }
        }
    }

    /// Inserts a variable into the heap if it is not already present.
    pub fn insert(&mut self, var: Var) {
        let idx = var.index();
        if self.heap_pos[idx] == usize::MAX {
            let pos = self.heap.len();
            self.heap.push(var);
            self.heap_pos[idx] = pos;
            self.sift_up(pos);
        }
    }

    /// Returns true if the variable is currently in the heap.
    pub fn is_in_heap(&self, var: Var) -> bool {
        let idx = var.index();
        idx < self.heap_pos.len() && self.heap_pos[idx] != usize::MAX
    }

    /// Bumps the activity of a variable involved in a conflict.
    pub fn bump_var(&mut self, var: Var) {
        let idx = var.index();
        self.activity[idx] += self.var_inc;
        if self.activity[idx] > 1e100 {
            // Rescale all activities to avoid floating-point overflow
            for act in &mut self.activity {
                *act *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        let pos = self.heap_pos[idx];
        if pos != usize::MAX {
            self.sift_up(pos);
        }
    }

    /// Decays variable activity by scaling `var_inc`.
    pub fn decay(&mut self) {
        self.var_inc /= self.var_decay;
    }

    /// Selects the next unassigned variable with highest activity score.
    pub fn select_decision_var(&mut self, trail: &Trail) -> Option<Var> {
        while let Some(var) = self.pop_max() {
            if !trail.var_value(var).is_defined() {
                return Some(var);
            }
        }
        for v in 0..self.activity.len() {
            let var = Var(v as u32);
            if !trail.var_value(var).is_defined() {
                self.insert(var);
                return self.pop_max();
            }
        }
        None
    }

    fn pop_max(&mut self) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let max_var = self.heap[0];
        self.heap_pos[max_var.index()] = usize::MAX;

        if self.heap.len() == 1 {
            self.heap.pop();
            return Some(max_var);
        }

        let last = self.heap.pop().unwrap();
        self.heap[0] = last;
        self.heap_pos[last.index()] = 0;
        self.sift_down(0);

        Some(max_var)
    }

    fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            let var_pos = self.heap[pos];
            let var_parent = self.heap[parent];
            if self.activity[var_pos.index()] > self.activity[var_parent.index()] {
                self.heap.swap(pos, parent);
                self.heap_pos[var_pos.index()] = parent;
                self.heap_pos[var_parent.index()] = pos;
                pos = parent;
            } else {
                break;
            }
        }
    }

    fn sift_down(&mut self, mut pos: usize) {
        let len = self.heap.len();
        while (2 * pos + 1) < len {
            let mut best = pos;
            let left = 2 * pos + 1;
            let right = left + 1;

            if self.activity[self.heap[left].index()] > self.activity[self.heap[best].index()] {
                best = left;
            }
            if right < len
                && self.activity[self.heap[right].index()] > self.activity[self.heap[best].index()]
            {
                best = right;
            }

            if best != pos {
                let var_pos = self.heap[pos];
                let var_best = self.heap[best];
                self.heap.swap(pos, best);
                self.heap_pos[var_pos.index()] = best;
                self.heap_pos[var_best.index()] = pos;
                pos = best;
            } else {
                break;
            }
        }
    }
}
