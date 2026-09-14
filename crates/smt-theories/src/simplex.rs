//! Dutertre-de Moura Incremental Dual Simplex Solver for LRA and LIA.

use crate::theory::Theory;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smt_core::term::{Op, TermArena, TermId};
use smt_sat::Lit;
use std::cmp::Ordering;
use std::collections::HashMap;

/// An infinitesimal-extended rational number: `c + k * delta`, with delta > 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeltaRational {
    pub c: BigRational,
    pub k: BigRational,
}

impl DeltaRational {
    pub fn new(c: BigRational, k: BigRational) -> Self {
        Self { c, k }
    }

    pub fn from_rational(c: BigRational) -> Self {
        Self {
            c,
            k: BigRational::zero(),
        }
    }

    pub fn zero() -> Self {
        Self::from_rational(BigRational::zero())
    }
}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.c.cmp(&other.c) {
            Ordering::Equal => self.k.cmp(&other.k),
            other_ord => other_ord,
        }
    }
}

impl std::ops::Add for &DeltaRational {
    type Output = DeltaRational;

    fn add(self, other: Self) -> DeltaRational {
        DeltaRational {
            c: &self.c + &other.c,
            k: &self.k + &other.k,
        }
    }
}

impl std::ops::Sub for &DeltaRational {
    type Output = DeltaRational;

    fn sub(self, other: Self) -> DeltaRational {
        DeltaRational {
            c: &self.c - &other.c,
            k: &self.k - &other.k,
        }
    }
}

impl std::ops::Mul<&BigRational> for &DeltaRational {
    type Output = DeltaRational;

    fn mul(self, scalar: &BigRational) -> DeltaRational {
        DeltaRational {
            c: &self.c * scalar,
            k: &self.k * scalar,
        }
    }
}

/// Variable index inside the Simplex tableau.
pub type SimplexVar = usize;

/// Bound record holding value and its assertion reason.
#[derive(Debug, Clone)]
pub struct Bound {
    pub value: DeltaRational,
    pub reason: Option<Lit>,
}

/// Undo history for simplex backtracking.
#[derive(Debug, Clone)]
enum SimplexUndo {
    SetLowerBound {
        var: SimplexVar,
        old: Option<Bound>,
    },
    SetUpperBound {
        var: SimplexVar,
        old: Option<Bound>,
    },
}

/// Dutertre-de Moura Simplex Tableau for Linear Real/Integer Arithmetic.
#[derive(Debug, Clone)]
pub struct SimplexSolver<'a> {
    pub arena: &'a TermArena,
    /// Mapping from TermId to SimplexVar.
    term_to_var: HashMap<TermId, SimplexVar>,
    var_to_term: Vec<TermId>,
    /// Whether variable is integer-sorted.
    pub is_integer: Vec<bool>,
    /// Basic variables set.
    is_basic: Vec<bool>,
    /// Tableau rows: matrix[basic_var] = map of (non_basic_var -> coeff).
    /// Represents: basic_var = sum_{j in non_basic} coeff * j.
    tableau: Vec<HashMap<SimplexVar, BigRational>>,
    /// Current variable assignments.
    assignment: Vec<DeltaRational>,
    /// Lower bounds.
    lower_bounds: Vec<Option<Bound>>,
    /// Upper bounds.
    upper_bounds: Vec<Option<Bound>>,
    /// Undo history stack.
    undo_stack: Vec<SimplexUndo>,
    scopes: Vec<usize>,
}

impl<'a> SimplexSolver<'a> {
    /// Creates a new Simplex solver.
    pub fn new(arena: &'a TermArena) -> Self {
        Self {
            arena,
            term_to_var: HashMap::with_capacity(256),
            var_to_term: Vec::with_capacity(256),
            is_integer: Vec::with_capacity(256),
            is_basic: Vec::with_capacity(256),
            tableau: Vec::with_capacity(256),
            assignment: Vec::with_capacity(256),
            lower_bounds: Vec::with_capacity(256),
            upper_bounds: Vec::with_capacity(256),
            undo_stack: Vec::with_capacity(512),
            scopes: Vec::with_capacity(32),
        }
    }

    /// Allocates or retrieves the Simplex variable corresponding to an arithmetic term.
    pub fn get_or_create_var(&mut self, term: TermId, is_int: bool) -> SimplexVar {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }
        let var = self.var_to_term.len();
        self.term_to_var.insert(term, var);
        self.var_to_term.push(term);
        self.is_integer.push(is_int);
        self.is_basic.push(false);
        self.tableau.push(HashMap::new());
        self.assignment.push(DeltaRational::zero());
        self.lower_bounds.push(None);
        self.upper_bounds.push(None);
        var
    }

    /// Allocates a new slack variable representing `slack = sum c_j * x_j`.
    pub fn create_slack_var(&mut self, row: HashMap<SimplexVar, BigRational>) -> SimplexVar {
        let var = self.var_to_term.len();
        self.var_to_term.push(self.arena.false_id);
        self.is_integer.push(false);
        self.is_basic.push(true);
        self.tableau.push(row);
        self.assignment.push(DeltaRational::zero());
        self.lower_bounds.push(None);
        self.upper_bounds.push(None);
        var
    }

    /// Checks if the current bounds entail vi == vj.
    pub fn is_equal_entailed(&self, vi: SimplexVar, vj: SimplexVar) -> bool {
        if vi == vj {
            return true;
        }
        // 1. Both fixed to identical constant bounds
        if let (Some(lbi), Some(ubi)) = (&self.lower_bounds[vi], &self.upper_bounds[vi]) {
            if lbi.value == ubi.value {
                if let (Some(lbj), Some(ubj)) = (&self.lower_bounds[vj], &self.upper_bounds[vj]) {
                    if lbj.value == ubj.value && lbi.value == lbj.value {
                        return true;
                    }
                }
            }
        }

        // 2. A slack variable s = vi - vj has lb >= 0 and ub <= 0, or paired slacks vi <= vj && vj <= vi
        let mut u_le_v = false;
        let mut v_le_u = false;

        for (r, row) in self.tableau.iter().enumerate() {
            if self.is_basic[r] && row.len() == 2 {
                let c_i = row.get(&vi);
                let c_j = row.get(&vj);
                if let (Some(ci), Some(cj)) = (c_i, c_j) {
                    if ci == &BigRational::one() && cj == &-BigRational::one() {
                        // row represents: s = vi - vj
                        if let (Some(lb), Some(ub)) = (&self.lower_bounds[r], &self.upper_bounds[r]) {
                            if lb.value >= DeltaRational::zero() && ub.value <= DeltaRational::zero() {
                                return true;
                            }
                        }
                        if let Some(ub) = &self.upper_bounds[r] {
                            if ub.value <= DeltaRational::zero() {
                                u_le_v = true;
                            }
                        }
                        if let Some(lb) = &self.lower_bounds[r] {
                            if lb.value >= DeltaRational::zero() {
                                v_le_u = true;
                            }
                        }
                    } else if ci == &-BigRational::one() && cj == &BigRational::one() {
                        // row represents: s = vj - vi
                        if let (Some(lb), Some(ub)) = (&self.lower_bounds[r], &self.upper_bounds[r]) {
                            if lb.value >= DeltaRational::zero() && ub.value <= DeltaRational::zero() {
                                return true;
                            }
                        }
                        if let Some(ub) = &self.upper_bounds[r] {
                            if ub.value <= DeltaRational::zero() {
                                v_le_u = true;
                            }
                        }
                        if let Some(lb) = &self.lower_bounds[r] {
                            if lb.value >= DeltaRational::zero() {
                                u_le_v = true;
                            }
                        }
                    }
                }
            }
        }

        if u_le_v && v_le_u {
            return true;
        }

        false
    }

    /// Sets a lower bound on a variable.
    pub fn set_lower_bound(&mut self, var: SimplexVar, bound: Bound) {
        let old = self.lower_bounds[var].clone();
        let should_update = match &old {
            Some(existing) => bound.value > existing.value,
            None => true,
        };
        if should_update {
            self.undo_stack.push(SimplexUndo::SetLowerBound { var, old });
            self.lower_bounds[var] = Some(bound);
        }
    }

    /// Sets an upper bound on a variable.
    pub fn set_upper_bound(&mut self, var: SimplexVar, bound: Bound) {
        let old = self.upper_bounds[var].clone();
        let should_update = match &old {
            Some(existing) => bound.value < existing.value,
            None => true,
        };
        if should_update {
            self.undo_stack.push(SimplexUndo::SetUpperBound { var, old });
            self.upper_bounds[var] = Some(bound);
        }
    }

    /// Performs Dutertre-de Moura pivoting step between basic variable `xi` and non-basic `xj`.
    pub fn pivot(&mut self, xi: SimplexVar, xj: SimplexVar) {
        let a_ij = self.tableau[xi].remove(&xj).unwrap();
        let inv_a_ij = BigRational::one() / &a_ij;

        // Express xj in terms of xi and other non-basics:
        // xj = (1 / a_ij) * xi - sum_{k != j} (a_ik / a_ij) * xk
        let mut new_row = HashMap::new();
        new_row.insert(xi, inv_a_ij.clone());

        for (xk, a_ik) in self.tableau[xi].drain() {
            let coeff = -&a_ik * &inv_a_ij;
            new_row.insert(xk, coeff);
        }

        // Substitute xj into all other basic rows
        for r in 0..self.tableau.len() {
            if r != xi && self.is_basic[r] {
                if let Some(a_rj) = self.tableau[r].remove(&xj) {
                    for (&col, coeff) in &new_row {
                        let existing = self.tableau[r].entry(col).or_insert_with(BigRational::zero);
                        *existing = &*existing + (&a_rj * coeff);
                        if existing.is_zero() {
                            self.tableau[r].remove(&col);
                        }
                    }
                }
            }
        }

        self.tableau[xj] = new_row;
        self.is_basic[xi] = false;
        self.is_basic[xj] = true;

        // Recompute basic variable values
        self.update_basic_assignments();
    }

    fn update_basic_assignments(&mut self) {
        for i in 0..self.tableau.len() {
            if self.is_basic[i] {
                let mut sum = DeltaRational::zero();
                for (&j, coeff) in &self.tableau[i] {
                    sum = &sum + &(&self.assignment[j] * coeff);
                }
                self.assignment[i] = sum;
            }
        }
    }

    /// Checks tableau consistency and performs dual simplex pivoting to restore feasibility.
    pub fn solve_simplex(&mut self) -> Result<(), Vec<Lit>> {
        // 1. Direct contradiction check: lower_bound > upper_bound on any variable
        for i in 0..self.tableau.len() {
            if let (Some(lb), Some(ub)) = (&self.lower_bounds[i], &self.upper_bounds[i]) {
                if lb.value > ub.value {
                    let mut conflict = Vec::new();
                    if let Some(lit) = lb.reason {
                        conflict.push(!lit);
                    }
                    if let Some(lit) = ub.reason {
                        conflict.push(!lit);
                    }
                    return Err(conflict);
                }
            }
        }

        // 2. Adjust non-basic variables that violate bounds
        for j in 0..self.tableau.len() {
            if !self.is_basic[j] {
                if let Some(lb) = &self.lower_bounds[j] {
                    if self.assignment[j] < lb.value {
                        self.assignment[j] = lb.value.clone();
                    }
                }
                if let Some(ub) = &self.upper_bounds[j] {
                    if self.assignment[j] > ub.value {
                        self.assignment[j] = ub.value.clone();
                    }
                }
            }
        }

        self.update_basic_assignments();

        let mut iterations = 0;
        let max_iterations = 10000;

        loop {
            iterations += 1;
            if iterations > max_iterations {
                break;
            }

            // Find a basic variable violating bounds
            let mut violating: Option<(SimplexVar, bool)> = None;
            for i in 0..self.tableau.len() {
                if !self.is_basic[i] {
                    continue;
                }
                if let Some(lb) = &self.lower_bounds[i] {
                    if self.assignment[i] < lb.value {
                        violating = Some((i, false));
                        break;
                    }
                }
                if let Some(ub) = &self.upper_bounds[i] {
                    if self.assignment[i] > ub.value {
                        violating = Some((i, true));
                        break;
                    }
                }
            }

            let (xi, is_above_upper) = match violating {
                Some(v) => v,
                None => return Ok(()), // All bounds satisfied
            };

            // Find suitable non-basic variable to pivot
            let mut pivot_cand: Option<SimplexVar> = None;

            for (&xj, a_ij) in &self.tableau[xi] {
                if !is_above_upper {
                    // xi < lb: need to increase xi
                    // xj with a_ij > 0 and xj < ub, or a_ij < 0 and xj > lb
                    if a_ij.is_positive() {
                        if let Some(ub) = &self.upper_bounds[xj] {
                            if self.assignment[xj] < ub.value {
                                pivot_cand = Some(xj);
                                break;
                            }
                        } else {
                            pivot_cand = Some(xj);
                            break;
                        }
                    } else if a_ij.is_negative() {
                        if let Some(lb) = &self.lower_bounds[xj] {
                            if self.assignment[xj] > lb.value {
                                pivot_cand = Some(xj);
                                break;
                            }
                        } else {
                            pivot_cand = Some(xj);
                            break;
                        }
                    }
                } else {
                    // xi > ub: need to decrease xi
                    if a_ij.is_positive() {
                        if let Some(lb) = &self.lower_bounds[xj] {
                            if self.assignment[xj] > lb.value {
                                pivot_cand = Some(xj);
                                break;
                            }
                        } else {
                            pivot_cand = Some(xj);
                            break;
                        }
                    } else if a_ij.is_negative() {
                        if let Some(ub) = &self.upper_bounds[xj] {
                            if self.assignment[xj] < ub.value {
                                pivot_cand = Some(xj);
                                break;
                            }
                        } else {
                            pivot_cand = Some(xj);
                            break;
                        }
                    }
                }
            }

            match pivot_cand {
                Some(xj) => {
                    self.pivot(xi, xj);
                }
                None => {
                    // Infeasible! Construct conflict explanation from bounds of xi and its row
                    let mut conflict = Vec::new();
                    if is_above_upper {
                        if let Some(ub) = &self.upper_bounds[xi] {
                            if let Some(lit) = ub.reason {
                                conflict.push(!lit);
                            }
                        }
                    } else if let Some(lb) = &self.lower_bounds[xi] {
                        if let Some(lit) = lb.reason {
                            conflict.push(!lit);
                        }
                    }

                    for (&xj, a_ij) in &self.tableau[xi] {
                        if (a_ij.is_positive() && is_above_upper) || (a_ij.is_negative() && !is_above_upper) {
                            if let Some(lb) = &self.lower_bounds[xj] {
                                if let Some(lit) = lb.reason {
                                    conflict.push(!lit);
                                }
                            }
                        } else if let Some(ub) = &self.upper_bounds[xj] {
                            if let Some(lit) = ub.reason {
                                conflict.push(!lit);
                            }
                        }
                    }

                    return Err(conflict);
                }
            }
        }

        Ok(())
    }

    /// Evaluates concrete value of a variable.
    pub fn get_value(&self, var: SimplexVar) -> &DeltaRational {
        &self.assignment[var]
    }
}

impl<'a> Theory for SimplexSolver<'a> {
    fn assert_term(&mut self, lit: Lit, term: TermId) {
        let op = self.arena.op_of(term).clone();
        let args = self.arena.args_of(term);

        match op {
            Op::Lt | Op::Le | Op::Gt | Op::Ge if args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];

                // Constant on RHS
                let rhs_val = match self.arena.op_of(rhs) {
                    Op::IntConst(i) => Some(BigRational::from_integer(i.clone())),
                    Op::RealConst(r) => Some(r.clone()),
                    _ => None,
                };

                if let Some(val) = rhs_val {
                    let var = self.get_or_create_var(lhs, false);
                    match op {
                        Op::Le => {
                            if lit.is_pos() {
                                self.set_upper_bound(var, Bound {
                                    value: DeltaRational::from_rational(val),
                                    reason: Some(lit),
                                });
                            } else {
                                // !(x <= val) <=> x > val <=> x >= val + delta
                                self.set_lower_bound(var, Bound {
                                    value: DeltaRational::new(val, BigRational::one()),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Lt => {
                            if lit.is_pos() {
                                // x < val <=> x <= val - delta
                                self.set_upper_bound(var, Bound {
                                    value: DeltaRational::new(val, -BigRational::one()),
                                    reason: Some(lit),
                                });
                            } else {
                                // !(x < val) <=> x >= val
                                self.set_lower_bound(var, Bound {
                                    value: DeltaRational::from_rational(val),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Ge => {
                            if lit.is_pos() {
                                self.set_lower_bound(var, Bound {
                                    value: DeltaRational::from_rational(val),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_upper_bound(var, Bound {
                                    value: DeltaRational::new(val, -BigRational::one()),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Gt => {
                            if lit.is_pos() {
                                self.set_lower_bound(var, Bound {
                                    value: DeltaRational::new(val, BigRational::one()),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_upper_bound(var, Bound {
                                    value: DeltaRational::from_rational(val),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Eq => {
                            if lit.is_pos() {
                                self.set_lower_bound(var, Bound {
                                    value: DeltaRational::from_rational(val.clone()),
                                    reason: Some(lit),
                                });
                                self.set_upper_bound(var, Bound {
                                    value: DeltaRational::from_rational(val),
                                    reason: Some(lit),
                                });
                            }
                        }
                        _ => {}
                    }
                } else {
                    let var_l = self.get_or_create_var(lhs, false);
                    let var_r = self.get_or_create_var(rhs, false);
                    let mut row = HashMap::new();
                    row.insert(var_l, BigRational::one());
                    row.insert(var_r, -BigRational::one());
                    let s = self.create_slack_var(row);

                    match op {
                        Op::Le => {
                            if lit.is_pos() {
                                self.set_upper_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_lower_bound(s, Bound {
                                    value: DeltaRational::new(BigRational::zero(), BigRational::one()),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Lt => {
                            if lit.is_pos() {
                                self.set_upper_bound(s, Bound {
                                    value: DeltaRational::new(BigRational::zero(), -BigRational::one()),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_lower_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Ge => {
                            if lit.is_pos() {
                                self.set_lower_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_upper_bound(s, Bound {
                                    value: DeltaRational::new(BigRational::zero(), -BigRational::one()),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Gt => {
                            if lit.is_pos() {
                                self.set_lower_bound(s, Bound {
                                    value: DeltaRational::new(BigRational::zero(), BigRational::one()),
                                    reason: Some(lit),
                                });
                            } else {
                                self.set_upper_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                            }
                        }
                        Op::Eq => {
                            if lit.is_pos() {
                                self.set_lower_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                                self.set_upper_bound(s, Bound {
                                    value: DeltaRational::zero(),
                                    reason: Some(lit),
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn check(&mut self) -> Result<(), Vec<Lit>> {
        self.solve_simplex()
    }

    fn propagate(&mut self) -> Vec<(Lit, Vec<Lit>)> {
        Vec::new()
    }

    fn push(&mut self) {
        self.scopes.push(self.undo_stack.len());
    }

    fn pop(&mut self) {
        if let Some(target) = self.scopes.pop() {
            while self.undo_stack.len() > target {
                match self.undo_stack.pop().unwrap() {
                    SimplexUndo::SetLowerBound { var, old } => {
                        self.lower_bounds[var] = old;
                    }
                    SimplexUndo::SetUpperBound { var, old } => {
                        self.upper_bounds[var] = old;
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.is_integer.clear();
        self.is_basic.clear();
        self.tableau.clear();
        self.assignment.clear();
        self.lower_bounds.clear();
        self.upper_bounds.clear();
        self.undo_stack.clear();
        self.scopes.clear();
    }
}
