//! Linear Mixed Boolean-Arithmetic (Linear MBA) Simplification Engine.

use crate::truth_table::TruthTable;
use num_traits::ToPrimitive;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use std::collections::HashMap;

/// Linear combination of bitwise truth tables: V = sum c_i * T(e_i).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearMbaVector {
    pub values: [i64; 16],
}

impl LinearMbaVector {
    /// Creates a zero vector for linear MBA combinations.
    ///
    /// # Example
    /// ```rust
    /// use smt_mba::linear_mba::LinearMbaVector;
    /// let v = LinearMbaVector::zero();
    /// assert_eq!(v.values[0], 0);
    /// ```
    pub fn zero() -> Self {
        Self { values: [0; 16] }
    }

    pub fn from_truth_table(tt: TruthTable, coeff: i64) -> Self {
        let mut vals = [0; 16];
        for (i, val) in vals.iter_mut().enumerate() {
            if (tt.0 >> i) & 1 == 1 {
                *val = coeff;
            }
        }
        Self { values: vals }
    }

    pub fn add(&mut self, other: &Self) {
        for i in 0..16 {
            self.values[i] += other.values[i];
        }
    }

    pub fn sub(&mut self, other: &Self) {
        for i in 0..16 {
            self.values[i] -= other.values[i];
        }
    }
}

/// Linear MBA simplifier mapping linear combinations of bitwise operations to simplified arithmetic.
pub struct LinearMbaSimplifier;

impl LinearMbaSimplifier {
    /// Attempts to simplify a linear MBA expression.
    pub fn simplify(
        term_id: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> Option<TermId> {
        let mut vars = Vec::new();
        Self::collect_vars(term_id, terms, &mut vars);
        if vars.is_empty() || vars.len() > 4 {
            return None;
        }

        let mut var_map = HashMap::new();
        for (i, &v) in vars.iter().enumerate() {
            var_map.insert(v, i);
        }

        let mut vec = LinearMbaVector::zero();
        if !Self::evaluate_linear_term(term_id, 1, terms, &var_map, &mut vec) {
            return None;
        }

        // Check if the resulting vector matches a target simplified expression
        if vars.len() == 2 {
            let x = vars[0];
            let y = vars[1];

            let tx = TruthTable::VAR0;
            let ty = TruthTable::VAR1;

            let vec_x = LinearMbaVector::from_truth_table(tx, 1);
            let vec_y = LinearMbaVector::from_truth_table(ty, 1);

            // 1. x + y
            let mut target_add = vec_x.clone();
            target_add.add(&vec_y);
            if vec == target_add {
                return terms.bv_binop(Op::BvAdd, x, y).ok();
            }

            // 2. x - y
            let mut target_sub = vec_x.clone();
            target_sub.sub(&vec_y);
            if vec == target_sub {
                return terms.bv_binop(Op::BvSub, x, y).ok();
            }

            // 3. y - x
            let mut target_sub_yx = vec_y.clone();
            target_sub_yx.sub(&vec_x);
            if vec == target_sub_yx {
                return terms.bv_binop(Op::BvSub, y, x).ok();
            }

            // 4. x ^ y
            let target_xor = LinearMbaVector::from_truth_table(tx.xor(ty), 1);
            if vec == target_xor {
                return terms.bv_binop(Op::BvXor, x, y).ok();
            }

            // 5. x & y
            let target_and = LinearMbaVector::from_truth_table(tx.and(ty), 1);
            if vec == target_and {
                return terms.bv_binop(Op::BvAnd, x, y).ok();
            }

            // 6. x | y
            let target_or = LinearMbaVector::from_truth_table(tx.or(ty), 1);
            if vec == target_or {
                return terms.bv_binop(Op::BvOr, x, y).ok();
            }

            // 7. x
            if vec == vec_x {
                return Some(x);
            }

            // 8. y
            if vec == vec_y {
                return Some(y);
            }

            // 9. 0
            if vec == LinearMbaVector::zero() {
                let width = match sorts.get(terms.sort_of(x)) {
                    smt_core::sort::Sort::BitVec(w) => *w,
                    _ => 32,
                };
                return Some(terms.bv_const(0u32.into(), width, sorts));
            }
        }

        None
    }

    fn collect_vars(term_id: TermId, terms: &TermArena, vars: &mut Vec<TermId>) {
        let term = terms.get(term_id);
        if matches!(term.op, Op::Var(_)) {
            if !vars.contains(&term_id) {
                vars.push(term_id);
            }
            return;
        }
        for &arg in &term.args {
            Self::collect_vars(arg, terms, vars);
        }
    }

    fn evaluate_linear_term(
        term_id: TermId,
        coeff: i64,
        terms: &TermArena,
        var_map: &HashMap<TermId, usize>,
        acc: &mut LinearMbaVector,
    ) -> bool {
        let term = terms.get(term_id);
        match &term.op {
            Op::BvAdd => {
                Self::evaluate_linear_term(term.args[0], coeff, terms, var_map, acc)
                    && Self::evaluate_linear_term(term.args[1], coeff, terms, var_map, acc)
            }
            Op::BvSub => {
                Self::evaluate_linear_term(term.args[0], coeff, terms, var_map, acc)
                    && Self::evaluate_linear_term(term.args[1], -coeff, terms, var_map, acc)
            }
            Op::BvMul => {
                // Check if one operand is a constant scalar
                let left_const = Self::get_constant(term.args[0], terms);
                let right_const = Self::get_constant(term.args[1], terms);

                if let Some(c) = left_const {
                    Self::evaluate_linear_term(term.args[1], coeff * c, terms, var_map, acc)
                } else if let Some(c) = right_const {
                    Self::evaluate_linear_term(term.args[0], coeff * c, terms, var_map, acc)
                } else {
                    false
                }
            }
            _ => {
                // Evaluate bitwise expression truth table
                if let Some(tt) = TruthTable::from_term(term_id, terms, var_map) {
                    let v = LinearMbaVector::from_truth_table(tt, coeff);
                    acc.add(&v);
                    true
                } else {
                    false
                }
            }
        }
    }

    fn get_constant(term_id: TermId, terms: &TermArena) -> Option<i64> {
        let term = terms.get(term_id);
        match &term.op {
            Op::BvConst { value, .. } => value.to_i64(),
            Op::IntConst(i) => i.to_i64(),
            _ => None,
        }
    }
}
