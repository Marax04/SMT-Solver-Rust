//! Deep recursive constant folding across Booleans, Bit-Vectors, and Arithmetic.

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};

/// Evaluates constant expressions recursively.
pub struct ConstantFolder<'a> {
    pub terms: &'a mut TermArena,
    pub sorts: &'a mut SortArena,
    pub steps: usize,
    pub max_steps: usize,
}

impl<'a> ConstantFolder<'a> {
    /// Creates a new constant folder.
    pub fn new(terms: &'a mut TermArena, sorts: &'a mut SortArena) -> Self {
        Self {
            terms,
            sorts,
            steps: 0,
            max_steps: 100_000,
        }
    }

    /// Folds a term and its sub-terms into a simplified form.
    pub fn fold_term(&mut self, id: TermId) -> TermId {
        self.steps += 1;
        if self.steps > self.max_steps {
            return id;
        }
        let term_data = self.terms.get(id).clone();
        let folded_args: Vec<TermId> = term_data
            .args
            .iter()
            .map(|&arg| self.fold_term(arg))
            .collect();

        match &term_data.op {
            // --- Boolean ops ---
            Op::Not => {
                let arg = folded_args[0];
                if arg == self.terms.true_id {
                    return self.terms.false_id;
                }
                if arg == self.terms.false_id {
                    return self.terms.true_id;
                }
                if let Op::Not = self.terms.op_of(arg) {
                    return self.terms.args_of(arg)[0];
                }
            }
            Op::And => {
                if folded_args.contains(&self.terms.false_id) {
                    return self.terms.false_id;
                }
                let non_true: Vec<TermId> = folded_args
                    .into_iter()
                    .filter(|&a| a != self.terms.true_id)
                    .collect();
                if non_true.is_empty() {
                    return self.terms.true_id;
                }
                if non_true.len() == 1 {
                    return non_true[0];
                }
                return self.terms.intern(Op::And, non_true, self.sorts.bool_sort);
            }
            Op::Or => {
                if folded_args.contains(&self.terms.true_id) {
                    return self.terms.true_id;
                }
                let non_false: Vec<TermId> = folded_args
                    .into_iter()
                    .filter(|&a| a != self.terms.false_id)
                    .collect();
                if non_false.is_empty() {
                    return self.terms.false_id;
                }
                if non_false.len() == 1 {
                    return non_false[0];
                }
                return self.terms.intern(Op::Or, non_false, self.sorts.bool_sort);
            }
            Op::Xor => {
                let a = folded_args[0];
                let b = folded_args[1];
                if a == b {
                    return self.terms.false_id;
                }
                if a == self.terms.false_id {
                    return b;
                }
                if b == self.terms.false_id {
                    return a;
                }
                if a == self.terms.true_id {
                    return self.terms.not(b);
                }
                if b == self.terms.true_id {
                    return self.terms.not(a);
                }
            }
            Op::Implies => {
                let a = folded_args[0];
                let b = folded_args[1];
                if a == self.terms.false_id || b == self.terms.true_id {
                    return self.terms.true_id;
                }
                if a == self.terms.true_id {
                    return b;
                }
            }
            Op::Ite => {
                let cond = folded_args[0];
                let then_b = folded_args[1];
                let else_b = folded_args[2];
                if cond == self.terms.true_id {
                    return then_b;
                }
                if cond == self.terms.false_id {
                    return else_b;
                }
                if then_b == else_b {
                    return then_b;
                }
            }
            Op::Eq => {
                let a = folded_args[0];
                let b = folded_args[1];
                if a == b {
                    return self.terms.true_id;
                }
                let op_a = self.terms.op_of(a).clone();
                let op_b = self.terms.op_of(b).clone();
                if let (Op::BvConst { value: v1, .. }, Op::BvConst { value: v2, .. }) =
                    (&op_a, &op_b)
                {
                    return if v1 == v2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::IntConst(i1), Op::IntConst(i2)) = (&op_a, &op_b) {
                    return if i1 == i2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::RealConst(r1), Op::RealConst(r2)) = (&op_a, &op_b) {
                    return if r1 == r2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            // --- Bit-Vector constant evaluations ---
            Op::BvAdd => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let sum = (v1 + v2) & bv_mask(w1);
                    return self.terms.bv_const(sum, w1, self.sorts);
                }
            }
            Op::BvSub => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let mask = bv_mask(w1);
                    let modulus = BigUint::from(1u32) << w1;
                    let diff = (v1 + &modulus - (v2 & &mask)) & mask;
                    return self.terms.bv_const(diff, w1, self.sorts);
                }
            }
            Op::BvMul => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let prod = (v1 * v2) & bv_mask(w1);
                    return self.terms.bv_const(prod, w1, self.sorts);
                }
            }
            Op::BvUdiv => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    if v2.is_zero() {
                        // SMT-LIB division by zero yields 2^w - 1 (all ones)
                        return self.terms.bv_const(bv_mask(w1), w1, self.sorts);
                    }
                    let res = (v1 / v2) & bv_mask(w1);
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvUrem => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    if v2.is_zero() {
                        return self.terms.bv_const(v1, w1, self.sorts);
                    }
                    let res = (v1 % v2) & bv_mask(w1);
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvAnd => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let res = (v1 & v2) & bv_mask(w1);
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvOr => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let res = (v1 | v2) & bv_mask(w1);
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvXor => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let res = (v1 ^ v2) & bv_mask(w1);
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvNot => {
                if let Some((v, w)) = self.as_bv_const(folded_args[0]) {
                    let res = bv_mask(w) ^ v;
                    return self.terms.bv_const(res, w, self.sorts);
                }
            }
            Op::BvShl => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let shift = v2.to_usize().unwrap_or(w1 as usize);
                    let res = if shift >= w1 as usize {
                        BigUint::zero()
                    } else {
                        (v1 << shift) & bv_mask(w1)
                    };
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvLshr => {
                if let (Some((v1, w1)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let shift = v2.to_usize().unwrap_or(w1 as usize);
                    let res = if shift >= w1 as usize {
                        BigUint::zero()
                    } else {
                        (v1 >> shift) & bv_mask(w1)
                    };
                    return self.terms.bv_const(res, w1, self.sorts);
                }
            }
            Op::BvConcat => {
                if let (Some((v1, w1)), Some((v2, w2))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    let res = ((v1 << w2) | v2) & bv_mask(w1 + w2);
                    return self.terms.bv_const(res, w1 + w2, self.sorts);
                }
            }
            Op::BvExtract { high, low } => {
                if let Some((v, _)) = self.as_bv_const(folded_args[0]) {
                    let shift = *low;
                    let width = high - low + 1;
                    let res = (v >> shift) & bv_mask(width);
                    return self.terms.bv_const(res, width, self.sorts);
                }
            }
            Op::BvUlt => {
                if let (Some((v1, _)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    return if v1 < v2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::BvUle => {
                if let (Some((v1, _)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    return if v1 <= v2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::BvUgt => {
                if let (Some((v1, _)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    return if v1 > v2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::BvUge => {
                if let (Some((v1, _)), Some((v2, _))) = (
                    self.as_bv_const(folded_args[0]),
                    self.as_bv_const(folded_args[1]),
                ) {
                    return if v1 >= v2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            // --- Arithmetic constant evaluations ---
            Op::Add => {
                let all_int = folded_args
                    .iter()
                    .all(|&a| matches!(self.terms.op_of(a), Op::IntConst(_)));
                if all_int && !folded_args.is_empty() {
                    let mut sum = BigInt::zero();
                    for &a in &folded_args {
                        if let Op::IntConst(val) = self.terms.op_of(a) {
                            sum += val;
                        }
                    }
                    return self.terms.int_const(sum, self.sorts);
                }
                let all_real = folded_args
                    .iter()
                    .all(|&a| matches!(self.terms.op_of(a), Op::RealConst(_)));
                if all_real && !folded_args.is_empty() {
                    let mut sum = BigRational::zero();
                    for &a in &folded_args {
                        if let Op::RealConst(val) = self.terms.op_of(a) {
                            sum += val;
                        }
                    }
                    return self.terms.real_const(sum, self.sorts);
                }
            }
            Op::Sub => {
                if folded_args.len() == 2 {
                    if let (Op::IntConst(i1), Op::IntConst(i2)) = (
                        self.terms.op_of(folded_args[0]),
                        self.terms.op_of(folded_args[1]),
                    ) {
                        return self.terms.int_const(i1 - i2, self.sorts);
                    }
                    if let (Op::RealConst(r1), Op::RealConst(r2)) = (
                        self.terms.op_of(folded_args[0]),
                        self.terms.op_of(folded_args[1]),
                    ) {
                        return self.terms.real_const(r1 - r2, self.sorts);
                    }
                }
            }
            Op::Mul => {
                let all_int = folded_args
                    .iter()
                    .all(|&a| matches!(self.terms.op_of(a), Op::IntConst(_)));
                if all_int && !folded_args.is_empty() {
                    let mut prod = BigInt::from(1);
                    for &a in &folded_args {
                        if let Op::IntConst(val) = self.terms.op_of(a) {
                            prod *= val;
                        }
                    }
                    return self.terms.int_const(prod, self.sorts);
                }
                let all_real = folded_args
                    .iter()
                    .all(|&a| matches!(self.terms.op_of(a), Op::RealConst(_)));
                if all_real && !folded_args.is_empty() {
                    let mut prod = BigRational::from_integer(BigInt::from(1));
                    for &a in &folded_args {
                        if let Op::RealConst(val) = self.terms.op_of(a) {
                            prod *= val;
                        }
                    }
                    return self.terms.real_const(prod, self.sorts);
                }
            }
            Op::Lt => {
                if let (Op::IntConst(i1), Op::IntConst(i2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if i1 < i2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::RealConst(r1), Op::RealConst(r2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if r1 < r2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::Le => {
                if let (Op::IntConst(i1), Op::IntConst(i2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if i1 <= i2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::RealConst(r1), Op::RealConst(r2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if r1 <= r2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::Gt => {
                if let (Op::IntConst(i1), Op::IntConst(i2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if i1 > i2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::RealConst(r1), Op::RealConst(r2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if r1 > r2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            Op::Ge => {
                if let (Op::IntConst(i1), Op::IntConst(i2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if i1 >= i2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
                if let (Op::RealConst(r1), Op::RealConst(r2)) = (
                    self.terms.op_of(folded_args[0]),
                    self.terms.op_of(folded_args[1]),
                ) {
                    return if r1 >= r2 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    };
                }
            }
            _ => {}
        }

        self.terms.intern(term_data.op, folded_args, term_data.sort)
    }

    fn as_bv_const(&self, id: TermId) -> Option<(BigUint, u32)> {
        match self.terms.op_of(id) {
            Op::BvConst { value, width } => Some((value.clone(), *width)),
            _ => None,
        }
    }
}

/// Helper function to create a bitmask for `width` bits.
fn bv_mask(width: u32) -> BigUint {
    if width > 0 {
        (BigUint::from(1u32) << width) - 1u32
    } else {
        BigUint::zero()
    }
}

/// Converts a signed BitVector BigUint to BigInt for signed operations.
pub fn bv_to_signed(val: &BigUint, width: u32) -> BigInt {
    let sign_bit = BigUint::from(1u32) << (width - 1);
    if (val & &sign_bit).is_zero() {
        BigInt::from_biguint(Sign::Plus, val.clone())
    } else {
        let modulus = BigInt::from_biguint(Sign::Plus, BigUint::from(1u32) << width);
        let pos = BigInt::from_biguint(Sign::Plus, val.clone());
        pos - modulus
    }
}
