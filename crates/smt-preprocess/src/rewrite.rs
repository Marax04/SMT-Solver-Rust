//! Algebraic rewrite and normalization rules.

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};

/// Algebraic simplification and term normalization engine.
pub struct Rewriter<'a> {
    pub terms: &'a mut TermArena,
    pub sorts: &'a mut SortArena,
    pub steps: usize,
    pub max_steps: usize,
}

impl<'a> Rewriter<'a> {
    /// Creates a rewriter.
    pub fn new(terms: &'a mut TermArena, sorts: &'a mut SortArena) -> Self {
        Self {
            terms,
            sorts,
            steps: 0,
            max_steps: 100_000,
        }
    }

    /// Rewrites a term by applying algebraic identities and canonical ordering.
    pub fn rewrite(&mut self, id: TermId) -> TermId {
        self.steps += 1;
        if self.steps > self.max_steps {
            return id;
        }
        let term = self.terms.get(id).clone();
        let mut rewritten_args: Vec<TermId> = term.args.iter().map(|&a| self.rewrite(a)).collect();

        // Canonical ordering for commutative operators
        if is_commutative(&term.op) && rewritten_args.len() >= 2 {
            rewritten_args.sort_by_key(|t| t.0);
        }

        match &term.op {
            Op::Eq => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if a == b {
                    return self.terms.true_id;
                }
            }
            Op::BvAdd => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if self.is_bv_zero(a) {
                    return b;
                }
                if self.is_bv_zero(b) {
                    return a;
                }
            }
            Op::BvSub => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if a == b {
                    let w = self.bv_width(a);
                    return self.terms.bv_const(BigUint::zero(), w, self.sorts);
                }
                if self.is_bv_zero(b) {
                    return a;
                }
            }
            Op::BvXor => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if a == b {
                    let w = self.bv_width(a);
                    return self.terms.bv_const(BigUint::zero(), w, self.sorts);
                }
                if self.is_bv_zero(a) {
                    return b;
                }
                if self.is_bv_zero(b) {
                    return a;
                }
            }
            Op::BvAnd => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if a == b {
                    return a;
                }
                if self.is_bv_zero(a) || self.is_bv_zero(b) {
                    let w = self.bv_width(a);
                    return self.terms.bv_const(BigUint::zero(), w, self.sorts);
                }
            }
            Op::BvOr => {
                let a = rewritten_args[0];
                let b = rewritten_args[1];
                if a == b {
                    return a;
                }
                if self.is_bv_zero(a) {
                    return b;
                }
                if self.is_bv_zero(b) {
                    return a;
                }
            }
            Op::Add => {
                let non_zero: Vec<TermId> = rewritten_args
                    .iter()
                    .copied()
                    .filter(|&a| !self.is_int_zero(a))
                    .collect();
                if non_zero.is_empty() {
                    return self.terms.int_const(BigInt::zero(), self.sorts);
                }
                if non_zero.len() == 1 {
                    return non_zero[0];
                }
                return self.terms.intern(Op::Add, non_zero, term.sort);
            }
            Op::Sub => {
                if rewritten_args.len() == 2 {
                    let a = rewritten_args[0];
                    let b = rewritten_args[1];
                    if a == b {
                        return self.terms.int_const(BigInt::zero(), self.sorts);
                    }
                    if self.is_int_zero(b) {
                        return a;
                    }
                }
            }
            Op::Distinct => {
                if rewritten_args.len() <= 1 {
                    return self.terms.true_id;
                } else if rewritten_args.len() == 2 {
                    let eq = self
                        .terms
                        .eq(rewritten_args[0], rewritten_args[1], self.sorts);
                    return self.terms.not(eq);
                } else {
                    let mut diffs = Vec::new();
                    for i in 0..rewritten_args.len() {
                        for j in (i + 1)..rewritten_args.len() {
                            let eq =
                                self.terms
                                    .eq(rewritten_args[i], rewritten_args[j], self.sorts);
                            diffs.push(self.terms.not(eq));
                        }
                    }
                    return self.terms.and(diffs, self.sorts);
                }
            }
            _ => {}
        }

        self.terms.intern(term.op, rewritten_args, term.sort)
    }

    fn is_bv_zero(&self, id: TermId) -> bool {
        match self.terms.op_of(id) {
            Op::BvConst { value, .. } => value.is_zero(),
            _ => false,
        }
    }

    fn is_int_zero(&self, id: TermId) -> bool {
        match self.terms.op_of(id) {
            Op::IntConst(i) => i.is_zero(),
            _ => false,
        }
    }

    fn bv_width(&self, id: TermId) -> u32 {
        let sort = self.terms.sort_of(id);
        match self.sorts.get(sort) {
            smt_core::sort::Sort::BitVec(w) => *w,
            _ => 1,
        }
    }
}

fn is_commutative(op: &Op) -> bool {
    matches!(
        op,
        Op::And
            | Op::Or
            | Op::Xor
            | Op::Eq
            | Op::Distinct
            | Op::BvAdd
            | Op::BvMul
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::Add
            | Op::Mul
    )
}
