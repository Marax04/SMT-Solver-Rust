//! Canonicalization and algebraic normalization for bitwise/arithmetic expressions.

use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};

/// Canonicalizer reducing equivalent bitwise patterns into canonical form before solving.
pub struct MbaCanonicalizer;

impl MbaCanonicalizer {
    /// Recursively normalizes a term.
    pub fn normalize(id: TermId, terms: &mut TermArena, sorts: &mut SortArena) -> TermId {
        let term = terms.get(id).clone();
        let mut new_args = Vec::with_capacity(term.args.len());
        for &arg in &term.args {
            new_args.push(Self::normalize(arg, terms, sorts));
        }

        // Commutative sorting
        if is_commutative(&term.op) && new_args.len() == 2 {
            if new_args[0].0 > new_args[1].0 {
                new_args.swap(0, 1);
            }
        }

        match &term.op {
            Op::BvNot => {
                let inner = new_args[0];
                let inner_term = terms.get(inner).clone();
                // Double negation: ~~a => a
                if inner_term.op == Op::BvNot {
                    return inner_term.args[0];
                }
                // De Morgan: ~(a & b) => ~a | ~b
                if inner_term.op == Op::BvAnd && inner_term.args.len() == 2 {
                    let not_a = Self::normalize(terms.intern(Op::BvNot, vec![inner_term.args[0]], term.sort), terms, sorts);
                    let not_b = Self::normalize(terms.intern(Op::BvNot, vec![inner_term.args[1]], term.sort), terms, sorts);
                    return terms.intern(Op::BvOr, vec![not_a, not_b], term.sort);
                }
                // De Morgan: ~(a | b) => ~a & ~b
                if inner_term.op == Op::BvOr && inner_term.args.len() == 2 {
                    let not_a = Self::normalize(terms.intern(Op::BvNot, vec![inner_term.args[0]], term.sort), terms, sorts);
                    let not_b = Self::normalize(terms.intern(Op::BvNot, vec![inner_term.args[1]], term.sort), terms, sorts);
                    return terms.intern(Op::BvAnd, vec![not_a, not_b], term.sort);
                }
            }
            Op::BvNeg => {
                let inner = new_args[0];
                let inner_term = terms.get(inner).clone();
                // Double arithmetic negation: -(-a) => a
                if inner_term.op == Op::BvNeg {
                    return inner_term.args[0];
                }
            }
            Op::BvXor => {
                if new_args.len() == 2 && new_args[0] == new_args[1] {
                    // a ^ a => 0
                    let width = match sorts.get(term.sort) {
                        smt_core::sort::Sort::BitVec(w) => *w,
                        _ => 32,
                    };
                    return terms.bv_const(0u32.into(), width, sorts);
                }
            }
            Op::BvSub => {
                if new_args.len() == 2 && new_args[0] == new_args[1] {
                    // a - a => 0
                    let width = match sorts.get(term.sort) {
                        smt_core::sort::Sort::BitVec(w) => *w,
                        _ => 32,
                    };
                    return terms.bv_const(0u32.into(), width, sorts);
                }
            }
            Op::BvAnd => {
                if new_args.len() == 2 && new_args[0] == new_args[1] {
                    // a & a => a
                    return new_args[0];
                }
            }
            Op::BvOr => {
                if new_args.len() == 2 && new_args[0] == new_args[1] {
                    // a | a => a
                    return new_args[0];
                }
            }
            _ => {}
        }

        terms.intern(term.op, new_args, term.sort)
    }
}

fn is_commutative(op: &Op) -> bool {
    matches!(
        op,
        Op::And | Op::Or | Op::Xor | Op::BvAnd | Op::BvOr | Op::BvXor | Op::BvAdd | Op::BvMul | Op::Eq
    )
}
