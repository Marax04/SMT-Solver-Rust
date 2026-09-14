//! Zhegalkin Normal Form (Algebraic Normal Form - ANF) for non-linear MBA canonicalization.
//!
//! Every boolean function has a unique representation as a polynomial over GF(2):
//! P(x0, ..., xn) = XOR_m (c_m * AND_{i in m} x_i)
//!
//! Provides canonical representation for non-linear bitwise expressions.

use num_traits::Zero;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use std::collections::{BTreeSet, HashMap};

/// Monomial in Algebraic Normal Form: product of distinct variables (AND).
/// Monomial of empty set represents the constant 1.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Monomial {
    /// Indices of sorted variable IDs involved in this product.
    pub vars: Vec<u32>,
}

impl Monomial {
    /// The unit constant 1 monomial.
    pub fn one() -> Self {
        Self { vars: Vec::new() }
    }

    /// Monomial of a single variable.
    pub fn variable(var_idx: u32) -> Self {
        Self {
            vars: vec![var_idx],
        }
    }

    /// Product of two monomials: A * B (with idempotence x * x = x).
    pub fn mul(&self, other: &Self) -> Self {
        let mut set = BTreeSet::new();
        for &v in &self.vars {
            set.insert(v);
        }
        for &v in &other.vars {
            set.insert(v);
        }
        Self {
            vars: set.into_iter().collect(),
        }
    }
}

/// Zhegalkin Polynomial (Algebraic Normal Form): unique XOR sum of monomials.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ZhegalkinPolynomial {
    /// Set of active monomials (odd count means coefficient is 1, even count eliminates).
    pub terms: BTreeSet<Monomial>,
}

impl ZhegalkinPolynomial {
    /// Zero polynomial: empty XOR sum.
    pub fn zero() -> Self {
        Self {
            terms: BTreeSet::new(),
        }
    }

    /// Constant 1 polynomial.
    pub fn one() -> Self {
        let mut terms = BTreeSet::new();
        terms.insert(Monomial::one());
        Self { terms }
    }

    /// Single variable polynomial: x_i.
    pub fn variable(var_idx: u32) -> Self {
        let mut terms = BTreeSet::new();
        terms.insert(Monomial::variable(var_idx));
        Self { terms }
    }

    /// Polynomial addition over GF(2): A XOR B (symmetric difference of monomials).
    pub fn xor(&self, other: &Self) -> Self {
        let mut res = self.terms.clone();
        for m in &other.terms {
            if !res.remove(m) {
                res.insert(m.clone());
            }
        }
        Self { terms: res }
    }

    /// Polynomial negation: NOT A = 1 XOR A.
    pub fn not(&self) -> Self {
        self.xor(&Self::one())
    }

    /// Polynomial multiplication: A AND B (distributive product over GF(2)).
    pub fn and(&self, other: &Self) -> Self {
        let mut res = Self::zero();
        for m1 in &self.terms {
            for m2 in &other.terms {
                let prod = m1.mul(m2);
                res = res.xor(&Self {
                    terms: [prod].into_iter().collect(),
                });
            }
        }
        res
    }

    /// Polynomial OR: A OR B = A XOR B XOR (A AND B).
    pub fn or(&self, other: &Self) -> Self {
        let a_xor_b = self.xor(other);
        let a_and_b = self.and(other);
        a_xor_b.xor(&a_and_b)
    }

    /// Builds a Zhegalkin polynomial from an SMT bitwise boolean term.
    pub fn from_term(
        id: TermId,
        terms: &TermArena,
        var_map: &mut HashMap<TermId, u32>,
        var_rev: &mut Vec<TermId>,
    ) -> Option<Self> {
        let term = terms.get(id);
        match &term.op {
            Op::True => Some(Self::one()),
            Op::False => Some(Self::zero()),
            Op::Var(_) => {
                let idx = *var_map.entry(id).or_insert_with(|| {
                    let next_idx = var_rev.len() as u32;
                    var_rev.push(id);
                    next_idx
                });
                Some(Self::variable(idx))
            }
            Op::BvConst { value, .. } => {
                if value.is_zero() {
                    Some(Self::zero())
                } else {
                    Some(Self::one())
                }
            }
            Op::Not | Op::BvNot => {
                let inner = Self::from_term(term.args[0], terms, var_map, var_rev)?;
                Some(inner.not())
            }
            Op::Xor | Op::BvXor => {
                let a = Self::from_term(term.args[0], terms, var_map, var_rev)?;
                let b = Self::from_term(term.args[1], terms, var_map, var_rev)?;
                Some(a.xor(&b))
            }
            Op::And | Op::BvAnd => {
                let a = Self::from_term(term.args[0], terms, var_map, var_rev)?;
                let b = Self::from_term(term.args[1], terms, var_map, var_rev)?;
                Some(a.and(&b))
            }
            Op::Or | Op::BvOr => {
                let a = Self::from_term(term.args[0], terms, var_map, var_rev)?;
                let b = Self::from_term(term.args[1], terms, var_map, var_rev)?;
                Some(a.or(&b))
            }
            _ => None,
        }
    }

    /// Attempts to canonicalize a bitwise boolean term into Zhegalkin Normal Form.
    pub fn simplify(
        term_id: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> Option<TermId> {
        let mut var_map = HashMap::new();
        let mut var_rev = Vec::new();
        let poly = Self::from_term(term_id, terms, &mut var_map, &mut var_rev)?;
        let width = match sorts.get(terms.get(term_id).sort) {
            smt_core::sort::Sort::BitVec(width) => *width,
            smt_core::sort::Sort::Bool => 1,
            _ => return None,
        };

        let canonical = poly.to_term(terms, sorts, &var_rev, width);
        if canonical != term_id {
            Some(canonical)
        } else {
            None
        }
    }

    /// Reconstructs a canonical SMT term from the Zhegalkin polynomial.
    pub fn to_term(
        &self,
        terms: &mut TermArena,
        sorts: &mut SortArena,
        var_rev: &[TermId],
        width: u32,
    ) -> TermId {
        if self.terms.is_empty() {
            return terms.bv_const(0u32.into(), width, sorts);
        }

        let mut mono_terms = Vec::with_capacity(self.terms.len());
        for m in &self.terms {
            if m.vars.is_empty() {
                // Constant 1
                mono_terms.push(terms.bv_const(1u32.into(), width, sorts));
            } else {
                let mut p = var_rev[m.vars[0] as usize];
                for &v_idx in &m.vars[1..] {
                    let next_v = var_rev[v_idx as usize];
                    p = terms.bv_binop(Op::BvAnd, p, next_v).unwrap_or(p);
                }
                mono_terms.push(p);
            }
        }

        let mut res = mono_terms[0];
        for &mt in &mono_terms[1..] {
            res = terms.bv_binop(Op::BvXor, res, mt).unwrap_or(res);
        }

        res
    }
}
