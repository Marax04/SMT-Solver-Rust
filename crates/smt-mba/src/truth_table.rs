//! 1-bit space truth table representation for bitwise Boolean expressions.

use smt_core::term::{Op, TermArena, TermId};
use std::collections::HashMap;

/// Truth table for a boolean function of up to 4 variables (16 entries).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TruthTable(pub u16);

impl TruthTable {
    pub const ZERO: Self = Self(0x0000);
    pub const ONE: Self = Self(0xFFFF);

    /// Variable 0 projection (pattern: 0101_0101_0101_0101).
    pub const VAR0: Self = Self(0xAAAA);
    /// Variable 1 projection (pattern: 0011_0011_0011_0011).
    pub const VAR1: Self = Self(0xCCCC);
    /// Variable 2 projection (pattern: 00001111_00001111).
    pub const VAR2: Self = Self(0xF0F0);
    /// Variable 3 projection (pattern: 0000000011111111).
    pub const VAR3: Self = Self(0xFF00);

    pub fn not(self) -> Self {
        Self(!self.0)
    }

    pub fn and(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    pub fn or(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub fn xor(self, other: Self) -> Self {
        Self(self.0 ^ other.0)
    }

    /// Evaluates the truth table of a pure bitwise term.
    pub fn from_term(
        term_id: TermId,
        terms: &TermArena,
        var_map: &HashMap<TermId, usize>,
    ) -> Option<Self> {
        let term = terms.get(term_id);
        if let Some(&var_idx) = var_map.get(&term_id) {
            return match var_idx {
                0 => Some(Self::VAR0),
                1 => Some(Self::VAR1),
                2 => Some(Self::VAR2),
                3 => Some(Self::VAR3),
                _ => None,
            };
        }

        match &term.op {
            Op::BvConst { value, .. } => {
                if value == &num_bigint::BigUint::from(0u32) {
                    Some(Self::ZERO)
                } else {
                    Some(Self::ONE)
                }
            }
            Op::BvNot => {
                let inner = Self::from_term(term.args[0], terms, var_map)?;
                Some(inner.not())
            }
            Op::BvAnd => {
                let a = Self::from_term(term.args[0], terms, var_map)?;
                let b = Self::from_term(term.args[1], terms, var_map)?;
                Some(a.and(b))
            }
            Op::BvOr => {
                let a = Self::from_term(term.args[0], terms, var_map)?;
                let b = Self::from_term(term.args[1], terms, var_map)?;
                Some(a.or(b))
            }
            Op::BvXor => {
                let a = Self::from_term(term.args[0], terms, var_map)?;
                let b = Self::from_term(term.args[1], terms, var_map)?;
                Some(a.xor(b))
            }
            _ => None,
        }
    }
}
