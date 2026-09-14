//! Concrete values produced during model generation and constant evaluation.

use crate::sort::SortId;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use std::fmt;

/// Evaluated concrete value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    /// Boolean constant.
    Bool(bool),
    /// Bit-vector constant with fixed width.
    BitVec {
        value: BigUint,
        width: u32,
    },
    /// Arbitrary-precision integer.
    Int(BigInt),
    /// Exact rational number.
    Real(BigRational),
    /// Array mapping with a default fallback value and explicit index-value entries.
    Array {
        default: Box<Value>,
        entries: Vec<(Value, Value)>,
    },
    /// An uninterpreted domain element.
    Uninterpreted {
        sort: SortId,
        id: u32,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            Self::BitVec { value, width } => {
                let s = format!("{:x}", value);
                let hex_len = ((width + 3) / 4) as usize;
                let padded = format!("{:0>width$}", s, width = hex_len);
                write!(f, "#x{}", padded)
            }
            Self::Int(i) => write!(f, "{}", i),
            Self::Real(r) => {
                if r.is_integer() {
                    write!(f, "{}.0", r.to_integer())
                } else {
                    write!(f, "(/ {} {})", r.numer(), r.denom())
                }
            }
            Self::Array { default, entries } => {
                write!(f, "[default: {}, entries: {:?}]", default, entries)
            }
            Self::Uninterpreted { sort, id } => write!(f, "@{}_{}", sort, id),
        }
    }
}

impl Value {
    /// Constructs a bit-vector value masked to width.
    pub fn new_bv(mut val: BigUint, width: u32) -> Self {
        let mask = if width >= 1 {
            (BigUint::from(1u32) << width) - 1u32
        } else {
            BigUint::from(0u32)
        };
        val &= mask;
        Self::BitVec { value: val, width }
    }

    /// Helper to get the boolean value if this is a Bool.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Helper to get the bit-vector value if this is a BitVec.
    pub fn as_bv(&self) -> Option<(&BigUint, u32)> {
        match self {
            Self::BitVec { value, width } => Some((value, *width)),
            _ => None,
        }
    }

    /// Helper to get the integer value if this is an Int.
    pub fn as_int(&self) -> Option<&BigInt> {
        match self {
            Self::Int(i) => Some(i),
            _ => None,
        }
    }

    /// Helper to get the rational value if this is a Real.
    pub fn as_real(&self) -> Option<&BigRational> {
        match self {
            Self::Real(r) => Some(r),
            _ => None,
        }
    }
}
