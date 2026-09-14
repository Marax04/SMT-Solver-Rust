//! Variable, Literal, and Ternary Boolean representation.

use std::fmt;
use std::ops::Not;

/// Boolean variable identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u32);

impl Var {
    /// Index representation.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Forms a positive literal.
    #[inline]
    pub fn to_lit(self) -> Lit {
        Lit(self.0 << 1)
    }

    /// Forms a negated literal.
    #[inline]
    pub fn to_neg_lit(self) -> Lit {
        Lit((self.0 << 1) | 1)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Literal representation with sign encoded in LSB.
///
/// If `lit.0 & 1 == 0`, literal is positive: `Var(lit.0 >> 1)`.
/// If `lit.0 & 1 == 1`, literal is negative: `!Var(lit.0 >> 1)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(pub u32);

impl Lit {
    /// Creates a literal given a variable and whether it is negated.
    #[inline]
    pub fn new(var: Var, negated: bool) -> Self {
        Self((var.0 << 1) | (negated as u32))
    }

    /// Returns the underlying variable.
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Returns true if literal is positive.
    #[inline]
    pub fn is_pos(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Returns true if literal is negative.
    #[inline]
    pub fn is_neg(self) -> bool {
        (self.0 & 1) == 1
    }

    /// Returns index representation in 2 * num_vars watch tables.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Converts literal to 1-based DIMACS format integer.
    pub fn to_dimacs(self) -> i32 {
        let v = (self.var().0 + 1) as i32;
        if self.is_pos() {
            v
        } else {
            -v
        }
    }

    /// Constructs literal from 1-based DIMACS integer.
    pub fn from_dimacs(d: i32) -> Self {
        assert!(d != 0, "DIMACS literal cannot be zero");
        let v = Var((d.abs() - 1) as u32);
        Self::new(v, d < 0)
    }
}

impl Not for Lit {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Self(self.0 ^ 1)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_neg() {
            write!(f, "-{}", self.var().0 + 1)
        } else {
            write!(f, "{}", self.var().0 + 1)
        }
    }
}

/// Ternary boolean value for partial assignments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LBool {
    Undef,
    True,
    False,
}

impl LBool {
    /// Creates LBool from a primitive boolean.
    #[inline]
    pub fn from_bool(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }

    /// Returns true if value is defined (True or False).
    #[inline]
    pub fn is_defined(self) -> bool {
        !matches!(self, Self::Undef)
    }

    /// Returns true if value is True.
    #[inline]
    pub fn is_true(self) -> bool {
        matches!(self, Self::True)
    }

    /// Returns true if value is False.
    #[inline]
    pub fn is_false(self) -> bool {
        matches!(self, Self::False)
    }
}

impl Not for LBool {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Undef => Self::Undef,
        }
    }
}

impl fmt::Display for LBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undef => write!(f, "undef"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
        }
    }
}
