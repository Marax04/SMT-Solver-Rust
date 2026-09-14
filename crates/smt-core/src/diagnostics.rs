//! Diagnostics and structured error types for the SMT solver pipeline.

use std::fmt;

/// Source code location span for reporting diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// 1-based line number.
    pub line: usize,
    /// 1-based column number.
    pub col: usize,
}

impl Span {
    /// Creates a new span.
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }

    /// Default dummy span for synthetic terms.
    pub fn dummy() -> Self {
        Self { line: 1, col: 1 }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// Structured error categories according to the architectural specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtError {
    /// Syntax or lexical error encountered during parsing.
    Parse { message: String, span: Span },
    /// Static sort / type mismatch error.
    Type {
        expected: String,
        found: String,
        context: String,
    },
    /// Incompatible or unsupported logic feature requested.
    UnsupportedLogic { feature: String },
    /// Solver state error (e.g. invalid push/pop stack operation).
    InvalidState { reason: String },
    /// Resource limit exceeded (timeout or memory limit).
    ResourceExhausted { detail: String },
    /// General system or IO failure.
    Internal { details: String },
}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse { message, span } => write!(f, "Parse error at {}: {}", span, message),
            Self::Type {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "Type mismatch in {}: expected {}, found {}",
                    context, expected, found
                )
            }
            Self::UnsupportedLogic { feature } => {
                write!(f, "Unsupported logic feature: {}", feature)
            }
            Self::InvalidState { reason } => write!(f, "Invalid solver state: {}", reason),
            Self::ResourceExhausted { detail } => write!(f, "Resource exhausted: {}", detail),
            Self::Internal { details } => write!(f, "Internal solver error: {}", details),
        }
    }
}

impl std::error::Error for SmtError {}

/// Standard result alias across the solver.
pub type SmtResult<T> = Result<T, SmtError>;
