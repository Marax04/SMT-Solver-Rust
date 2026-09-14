//! Core foundational types, intermediate representation (IR), hash-consing term arena,
//! sort system, concrete value representations, and diagnostics for the pure Rust SMT solver.

pub mod diagnostics;
pub mod sort;
pub mod term;
pub mod value;

pub use diagnostics::{SmtError, SmtResult, Span};
pub use sort::{Sort, SortArena, SortId};
pub use term::{Op, TermArena, TermData, TermId};
pub use value::Value;
