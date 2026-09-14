//! Preprocessing, algebraic rewriting, constant folding, and Tseitin CNF encoding.

pub mod constant_folding;
pub mod rewrite;
pub mod tseitin;

pub use constant_folding::{bv_to_signed, ConstantFolder};
pub use rewrite::Rewriter;
pub use tseitin::TseitinEncoder;
