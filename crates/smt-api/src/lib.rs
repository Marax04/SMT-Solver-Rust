//! Programmatic Rust Builder API, C-ABI bindings, and WASM integration.

pub mod c_api;
pub mod fluent;

pub use c_api::*;
pub use fluent::{Context, Expr, FluentSolver};
