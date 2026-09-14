//! Specialized theory solvers for CDCL(T) and Nelson-Oppen theory combination:
//! - Equality with Uninterpreted Functions (EUF) Congruence Closure & Equality Engine
//! - Dutertre-de Moura Incremental Dual Simplex for LRA/LIA with strict inequalities (delta infinitesimals)
//! - QF_BV Circuit Bit-Blaster (ripple-carry adders, multipliers, shifters, comparisons)
//! - Theory of Arrays with read-over-write axiom expansion
//! - Centralized Theory Coordinator for CDCL(T) integration.

pub mod array;
pub mod bitvector;
pub mod euf;
pub mod nelson_oppen;
pub mod simplex;
pub mod theory;

pub use array::ArraySolver;
pub use bitvector::BitBlaster;
pub use euf::EufSolver;
pub use nelson_oppen::TheoryCoordinator;
pub use simplex::{Bound, DeltaRational, SimplexSolver};
pub use theory::Theory;
