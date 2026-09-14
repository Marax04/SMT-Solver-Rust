//! High-performance CDCL Boolean SAT Solver Core with Two-Watched Literals (2WL),
//! 1-UIP conflict analysis, Glucose-style adaptive LBD restarts, VSIDS branching,
//! DRAT proof generation, and bidirectional CDCL(T) theory integration.

pub mod clause;
pub mod drat;
pub mod drat_checker;
pub mod lit;
pub mod restart;
pub mod solver;
pub mod theory;
pub mod trail;
pub mod vsids;
pub mod watch;

pub use clause::{Clause, ClauseArena, ClauseId};
pub use drat::DratProof;
pub use drat_checker::{DratChecker, DratVerificationResult};
pub use lit::{LBool, Lit, Var};
pub use restart::RestartStrategy;
pub use solver::{SatSolver, SolverStats};
pub use theory::{NoOpTheory, TheoryCallback};
pub use trail::{Reason, Trail, VarData};
pub use vsids::Vsids;
pub use watch::{WatchList, Watcher};
