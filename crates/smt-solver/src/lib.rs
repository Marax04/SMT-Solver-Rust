//! High-level SMT Solver engine coordinating CDCL(T), theory solvers,
//! model generation, unsat core computation, and script execution.

pub mod crypto;
pub mod engine;
pub mod lifter;
pub mod model;
pub mod opaque;
pub mod stats;
pub mod synthesis;
pub mod validator;

pub use crypto::{CryptoAlgorithm, CryptoMatch, CryptoScanner};
pub use engine::{CheckSatResult, ScoreHeuristic, Solver};
pub use lifter::{
    BasicBlock, BranchCondition, BranchResolution, DeobfuscationStatus, IrInstruction, Lifter,
    Operand, ProofCarryingResolution,
};
pub use model::Model;
pub use opaque::{
    FoldedTraceResult, OpaqueClassification, OpaquePredicateAnalyzer, PathConditionFolder,
    TraceBranch,
};
pub use stats::SolverMetrics;
pub use synthesis::{Gf2LinearMbaSimplifier, IoProgramSynthesizer};
pub use validator::ModelValidator;
