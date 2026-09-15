//! High-level SMT Solver engine coordinating CDCL(T), theory solvers,
//! model generation, unsat core computation, and script execution.

pub mod binary_loader;
pub mod cache;
pub mod crypto;
pub mod engine;
pub mod explain;
pub mod lifter;
pub mod model;
pub mod opaque;
pub mod provenance;
pub mod replay;
pub mod stats;
pub mod synthesis;
pub mod validator;
pub mod x86_decoder;

pub use binary_loader::{
    BinaryFormat, BinaryLoader, Elf64File, Elf64ProgramHeader, Elf64Section, LoadedProcessImage,
    LoaderError, MemorySegment, Pe64File, PeDataDirectory, PeImport, PeRelocationBlock, PeSection,
    PeTlsDirectory,
};
pub use cache::{CachedFormulaResult, PersistentCache};
pub use crypto::{CryptoAlgorithm, CryptoMatch, CryptoScanner};
pub use engine::{CheckSatResult, ScoreHeuristic, Solver};
pub use explain::DeobfuscationExplainer;
pub use lifter::{
    BasicBlock, BranchCondition, BranchResolution, DeobfuscationStatus, IrInstruction, Lifter,
    Operand, ProofCarryingResolution,
};
pub use model::Model;
pub use opaque::{
    FoldedTraceResult, OpaqueClassification, OpaquePredicateAnalyzer, PathConditionFolder,
    TraceBranch,
};
pub use provenance::BlockProvenanceArtifact;
pub use replay::{ReplayEngine, ReplayVerification};
pub use stats::SolverMetrics;
pub use synthesis::{
    EquivalenceMetadata, EquivalenceResult, Gf2LinearMbaSimplifier, IoProgramSynthesizer,
};
pub use validator::ModelValidator;
pub use x86_decoder::{DecodedInstruction, X86Decoder};
