//! Opaque predicate classification and path-condition folding engine for binary deobfuscation.
//!
//! Classifies branch predicates into:
//! - AlwaysTrue: Invariant/contextual branch always taken (dead false branch can be eliminated)
//! - AlwaysFalse: Invariant/contextual branch never taken (dead true branch can be eliminated)
//! - Dynamic: Dependent on program inputs (genuine conditional branch)
//! - Unreachable: The contextual path condition itself is unsatisfiable (dead code block)
//! - Unknown: Solver timeout or incomplete theory reasoning

use crate::engine::{CheckSatResult, Solver};
use smt_core::term::TermId;

/// Classification of a candidate opaque branch condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpaqueClassification {
    /// The predicate is invariant/contextually implied and always evaluates to `true`.
    AlwaysTrue,
    /// The predicate is invariant/contextually contradictory and always evaluates to `false`.
    AlwaysFalse,
    /// The predicate is dynamic and can evaluate to both `true` and `false` in this context.
    Dynamic,
    /// The path condition leading to this predicate is itself contradictory (unreachable code).
    Unreachable,
    /// The solver could not definitively prove invariance or dynamism.
    Unknown,
}

/// Analyzer for detecting and classifying opaque predicates in decompiled/disassembled code.
pub struct OpaquePredicateAnalyzer;

impl OpaquePredicateAnalyzer {
    /// Classifies whether an isolated boolean term `predicate` is an invariant opaque condition.
    pub fn classify(solver: &mut Solver, predicate: TermId) -> OpaqueClassification {
        Self::classify_contextual(solver, &[], predicate)
    }

    /// Classifies whether a boolean term `predicate` is an opaque condition under an accumulated `path_condition`.
    pub fn classify_contextual(
        solver: &mut Solver,
        path_condition: &[TermId],
        predicate: TermId,
    ) -> OpaqueClassification {
        let not_p = solver.terms.not(predicate);

        // 0. Verify if path condition is itself satisfiable
        if !path_condition.is_empty() {
            let res_pc = solver.check_sat_assuming(path_condition);
            if res_pc == CheckSatResult::Unsat {
                return OpaqueClassification::Unreachable;
            }
        }

        // 1. Check if PC AND NOT(P) is unsatisfiable -> If so, PC => P is valid (AlwaysTrue)
        let mut assumptions_not = Vec::with_capacity(path_condition.len() + 1);
        assumptions_not.extend_from_slice(path_condition);
        assumptions_not.push(not_p);
        let res_not = solver.check_sat_assuming(&assumptions_not);
        if res_not == CheckSatResult::Unsat {
            return OpaqueClassification::AlwaysTrue;
        }

        // 2. Check if PC AND P is unsatisfiable -> If so, PC => NOT(P) is valid (AlwaysFalse)
        let mut assumptions_p = Vec::with_capacity(path_condition.len() + 1);
        assumptions_p.extend_from_slice(path_condition);
        assumptions_p.push(predicate);
        let res_p = solver.check_sat_assuming(&assumptions_p);
        if res_p == CheckSatResult::Unsat {
            return OpaqueClassification::AlwaysFalse;
        }

        // 3. If both branches are satisfiable under PC, it is a genuine dynamic conditional branch
        if res_not == CheckSatResult::Sat && res_p == CheckSatResult::Sat {
            return OpaqueClassification::Dynamic;
        }

        OpaqueClassification::Unknown
    }
}

/// Branch action recorded along an execution trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceBranch {
    /// Identifier of the basic block containing the branch instruction.
    pub block_id: u32,
    /// SMT boolean term representing the branch condition (e.g. flag test, comparison).
    pub predicate: TermId,
    /// Whether the branch was taken (`true`) or fallen through (`false`).
    pub taken: bool,
}

/// Result of folding path conditions over a control-flow trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldedTraceResult {
    /// Basic blocks verified to be reachable.
    pub reachable_blocks: Vec<u32>,
    /// Dead branch edges eliminated by opaque predicate resolution: (block_id, dead_branch_direction).
    pub eliminated_dead_edges: Vec<(u32, bool)>,
    /// Opaque classifications discovered per block: (block_id, classification).
    pub classifications: Vec<(u32, OpaqueClassification)>,
}

/// Path Condition Folding Engine pruning dead control-flow branches across execution traces.
pub struct PathConditionFolder;

impl PathConditionFolder {
    /// Walks a linear execution trace, accumulates path conditions, simplifies branches,
    /// and prunes dead control flow edges.
    pub fn fold_trace(solver: &mut Solver, trace: &[TraceBranch]) -> FoldedTraceResult {
        let mut accumulated_pc: Vec<TermId> = Vec::with_capacity(trace.len());
        let mut reachable_blocks = Vec::with_capacity(trace.len());
        let mut eliminated_dead_edges = Vec::new();
        let mut classifications = Vec::with_capacity(trace.len());

        for branch in trace {
            let class = OpaquePredicateAnalyzer::classify_contextual(
                solver,
                &accumulated_pc,
                branch.predicate,
            );
            classifications.push((branch.block_id, class));

            match class {
                OpaqueClassification::AlwaysTrue => {
                    reachable_blocks.push(branch.block_id);
                    // The false (not taken) edge is dead code
                    eliminated_dead_edges.push((branch.block_id, false));
                    // Add predicate to path condition
                    accumulated_pc.push(branch.predicate);
                }
                OpaqueClassification::AlwaysFalse => {
                    reachable_blocks.push(branch.block_id);
                    // The true (taken) edge is dead code
                    eliminated_dead_edges.push((branch.block_id, true));
                    // Add negated predicate to path condition
                    let not_p = solver.terms.not(branch.predicate);
                    accumulated_pc.push(not_p);
                }
                OpaqueClassification::Dynamic => {
                    reachable_blocks.push(branch.block_id);
                    let assumed = if branch.taken {
                        branch.predicate
                    } else {
                        solver.terms.not(branch.predicate)
                    };
                    accumulated_pc.push(assumed);
                }
                OpaqueClassification::Unreachable => {
                    // Block is completely unreachable given prior path constraints
                    break;
                }
                OpaqueClassification::Unknown => {
                    reachable_blocks.push(branch.block_id);
                    let assumed = if branch.taken {
                        branch.predicate
                    } else {
                        solver.terms.not(branch.predicate)
                    };
                    accumulated_pc.push(assumed);
                }
            }
        }

        FoldedTraceResult {
            reachable_blocks,
            eliminated_dead_edges,
            classifications,
        }
    }
}
