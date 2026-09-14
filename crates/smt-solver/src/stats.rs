//! Solver observability metrics and structured statistics.

/// Execution metrics gathered during solving.
#[derive(Debug, Clone, Default)]
pub struct SolverMetrics {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub clauses_learned: u64,
    pub clauses_deleted: u64,
    pub wall_clock_ms: u128,
}

impl SolverMetrics {
    /// Formats metrics as a structured JSON string.
    pub fn to_json(&self) -> String {
        format!(
            "{{\n  \"conflicts\": {},\n  \"decisions\": {},\n  \"propagations\": {},\n  \"restarts\": {},\n  \"clauses_learned\": {},\n  \"clauses_deleted\": {},\n  \"wall_clock_ms\": {}\n}}",
            self.conflicts,
            self.decisions,
            self.propagations,
            self.restarts,
            self.clauses_learned,
            self.clauses_deleted,
            self.wall_clock_ms
        )
    }
}
