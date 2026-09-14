//! Top-level SMT-LIB Solver Engine coordinating parsing, theories, SAT, and models.

use crate::model::Model;
use crate::stats::SolverMetrics;
use crate::validator::ModelValidator;
use num_bigint::BigUint;
use smt_core::diagnostics::{SmtError, SmtResult};
use smt_core::sort::{Sort, SortArena, SortId};
use smt_core::term::{Op, TermArena, TermId};
use smt_core::value::Value;
use smt_parser::ast::Command;
use smt_parser::parser::Parser;
use smt_preprocess::{ConstantFolder, Rewriter, TseitinEncoder};
use smt_sat::{LBool, SatSolver};
use smt_theories::bitvector::BitBlaster;
use smt_theories::nelson_oppen::TheoryCoordinator;
use std::collections::HashMap;
use std::fmt;
use std::time::Instant;

/// Result returned by `check-sat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

impl fmt::Display for CheckSatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Heuristic for scoring enumerated models during key recovery and crackme analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScoreHeuristic {
    /// Rewards printable ASCII characters (0x20..=0x7E, \r, \n, \t).
    AsciiPrintable,
    /// Rewards low Shannon entropy (structured strings/keys).
    Entropy,
    /// Favors values with lower Hamming weight (sparse solutions).
    LowHammingWeight,
}

/// The main high-level SMT Solver engine.
pub struct Solver {
    pub sorts: SortArena,
    pub terms: TermArena,
    pub sat: SatSolver,
    pub tseitin: TseitinEncoder,
    assertions: Vec<TermId>,
    scopes: Vec<usize>,
    var_decls: HashMap<String, (TermId, SortId)>,
    last_model: Option<Model>,
    pub logic: Option<String>,
    pub metrics: SolverMetrics,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Creates a new solver instance.
    pub fn new() -> Self {
        let mut sorts = SortArena::new();
        let terms = TermArena::new(&mut sorts);
        Self {
            sorts,
            terms,
            sat: SatSolver::new(),
            tseitin: TseitinEncoder::new(),
            assertions: Vec::with_capacity(256),
            scopes: Vec::with_capacity(16),
            var_decls: HashMap::with_capacity(256),
            last_model: None,
            logic: None,
            metrics: SolverMetrics::default(),
        }
    }

    /// Sets the SMT-LIB logic.
    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_string());
    }

    /// Declares a constant symbol with the given sort.
    pub fn declare_const(&mut self, name: &str, sort: SortId) -> TermId {
        let term = self.terms.var(name, sort);
        self.var_decls.insert(name.to_string(), (term, sort));
        term
    }

    /// Asserts a formula constraint.
    pub fn assert_formula(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Returns the currently active assertions.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Executes `check-sat`.
    pub fn check_sat(&mut self) -> CheckSatResult {
        self.check_sat_assuming(&[])
    }

    /// Executes `check-sat-assuming` under temporary assumption terms.
    pub fn check_sat_assuming(&mut self, assumptions: &[TermId]) -> CheckSatResult {
        let start_time = Instant::now();
        self.last_model = None;

        // 1. Preprocess: fold constants and apply algebraic rewrites
        let mut simplified_assertions = Vec::with_capacity(self.assertions.len());
        for &ast_term in &self.assertions {
            let mut folder = ConstantFolder::new(&mut self.terms, &mut self.sorts);
            let folded = folder.fold_term(ast_term);
            let mut rewriter = Rewriter::new(&mut self.terms, &mut self.sorts);
            let rewritten = rewriter.rewrite(folded);
            simplified_assertions.push(rewritten);
        }

        let mut simplified_assumptions = Vec::with_capacity(assumptions.len());
        for &ast_term in assumptions {
            let mut folder = ConstantFolder::new(&mut self.terms, &mut self.sorts);
            let folded = folder.fold_term(ast_term);
            let mut rewriter = Rewriter::new(&mut self.terms, &mut self.sorts);
            let rewritten = rewriter.rewrite(folded);
            simplified_assumptions.push(rewritten);
        }

        // Trivial UNSAT check
        if simplified_assertions.contains(&self.terms.false_id)
            || simplified_assumptions.contains(&self.terms.false_id)
        {
            self.record_metrics(start_time);
            return CheckSatResult::Unsat;
        }

        let is_qf_bv = self.is_pure_bv_problem();

        let sat_res = if is_qf_bv {
            self.solve_qf_bv(&simplified_assertions, &simplified_assumptions)
        } else {
            self.solve_cdcl_t(&simplified_assertions, &simplified_assumptions)
        };

        self.record_metrics(start_time);

        match sat_res {
            LBool::True => {
                if let Some(ref model) = self.last_model {
                    let mut validator = ModelValidator::new();
                    let mut all_to_verify = self.assertions.clone();
                    all_to_verify.extend_from_slice(assumptions);
                    if validator
                        .validate(&all_to_verify, model, &self.terms, &self.sorts)
                        .is_err()
                    {
                        return CheckSatResult::Unknown;
                    }
                }
                CheckSatResult::Sat
            }
            LBool::False => CheckSatResult::Unsat,
            LBool::Undef => CheckSatResult::Unknown,
        }
    }

    fn solve_qf_bv(&mut self, assertions: &[TermId], assumptions: &[TermId]) -> LBool {
        let mut sat_solver = SatSolver::new();
        let mut bit_blaster = BitBlaster::new(&self.terms, &self.sorts);

        // Bit-blast all assertions
        for &term in assertions {
            let lit = bit_blaster.blast_bool(term, &mut sat_solver);
            sat_solver.add_clause(vec![lit]);
        }

        // Bit-blast assumptions
        let mut assumption_lits = Vec::with_capacity(assumptions.len());
        for &a in assumptions {
            let lit = bit_blaster.blast_bool(a, &mut sat_solver);
            assumption_lits.push(lit);
        }

        let res = sat_solver.solve_with_assumptions(&assumption_lits);

        if res == LBool::True {
            // Reconstruct model
            let mut model = Model::new();
            for (name, &(term, sort)) in &self.var_decls {
                match self.sorts.get(sort) {
                    Sort::Bool => {
                        let bit = bit_blaster.blast_bool(term, &mut sat_solver);
                        let val = sat_solver.model_lit(bit) == LBool::True;
                        model.insert(name, Value::Bool(val));
                    }
                    Sort::BitVec(w) => {
                        let bits = bit_blaster.blast_bv(term, &mut sat_solver);
                        let mut val = BigUint::from(0u32);
                        for (i, &bit) in bits.iter().enumerate() {
                            if sat_solver.model_lit(bit) == LBool::True {
                                val |= BigUint::from(1u32) << i;
                            }
                        }
                        model.insert(
                            name,
                            Value::BitVec {
                                value: val,
                                width: *w,
                            },
                        );
                    }
                    _ => {}
                }
            }
            self.last_model = Some(model);
        }

        self.sat.stats = sat_solver.stats;
        res
    }

    fn solve_cdcl_t(&mut self, assertions: &[TermId], assumptions: &[TermId]) -> LBool {
        let mut sat_solver = SatSolver::new();
        let mut tseitin = TseitinEncoder::new();
        // Array axiom scanning
        let array_axioms = {
            let mut array_solver = smt_theories::ArraySolver::new(&self.sorts);
            for &term in assertions {
                array_solver.scan_term(term, &mut self.terms);
            }
            array_solver.take_pending_axioms()
        };

        let mut coordinator = TheoryCoordinator::new(&self.terms, &self.sorts);
        for ax in array_axioms {
            tseitin.assert_formula(ax, &mut sat_solver, &self.terms);
        }

        // Encode all assertions into SAT clauses
        for &term in assertions {
            tseitin.assert_formula(term, &mut sat_solver, &self.terms);
        }

        // Register all terms and atomic theory constraints
        for id in 0..self.terms.len() {
            let term_id = TermId(id as u32);
            coordinator.euf.register_term(term_id);
            let term = self.terms.get(term_id);
            let sort = self.sorts.get(term.sort);
            if matches!(sort, Sort::Int | Sort::Real) {
                coordinator.register_shared_term(term_id);
            }
            if matches!(
                term.op,
                Op::Eq | Op::Lt | Op::Le | Op::Gt | Op::Ge | Op::Distinct
            ) {
                let lit = tseitin.encode(term_id, &mut sat_solver, &self.terms);
                coordinator.register_lit_term(lit, term_id);
            }
        }

        let mut assumption_lits = Vec::with_capacity(assumptions.len());
        for &a in assumptions {
            let lit = tseitin.encode(a, &mut sat_solver, &self.terms);
            assumption_lits.push(lit);
        }

        let res = sat_solver.solve_with_theory(&mut coordinator, &assumption_lits);

        if res == LBool::True {
            let mut model = Model::new();
            for (name, &(term, sort)) in &self.var_decls {
                match self.sorts.get(sort) {
                    Sort::Bool => {
                        let lit = tseitin.encode(term, &mut sat_solver, &self.terms);
                        let val = sat_solver.model_lit(lit) == LBool::True;
                        model.insert(name, Value::Bool(val));
                    }
                    Sort::Int => {
                        let simplex_var = coordinator.simplex.get_or_create_var(term, true);
                        let val = coordinator.simplex.get_value(simplex_var).c.to_integer();
                        model.insert(name, Value::Int(val));
                    }
                    Sort::Real => {
                        let simplex_var = coordinator.simplex.get_or_create_var(term, false);
                        let val = coordinator.simplex.get_value(simplex_var).c.clone();
                        model.insert(name, Value::Real(val));
                    }
                    _ => {}
                }
            }
            self.last_model = Some(model);
        }

        self.sat.stats = sat_solver.stats;
        res
    }

    fn is_pure_bv_problem(&self) -> bool {
        if let Some(ref l) = self.logic {
            if l != "QF_BV" {
                return false;
            }
        }
        for id in 0..self.terms.len() {
            let term = self.terms.get(TermId(id as u32));
            if matches!(
                term.op,
                Op::Select
                    | Op::Store
                    | Op::Apply(_)
                    | Op::IntConst(_)
                    | Op::RealConst(_)
                    | Op::Add
                    | Op::Sub
                    | Op::Mul
                    | Op::Div
                    | Op::Lt
                    | Op::Le
                    | Op::Gt
                    | Op::Ge
            ) {
                return false;
            }
        }
        true
    }

    fn record_metrics(&mut self, start_time: Instant) {
        self.metrics.wall_clock_ms = start_time.elapsed().as_millis();
        self.metrics.conflicts = self.sat.stats.conflicts;
        self.metrics.decisions = self.sat.stats.decisions;
        self.metrics.propagations = self.sat.stats.propagations;
        self.metrics.restarts = self.sat.stats.restarts;
        self.metrics.clauses_learned = self.sat.stats.clauses_learned;
        self.metrics.clauses_deleted = self.sat.stats.clauses_deleted;
    }

    /// Returns the last computed model if satisfiable.
    pub fn get_model(&self) -> Option<&Model> {
        self.last_model.as_ref()
    }

    /// Pushes `n` scope frames.
    pub fn push(&mut self, n: u32) {
        for _ in 0..n {
            self.scopes.push(self.assertions.len());
            self.sat.push();
        }
    }

    /// Pops `n` scope frames.
    pub fn pop(&mut self, n: u32) {
        for _ in 0..n {
            if let Some(target_len) = self.scopes.pop() {
                self.assertions.truncate(target_len);
                self.sat.pop();
            }
        }
    }

    /// Resets the solver state.
    pub fn reset(&mut self) {
        self.sorts = SortArena::new();
        self.terms = TermArena::new(&mut self.sorts);
        self.sat = SatSolver::new();
        self.tseitin = TseitinEncoder::new();
        self.assertions.clear();
        self.scopes.clear();
        self.var_decls.clear();
        self.last_model = None;
        self.logic = None;
    }

    /// Classifies an opaque branch predicate (`AlwaysTrue`, `AlwaysFalse`, or `Dynamic`).
    pub fn check_opaque(&mut self, predicate: TermId) -> crate::opaque::OpaqueClassification {
        crate::opaque::OpaquePredicateAnalyzer::classify(self, predicate)
    }

    /// Classifies an opaque branch predicate under an accumulated path condition context.
    pub fn check_opaque_contextual(
        &mut self,
        path_condition: &[TermId],
        predicate: TermId,
    ) -> crate::opaque::OpaqueClassification {
        crate::opaque::OpaquePredicateAnalyzer::classify_contextual(self, path_condition, predicate)
    }

    /// Folds path conditions across an execution trace, identifying and eliminating dead control-flow branches.
    pub fn fold_trace(
        &mut self,
        trace: &[crate::opaque::TraceBranch],
    ) -> crate::opaque::FoldedTraceResult {
        crate::opaque::PathConditionFolder::fold_trace(self, trace)
    }

    /// Enumerates distinct models up to `limit` over `target_vars` using iterative blocking clauses.
    /// If `target_vars` is empty, enumerates over all declared variables.
    pub fn enumerate_models(&mut self, target_vars: &[&str], limit: usize) -> Vec<Model> {
        let mut models = Vec::with_capacity(limit);

        let vars_to_block: Vec<String> = if target_vars.is_empty() {
            self.var_decls.keys().cloned().collect()
        } else {
            target_vars.iter().map(|s| s.to_string()).collect()
        };

        while models.len() < limit {
            let res = self.check_sat();
            if res != CheckSatResult::Sat {
                break;
            }

            let model = match self.get_model() {
                Some(m) => m.clone(),
                None => break,
            };

            // Build blocking clause: OR_{v in vars} (v != val(v))
            let mut diffs = Vec::with_capacity(vars_to_block.len());
            for var_name in &vars_to_block {
                if let (Some(&(term, _)), Some(val)) =
                    (self.var_decls.get(var_name), model.get(var_name))
                {
                    let const_term = match val {
                        Value::BitVec { value, width } => {
                            self.terms.bv_const(value.clone(), *width, &mut self.sorts)
                        }
                        Value::Bool(b) => {
                            if *b {
                                self.terms.true_id
                            } else {
                                self.terms.false_id
                            }
                        }
                        Value::Int(i) => self.terms.int_const(i.clone(), &self.sorts),
                        Value::Real(r) => self.terms.real_const(r.clone(), &self.sorts),
                        _ => continue,
                    };
                    let eq = self.terms.eq(term, const_term, &self.sorts);
                    let neq = self.terms.not(eq);
                    diffs.push(neq);
                }
            }

            models.push(model);

            if diffs.is_empty() {
                break;
            }

            let blocking_clause = self.terms.or(diffs, &self.sorts);
            self.assert_formula(blocking_clause);
        }

        models
    }

    /// Enumerates distinct models and ranks them using a decryption/key-recovery scoring heuristic.
    pub fn enumerate_models_scored(
        &mut self,
        target_vars: &[&str],
        limit: usize,
        heuristic: ScoreHeuristic,
    ) -> Vec<(Model, f64)> {
        let models = self.enumerate_models(target_vars, limit);
        let mut scored: Vec<(Model, f64)> = models
            .into_iter()
            .map(|m| {
                let s = Self::score_model(&m, target_vars, heuristic);
                (m, s)
            })
            .collect();

        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        scored
    }

    fn score_model(model: &Model, target_vars: &[&str], heuristic: ScoreHeuristic) -> f64 {
        let mut bytes = Vec::new();
        let mut set_bits = 0usize;
        let mut total_bits = 0usize;

        let var_names: Vec<String> = if target_vars.is_empty() {
            model.keys().cloned().collect()
        } else {
            target_vars.iter().map(|s| s.to_string()).collect()
        };

        for name in &var_names {
            if let Some(Value::BitVec { value, width }) = model.get(name) {
                let b = value.to_bytes_be();
                let expected_bytes = (*width as usize).div_ceil(8);
                if b.len() < expected_bytes {
                    bytes.resize(bytes.len() + (expected_bytes - b.len()), 0);
                }
                bytes.extend_from_slice(&b);
                total_bits += *width as usize;
                for byte in &b {
                    set_bits += byte.count_ones() as usize;
                }
            }
        }

        match heuristic {
            ScoreHeuristic::AsciiPrintable => {
                if bytes.is_empty() {
                    return 0.0;
                }
                let printable = bytes
                    .iter()
                    .filter(|&&b| {
                        (0x20..=0x7E).contains(&b) || b == b'\t' || b == b'\n' || b == b'\r'
                    })
                    .count();
                printable as f64 / bytes.len() as f64
            }
            ScoreHeuristic::LowHammingWeight => {
                if total_bits == 0 {
                    return 0.0;
                }
                1.0 - (set_bits as f64 / total_bits as f64)
            }
            ScoreHeuristic::Entropy => {
                if bytes.is_empty() {
                    return 0.0;
                }
                let mut freq = [0usize; 256];
                for &b in &bytes {
                    freq[b as usize] += 1;
                }
                let len = bytes.len() as f64;
                let mut entropy = 0.0;
                for &cnt in &freq {
                    if cnt > 0 {
                        let p = cnt as f64 / len;
                        entropy -= p * p.log2();
                    }
                }
                (8.0 - entropy).max(0.0) / 8.0
            }
        }
    }

    /// Scans the assertion set for known cryptographic constants, tables, and patterns.
    ///
    /// Implements the correct **normalize-then-scan** pipeline: each asserted term is
    /// first constant-folded so that MBA-obfuscated expressions (e.g., `(x ^ x) + 0x63`)
    /// resolve to their underlying constants before pattern matching. The folded terms are
    /// interned into the arena and therefore visible to `CryptoScanner::scan`.
    pub fn scan_crypto(&mut self) -> Vec<crate::crypto::CryptoMatch> {
        // 1. Normalize every assertion: MBA simplification, algebraic rewrite, followed by constant folding.
        // This resolves MBA-obfuscated expressions (e.g. (x ^ x) + c, (c ^ k) + 2*(c & k) - k)
        // to their underlying values before pattern matching.
        let assertion_ids: Vec<TermId> = self.assertions.clone();
        {
            let mut mba = smt_mba::MbaSimplifier::new();
            for id in &assertion_ids {
                mba.simplify(*id, &mut self.terms, &mut self.sorts);
            }
        }
        {
            let mut rewriter = Rewriter::new(&mut self.terms, &mut self.sorts);
            for id in &assertion_ids {
                rewriter.rewrite(*id);
            }
        }
        {
            let mut folder = ConstantFolder::new(&mut self.terms, &mut self.sorts);
            for id in &assertion_ids {
                folder.fold_term(*id);
            }
        }
        // 2. Scan the (now-enriched) arena for crypto fingerprints.
        crate::crypto::CryptoScanner::scan(&self.terms)
    }

    /// Executes a parsed SMT-LIB command and returns its string response.
    pub fn execute_command(&mut self, cmd: Command) -> SmtResult<String> {
        match cmd {
            Command::SetLogic(l) => {
                self.set_logic(&l);
                Ok(String::new())
            }
            Command::SetInfo(_, _) | Command::SetOption(_, _) => Ok(String::new()),
            Command::DeclareSort(name, _) => {
                self.sorts.uninterpreted(name);
                Ok(String::new())
            }
            Command::DeclareConst(name, sort) => {
                self.declare_const(&name, sort);
                Ok(String::new())
            }
            Command::DeclareFun(name, arg_sorts, ret_sort) => {
                if arg_sorts.is_empty() {
                    self.declare_const(&name, ret_sort);
                }
                Ok(String::new())
            }
            Command::DefineFun(_, _, _, _) => Ok(String::new()),
            Command::Assert(term) => {
                self.assert_formula(term);
                Ok(String::new())
            }
            Command::CheckSat => {
                let res = self.check_sat();
                Ok(format!("{}", res))
            }
            Command::CheckSatAssuming(props) => {
                let res = self.check_sat_assuming(&props);
                Ok(format!("{}", res))
            }
            Command::GetModel => {
                if let Some(model) = self.get_model() {
                    Ok(format!("{}", model))
                } else {
                    Err(SmtError::InvalidState {
                        reason: "Cannot get-model when result is not SAT".to_string(),
                    })
                }
            }
            Command::GetUnsatCore => Ok("()".to_string()),
            Command::GetValue(_) => Ok("()".to_string()),
            Command::Push(n) => {
                self.push(n);
                Ok(String::new())
            }
            Command::Pop(n) => {
                self.pop(n);
                Ok(String::new())
            }
            Command::Reset => {
                self.reset();
                Ok(String::new())
            }
            Command::Exit => Ok(String::new()),
        }
    }

    /// Executes an entire SMT-LIB script string and returns the collected outputs.
    pub fn execute_script(&mut self, input: &str) -> SmtResult<Vec<String>> {
        let mut parser = Parser::new(&mut self.sorts, &mut self.terms);
        let commands = parser.parse_script(input)?;
        let mut outputs = Vec::new();

        for cmd in commands {
            let out = self.execute_command(cmd)?;
            if !out.is_empty() {
                outputs.push(out);
            }
        }

        Ok(outputs)
    }
}
