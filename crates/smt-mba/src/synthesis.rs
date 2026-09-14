//! I/O-guided program synthesis engine (Syntia / MCTS style) with SMT oracle verification.

use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_core::value::Value;
use smt_solver::engine::{CheckSatResult, Solver};
use smt_solver::model::Model;
use smt_solver::validator::ModelValidator;

/// Program Synthesizer using concrete I/O observation and SMT verification.
pub struct IoProgramSynthesizer;

impl IoProgramSynthesizer {
    /// Attempts to synthesize a smaller equivalent term for `term_id`.
    pub fn synthesize(
        term_id: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> Option<TermId> {
        let mut vars = Vec::new();
        Self::collect_vars(term_id, terms, &mut vars);
        if vars.len() != 2 {
            return None;
        }

        let x = vars[0];
        let y = vars[1];
        let x_name = match &terms.get(x).op {
            Op::Var(s) => s.clone(),
            _ => return None,
        };
        let y_name = match &terms.get(y).op {
            Op::Var(s) => s.clone(),
            _ => return None,
        };

        // 1. Collect concrete I/O samples
        let samples: [(u32, u32); 8] = [
            (0, 0),
            (1, 0),
            (0, 1),
            (1, 1),
            (5, 7),
            (42, 13),
            (255, 128),
            (100, 200),
        ];

        let mut outputs = Vec::with_capacity(samples.len());
        for &(sx, sy) in &samples {
            let mut model = Model::new();
            model.insert(&x_name, Value::new_bv(sx.into(), 32));
            model.insert(&y_name, Value::new_bv(sy.into(), 32));

            let mut validator = ModelValidator::new();
            let val = validator.evaluate(term_id, &model, terms, sorts).ok()?;
            outputs.push(val);
        }

        // 2. Candidate pool of simplified terms
        let candidates = vec![
            terms.bv_binop(Op::BvAdd, x, y).ok()?,
            terms.bv_binop(Op::BvSub, x, y).ok()?,
            terms.bv_binop(Op::BvSub, y, x).ok()?,
            terms.bv_binop(Op::BvXor, x, y).ok()?,
            terms.bv_binop(Op::BvAnd, x, y).ok()?,
            terms.bv_binop(Op::BvOr, x, y).ok()?,
            x,
            y,
        ];

        // 3. Filter candidates against all I/O samples
        for cand in candidates {
            if cand == term_id {
                continue;
            }

            let mut all_match = true;
            for (idx, &(sx, sy)) in samples.iter().enumerate() {
                let mut model = Model::new();
                model.insert(&x_name, Value::new_bv(sx.into(), 32));
                model.insert(&y_name, Value::new_bv(sy.into(), 32));

                let mut validator = ModelValidator::new();
                if let Ok(cand_val) = validator.evaluate(cand, &model, terms, sorts) {
                    if cand_val != outputs[idx] {
                        all_match = false;
                        break;
                    }
                } else {
                    all_match = false;
                    break;
                }
            }

            if all_match {
                // 4. Verify formal equivalence with SMT solver oracle
                if Self::verify_equivalence(term_id, cand, terms, sorts) {
                    return Some(cand);
                }
            }
        }

        None
    }

    /// Verifies that `a <=> b` for all inputs using an SMT oracle (asserting a != b is UNSAT).
    fn verify_equivalence(
        a: TermId,
        b: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> bool {
        let mut solver = Solver::new();
        solver.sorts = sorts.clone();
        solver.terms = terms.clone();
        solver.set_logic("QF_BV");

        let neq = solver.terms.distinct(vec![a, b], &solver.sorts);
        solver.assert_formula(neq);
        solver.check_sat() == CheckSatResult::Unsat
    }

    fn collect_vars(term_id: TermId, terms: &TermArena, vars: &mut Vec<TermId>) {
        let term = terms.get(term_id);
        if matches!(term.op, Op::Var(_)) {
            if !vars.contains(&term_id) {
                vars.push(term_id);
            }
            return;
        }
        for &arg in &term.args {
            Self::collect_vars(arg, terms, vars);
        }
    }
}
