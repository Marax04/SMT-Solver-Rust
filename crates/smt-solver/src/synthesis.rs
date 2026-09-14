//! I/O-guided program synthesis engine (Syntia / MCTS style) with SMT oracle verification.
//!
//! Separated into `smt-solver` to break the cyclic dependency with `smt-mba` (algebra).
//! Now `smt-mba` is 100% pure algebra, and `smt-solver` provides the SMT oracle for synthesis.

use crate::engine::{CheckSatResult, Solver};
use crate::model::Model;
use crate::validator::ModelValidator;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_core::value::Value;

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
    /// Scales to arbitrary bit-widths (e.g. 32-bit, 64-bit registers) where truth table enumeration is impossible.
    pub fn verify_equivalence(
        a: TermId,
        b: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> bool {
        Self::verify_equivalence_with_counterexample(a, b, terms, sorts).is_ok()
    }

    /// Formally checks equivalence `a <=> b`.
    /// - If equivalent, returns `Ok(())` (certified UNSAT for distinct(a, b)).
    /// - If non-equivalent, returns `Err(counterexample)` with concrete variable assignments disproving equivalence.
    pub fn verify_equivalence_with_counterexample(
        a: TermId,
        b: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> Result<(), Model> {
        let mut solver = Solver::new();
        solver.sorts = sorts.clone();
        solver.terms = terms.clone();
        solver.set_logic("QF_BV");

        let mut vars = Vec::new();
        Self::collect_vars(a, &solver.terms, &mut vars);
        Self::collect_vars(b, &solver.terms, &mut vars);
        let mut decls = Vec::new();
        for &v in &vars {
            if let Op::Var(ref name) = solver.terms.get(v).op {
                let sort = solver.terms.sort_of(v);
                decls.push((name.clone(), sort));
            }
        }
        for (name, sort) in decls {
            solver.declare_const(&name, sort);
        }

        let neq = solver.terms.distinct(vec![a, b], &solver.sorts);
        solver.assert_formula(neq);
        match solver.check_sat() {
            CheckSatResult::Unsat => Ok(()),
            CheckSatResult::Sat => {
                let model = solver.get_model().cloned().unwrap_or_default();
                Err(model)
            }
            CheckSatResult::Unknown => Err(solver.get_model().cloned().unwrap_or_default()),
        }
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

/// Multi-variable Linear MBA simplifier combining random sampling with SMT oracle verification.
pub struct Gf2LinearMbaSimplifier;

impl Gf2LinearMbaSimplifier {
    /// Attempts to simplify multi-variable MBA expressions (5-8+ variables).
    pub fn simplify(
        term_id: TermId,
        terms: &mut TermArena,
        sorts: &mut SortArena,
    ) -> Option<TermId> {
        let mut vars = Vec::new();
        Self::collect_vars(term_id, terms, &mut vars);
        if vars.is_empty() {
            return None;
        }

        let mut var_names = Vec::with_capacity(vars.len());
        for &v in &vars {
            if let Op::Var(ref s) = terms.get(v).op {
                var_names.push(s.clone());
            } else {
                return None;
            }
        }

        // Generate M pseudo-random sample points
        let num_samples = 32.max(vars.len() * 4);
        let mut samples: Vec<Vec<u32>> = Vec::with_capacity(num_samples);
        let mut seed = 0x1337c0de_u32;
        for _ in 0..num_samples {
            let mut pt = Vec::with_capacity(vars.len());
            for _ in 0..vars.len() {
                seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
                pt.push(seed & 0xff);
            }
            samples.push(pt);
        }

        // Evaluate target term on all samples
        let mut target_vals = Vec::with_capacity(num_samples);
        for pt in &samples {
            let mut model = Model::new();
            for (v_idx, name) in var_names.iter().enumerate() {
                model.insert(name, Value::new_bv(pt[v_idx].into(), 32));
            }
            let mut validator = ModelValidator::new();
            let val = validator.evaluate(term_id, &model, terms, sorts).ok()?;
            match val {
                Value::BitVec { value, .. } => target_vals.push(value),
                _ => return None,
            }
        }

        // Candidate basis pool: individual variables, pairwise additions, XORs, ANDs
        let mut candidates = Vec::new();
        for &v in &vars {
            candidates.push(v);
        }
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if let Ok(cand) = terms.bv_binop(Op::BvAdd, vars[i], vars[j]) {
                    candidates.push(cand);
                }
                if let Ok(cand) = terms.bv_binop(Op::BvXor, vars[i], vars[j]) {
                    candidates.push(cand);
                }
                if let Ok(cand) = terms.bv_binop(Op::BvSub, vars[i], vars[j]) {
                    candidates.push(cand);
                }
                if let Ok(cand) = terms.bv_binop(Op::BvSub, vars[j], vars[i]) {
                    candidates.push(cand);
                }
            }
        }

        // Check if any single candidate matches exactly on all samples
        for &cand in &candidates {
            if cand == term_id {
                continue;
            }
            let mut matches = true;
            for (pt_idx, pt) in samples.iter().enumerate() {
                let mut model = Model::new();
                for (v_idx, name) in var_names.iter().enumerate() {
                    model.insert(name, Value::new_bv(pt[v_idx].into(), 32));
                }
                let mut validator = ModelValidator::new();
                if let Ok(Value::BitVec { value, .. }) =
                    validator.evaluate(cand, &model, terms, sorts)
                {
                    if value != target_vals[pt_idx] {
                        matches = false;
                        break;
                    }
                } else {
                    matches = false;
                    break;
                }
            }

            if matches && IoProgramSynthesizer::verify_equivalence(term_id, cand, terms, sorts) {
                return Some(cand);
            }
        }

        None
    }

    fn collect_vars(term_id: TermId, terms: &TermArena, vars: &mut Vec<TermId>) {
        let mut visited = std::collections::HashSet::new();
        let mut stack = vec![term_id];
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            let term = terms.get(id);
            if matches!(term.op, Op::Var(_)) {
                if !vars.contains(&id) {
                    vars.push(id);
                }
            } else {
                for &arg in &term.args {
                    stack.push(arg);
                }
            }
        }
    }
}
