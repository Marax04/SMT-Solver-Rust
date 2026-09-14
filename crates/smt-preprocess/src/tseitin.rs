//! Tseitin Transformation for CNF formula synthesis.

use smt_core::term::{Op, TermArena, TermId};
use smt_sat::{Lit, SatSolver};
use std::collections::HashMap;

/// Tseitin CNF encoder mapping boolean DAG terms into SAT clauses.
#[derive(Debug, Clone, Default)]
pub struct TseitinEncoder {
    term_to_lit: HashMap<TermId, Lit>,
    lit_to_term: HashMap<Lit, TermId>,
    pub true_lit: Option<Lit>,
}

impl TseitinEncoder {
    /// Creates a new encoder.
    pub fn new() -> Self {
        Self {
            term_to_lit: HashMap::with_capacity(1024),
            lit_to_term: HashMap::with_capacity(1024),
            true_lit: None,
        }
    }

    /// Returns the true literal, creating it if not already initialized.
    pub fn get_true_lit(&mut self, solver: &mut SatSolver) -> Lit {
        if let Some(l) = self.true_lit {
            return l;
        }
        let v = solver.new_var();
        let lit = v.to_lit();
        solver.add_clause(vec![lit]);
        self.true_lit = Some(lit);
        lit
    }

    /// Retrieves the term associated with a SAT literal, if registered.
    pub fn term_of_lit(&self, lit: Lit) -> Option<TermId> {
        self.lit_to_term.get(&lit).copied()
    }

    /// Asserts a top-level boolean constraint into the SAT solver.
    pub fn assert_formula(&mut self, id: TermId, solver: &mut SatSolver, arena: &TermArena) {
        if let Op::And = arena.op_of(id) {
            for &arg in arena.args_of(id) {
                self.assert_formula(arg, solver, arena);
            }
            return;
        }

        let lit = self.encode(id, solver, arena);
        solver.add_clause(vec![lit]);
    }

    /// Recursively encodes a boolean term as an equisatisfiable literal.
    pub fn encode(&mut self, id: TermId, solver: &mut SatSolver, arena: &TermArena) -> Lit {
        if let Some(&lit) = self.term_to_lit.get(&id) {
            return lit;
        }

        let term = arena.get(id);
        let lit = match &term.op {
            Op::True => self.get_true_lit(solver),
            Op::False => !self.get_true_lit(solver),
            Op::Not => {
                let inner = self.encode(term.args[0], solver, arena);
                !inner
            }
            Op::And => {
                let v = solver.new_var();
                let p = v.to_lit();
                let arg_lits: Vec<Lit> = term.args.iter().map(|&a| self.encode(a, solver, arena)).collect();

                // p => a_i  ==>  (!p or a_i)
                for &a in &arg_lits {
                    solver.add_clause(vec![!p, a]);
                }
                // (a_1 and ... and a_n) => p  ==>  (!a_1 or ... or !a_n or p)
                let mut big_clause: Vec<Lit> = arg_lits.iter().map(|&a| !a).collect();
                big_clause.push(p);
                solver.add_clause(big_clause);

                p
            }
            Op::Or => {
                let v = solver.new_var();
                let p = v.to_lit();
                let arg_lits: Vec<Lit> = term.args.iter().map(|&a| self.encode(a, solver, arena)).collect();

                // a_i => p  ==>  (!a_i or p)
                for &a in &arg_lits {
                    solver.add_clause(vec![!a, p]);
                }
                // p => (a_1 or ... or a_n)  ==>  (!p or a_1 or ... or a_n)
                let mut big_clause: Vec<Lit> = arg_lits;
                big_clause.push(!p);
                solver.add_clause(big_clause);

                p
            }
            Op::Xor => {
                let v = solver.new_var();
                let p = v.to_lit();
                let a = self.encode(term.args[0], solver, arena);
                let b = self.encode(term.args[1], solver, arena);

                // p <=> (a xor b)
                solver.add_clause(vec![!p, a, b]);
                solver.add_clause(vec![!p, !a, !b]);
                solver.add_clause(vec![p, !a, b]);
                solver.add_clause(vec![p, a, !b]);

                p
            }
            Op::Implies => {
                let v = solver.new_var();
                let p = v.to_lit();
                let a = self.encode(term.args[0], solver, arena);
                let b = self.encode(term.args[1], solver, arena);

                // p <=> (!a or b)
                solver.add_clause(vec![!p, !a, b]);
                solver.add_clause(vec![p, a]);
                solver.add_clause(vec![p, !b]);

                p
            }
            Op::Ite => {
                let v = solver.new_var();
                let p = v.to_lit();
                let c = self.encode(term.args[0], solver, arena);
                let t = self.encode(term.args[1], solver, arena);
                let e = self.encode(term.args[2], solver, arena);

                // c => (p <=> t)
                solver.add_clause(vec![!c, !t, p]);
                solver.add_clause(vec![!c, t, !p]);
                // !c => (p <=> e)
                solver.add_clause(vec![c, !e, p]);
                solver.add_clause(vec![c, e, !p]);

                p
            }
            // All other operations (atomic boolean variables, theory atoms, comparisons, equalities)
            _ => {
                let v = solver.new_var();
                v.to_lit()
            }
        };

        self.term_to_lit.insert(id, lit);
        self.lit_to_term.insert(lit, id);
        lit
    }
}
