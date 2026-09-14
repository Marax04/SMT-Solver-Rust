//! Complete QF_BV Circuit Bit-Blaster for SMT-LIB bit-vectors.

use num_bigint::BigUint;
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_sat::{Lit, SatSolver};
use std::collections::HashMap;

/// Circuit Bit-Blaster translating bit-vector AST operations into boolean SAT gates.
#[derive(Debug, Clone)]
pub struct BitBlaster<'a> {
    pub arena: &'a TermArena,
    pub sorts: &'a SortArena,
    /// Cache of bit-blasted terms: TermId -> list of Lits (LSB at index 0).
    term_bits: HashMap<TermId, Vec<Lit>>,
    bool_cache: HashMap<TermId, Lit>,
    var_lits: HashMap<String, Lit>,
    true_lit: Option<Lit>,
}

impl<'a> BitBlaster<'a> {
    /// Creates a bit-blaster.
    pub fn new(arena: &'a TermArena, sorts: &'a SortArena) -> Self {
        Self {
            arena,
            sorts,
            term_bits: HashMap::with_capacity(1024),
            bool_cache: HashMap::with_capacity(1024),
            var_lits: HashMap::with_capacity(256),
            true_lit: None,
        }
    }

    /// Gets or creates a constant true SAT literal.
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

    /// Bit-blasts a bit-vector term into a vector of SAT literals representing its bits.
    pub fn blast_bv(&mut self, id: TermId, solver: &mut SatSolver) -> Vec<Lit> {
        if let Some(bits) = self.term_bits.get(&id) {
            return bits.clone();
        }

        let term = self.arena.get(id);
        let width = match self.sorts.get(term.sort) {
            smt_core::sort::Sort::BitVec(w) => (*w).min(smt_core::sort::MAX_BV_WIDTH) as usize,
            _ => 1,
        };

        let bits = match &term.op {
            Op::BvConst { value, .. } => {
                let true_l = self.get_true_lit(solver);
                let mut res = Vec::with_capacity(width);
                for i in 0..width {
                    let bit = (value >> i) & BigUint::from(1u32);
                    if bit == BigUint::from(1u32) {
                        res.push(true_l);
                    } else {
                        res.push(!true_l);
                    }
                }
                res
            }
            Op::Var(_) => {
                let mut res = Vec::with_capacity(width);
                for _ in 0..width {
                    let v = solver.new_var();
                    res.push(v.to_lit());
                }
                res
            }
            Op::BvNot => {
                let a_bits = self.blast_bv(term.args[0], solver);
                a_bits.into_iter().map(|b| !b).collect()
            }
            Op::BvAnd => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.gate_and_vec(&a_bits, &b_bits, solver)
            }
            Op::BvOr => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.gate_or_vec(&a_bits, &b_bits, solver)
            }
            Op::BvXor => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.gate_xor_vec(&a_bits, &b_bits, solver)
            }
            Op::BvAdd => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_adder(&a_bits, &b_bits, solver)
            }
            Op::BvSub => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_subtractor(&a_bits, &b_bits, solver)
            }
            Op::BvNeg => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let not_a: Vec<Lit> = a_bits.iter().map(|&b| !b).collect();
                let true_l = self.get_true_lit(solver);
                let mut one_bits = vec![!true_l; width];
                one_bits[0] = true_l;
                self.circuit_adder(&not_a, &one_bits, solver)
            }
            Op::BvMul => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_multiplier(&a_bits, &b_bits, solver)
            }
            Op::BvConcat => {
                // SMT-LIB (concat a b) has a as high bits and b as low bits
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let mut res = b_bits;
                res.extend(a_bits);
                res
            }
            Op::BvExtract { high, low } => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let h = *high as usize;
                let l = *low as usize;
                a_bits[l..=h].to_vec()
            }
            Op::BvShl => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_shl(&a_bits, &b_bits, solver)
            }
            Op::BvLshr => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_lshr(&a_bits, &b_bits, solver)
            }
            Op::BvAshr => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_ashr(&a_bits, &b_bits, solver)
            }
            Op::BvUdiv => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let (q, _) = self.circuit_udiv_urem(&a_bits, &b_bits, solver);
                q
            }
            Op::BvUrem => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let (_, r) = self.circuit_udiv_urem(&a_bits, &b_bits, solver);
                r
            }
            Op::BvSdiv => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_sdiv(&a_bits, &b_bits, solver)
            }
            Op::BvSrem => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_srem(&a_bits, &b_bits, solver)
            }
            Op::BvSmod => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_smod(&a_bits, &b_bits, solver)
            }
            Op::BvNand => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let and_bits = self.gate_and_vec(&a_bits, &b_bits, solver);
                and_bits.into_iter().map(|b| !b).collect()
            }
            Op::BvNor => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let or_bits = self.gate_or_vec(&a_bits, &b_bits, solver);
                or_bits.into_iter().map(|b| !b).collect()
            }
            Op::BvXnor => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let xor_bits = self.gate_xor_vec(&a_bits, &b_bits, solver);
                xor_bits.into_iter().map(|b| !b).collect()
            }
            Op::BvZeroExtend(n) => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let false_l = !self.get_true_lit(solver);
                let mut res = a_bits;
                for _ in 0..*n {
                    res.push(false_l);
                }
                res
            }
            Op::BvSignExtend(n) => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let sign_bit = *a_bits.last().unwrap_or(&!self.get_true_lit(solver));
                let mut res = a_bits;
                for _ in 0..*n {
                    res.push(sign_bit);
                }
                res
            }
            Op::BvRotateLeft(n) => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let len = a_bits.len();
                if len == 0 {
                    a_bits
                } else {
                    let rot = (*n as usize) % len;
                    let mut res = vec![!self.get_true_lit(solver); len];
                    for i in 0..len {
                        res[(i + rot) % len] = a_bits[i];
                    }
                    res
                }
            }
            Op::BvRotateRight(n) => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let len = a_bits.len();
                if len == 0 {
                    a_bits
                } else {
                    let rot = (*n as usize) % len;
                    let mut res = vec![!self.get_true_lit(solver); len];
                    for i in 0..len {
                        res[i] = a_bits[(i + rot) % len];
                    }
                    res
                }
            }
            Op::BvRepeat(n) => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let mut res = Vec::with_capacity(a_bits.len() * (*n as usize));
                for _ in 0..*n {
                    res.extend_from_slice(&a_bits);
                }
                res
            }
            Op::Ite => {
                let cond_lit = self.blast_bool(term.args[0], solver);
                let then_bits = self.blast_bv(term.args[1], solver);
                let else_bits = self.blast_bv(term.args[2], solver);
                let mut res = Vec::with_capacity(width);
                for i in 0..width {
                    res.push(self.gate_ite(cond_lit, then_bits[i], else_bits[i], solver));
                }
                res
            }
            _ => {
                // Fallback for uninterpreted bitvector terms
                let mut res = Vec::with_capacity(width);
                for _ in 0..width {
                    let v = solver.new_var();
                    res.push(v.to_lit());
                }
                res
            }
        };

        self.term_bits.insert(id, bits.clone());
        bits
    }

    /// Bit-blasts a boolean comparison or predicate into a single SAT literal.
    pub fn blast_bool(&mut self, id: TermId, solver: &mut SatSolver) -> Lit {
        if let Some(&cached) = self.bool_cache.get(&id) {
            return cached;
        }

        let term = self.arena.get(id);
        let lit = match &term.op {
            Op::True => self.get_true_lit(solver),
            Op::False => !self.get_true_lit(solver),
            Op::Var(name) => {
                if let Some(&v_lit) = self.var_lits.get(name) {
                    v_lit
                } else {
                    let v = solver.new_var();
                    let v_lit = v.to_lit();
                    self.var_lits.insert(name.clone(), v_lit);
                    v_lit
                }
            }
            Op::Not => {
                let inner = self.blast_bool(term.args[0], solver);
                !inner
            }
            Op::And => {
                if term.args.is_empty() {
                    self.get_true_lit(solver)
                } else {
                    let mut res = self.blast_bool(term.args[0], solver);
                    for &arg in &term.args[1..] {
                        let b = self.blast_bool(arg, solver);
                        res = self.gate_and(res, b, solver);
                    }
                    res
                }
            }
            Op::Or => {
                if term.args.is_empty() {
                    !self.get_true_lit(solver)
                } else {
                    let mut res = self.blast_bool(term.args[0], solver);
                    for &arg in &term.args[1..] {
                        let b = self.blast_bool(arg, solver);
                        res = self.gate_or(res, b, solver);
                    }
                    res
                }
            }
            Op::Xor => {
                let a = self.blast_bool(term.args[0], solver);
                let b = self.blast_bool(term.args[1], solver);
                self.gate_xor(a, b, solver)
            }
            Op::Implies => {
                let a = self.blast_bool(term.args[0], solver);
                let b = self.blast_bool(term.args[1], solver);
                self.gate_or(!a, b, solver)
            }
            Op::Ite => {
                let c = self.blast_bool(term.args[0], solver);
                let t = self.blast_bool(term.args[1], solver);
                let e = self.blast_bool(term.args[2], solver);
                self.gate_ite(c, t, e, solver)
            }
            Op::Eq => {
                let a = term.args[0];
                let b = term.args[1];
                let a_sort = self.arena.sort_of(a);
                if let smt_core::sort::Sort::BitVec(_) = self.sorts.get(a_sort) {
                    let a_bits = self.blast_bv(a, solver);
                    let b_bits = self.blast_bv(b, solver);
                    self.circuit_eq(&a_bits, &b_bits, solver)
                } else if a_sort == self.sorts.bool_sort {
                    let a_lit = self.blast_bool(a, solver);
                    let b_lit = self.blast_bool(b, solver);
                    let xor = self.gate_xor(a_lit, b_lit, solver);
                    !xor
                } else {
                    let v = solver.new_var();
                    v.to_lit()
                }
            }
            Op::Distinct => {
                if term.args.len() <= 1 {
                    self.get_true_lit(solver)
                } else if term.args.len() == 2 {
                    let a = term.args[0];
                    let b = term.args[1];
                    let a_sort = self.arena.sort_of(a);
                    let eq_lit = if let smt_core::sort::Sort::BitVec(_) = self.sorts.get(a_sort) {
                        let a_bits = self.blast_bv(a, solver);
                        let b_bits = self.blast_bv(b, solver);
                        self.circuit_eq(&a_bits, &b_bits, solver)
                    } else if a_sort == self.sorts.bool_sort {
                        let a_lit = self.blast_bool(a, solver);
                        let b_lit = self.blast_bool(b, solver);
                        let xor = self.gate_xor(a_lit, b_lit, solver);
                        !xor
                    } else {
                        let v = solver.new_var();
                        v.to_lit()
                    };
                    !eq_lit
                } else {
                    let mut diff_lits = Vec::new();
                    for i in 0..term.args.len() {
                        for j in (i + 1)..term.args.len() {
                            let a = term.args[i];
                            let b = term.args[j];
                            let a_sort = self.arena.sort_of(a);
                            let eq_lit =
                                if let smt_core::sort::Sort::BitVec(_) = self.sorts.get(a_sort) {
                                    let a_bits = self.blast_bv(a, solver);
                                    let b_bits = self.blast_bv(b, solver);
                                    self.circuit_eq(&a_bits, &b_bits, solver)
                                } else if a_sort == self.sorts.bool_sort {
                                    let a_lit = self.blast_bool(a, solver);
                                    let b_lit = self.blast_bool(b, solver);
                                    let xor = self.gate_xor(a_lit, b_lit, solver);
                                    !xor
                                } else {
                                    let v = solver.new_var();
                                    v.to_lit()
                                };
                            diff_lits.push(!eq_lit);
                        }
                    }
                    let mut res = diff_lits[0];
                    for &d in &diff_lits[1..] {
                        res = self.gate_and(res, d, solver);
                    }
                    res
                }
            }
            Op::BvUlt => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_ult(&a_bits, &b_bits, solver)
            }
            Op::BvUle => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let ult = self.circuit_ult(&a_bits, &b_bits, solver);
                let eq = self.circuit_eq(&a_bits, &b_bits, solver);
                self.gate_or(ult, eq, solver)
            }
            Op::BvUgt => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_ult(&b_bits, &a_bits, solver)
            }
            Op::BvUge => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let ugt = self.circuit_ult(&b_bits, &a_bits, solver);
                let eq = self.circuit_eq(&a_bits, &b_bits, solver);
                self.gate_or(ugt, eq, solver)
            }
            Op::BvSlt => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                self.circuit_slt(&a_bits, &b_bits, solver)
            }
            Op::BvSle => {
                let a_bits = self.blast_bv(term.args[0], solver);
                let b_bits = self.blast_bv(term.args[1], solver);
                let slt = self.circuit_slt(&a_bits, &b_bits, solver);
                let eq = self.circuit_eq(&a_bits, &b_bits, solver);
                self.gate_or(slt, eq, solver)
            }
            _ => {
                let v = solver.new_var();
                v.to_lit()
            }
        };

        self.bool_cache.insert(id, lit);
        lit
    }

    // --- Circuit Synthesis Helpers ---

    fn gate_and(&self, a: Lit, b: Lit, solver: &mut SatSolver) -> Lit {
        let v = solver.new_var();
        let p = v.to_lit();
        solver.add_clause(vec![!p, a]);
        solver.add_clause(vec![!p, b]);
        solver.add_clause(vec![p, !a, !b]);
        p
    }

    fn gate_or(&self, a: Lit, b: Lit, solver: &mut SatSolver) -> Lit {
        let v = solver.new_var();
        let p = v.to_lit();
        solver.add_clause(vec![!a, p]);
        solver.add_clause(vec![!b, p]);
        solver.add_clause(vec![!p, a, b]);
        p
    }

    fn gate_xor(&self, a: Lit, b: Lit, solver: &mut SatSolver) -> Lit {
        let v = solver.new_var();
        let p = v.to_lit();
        solver.add_clause(vec![!p, a, b]);
        solver.add_clause(vec![!p, !a, !b]);
        solver.add_clause(vec![p, !a, b]);
        solver.add_clause(vec![p, a, !b]);
        p
    }

    fn gate_ite(&self, c: Lit, t: Lit, e: Lit, solver: &mut SatSolver) -> Lit {
        let v = solver.new_var();
        let p = v.to_lit();
        solver.add_clause(vec![!c, !t, p]);
        solver.add_clause(vec![!c, t, !p]);
        solver.add_clause(vec![c, !e, p]);
        solver.add_clause(vec![c, e, !p]);
        p
    }

    fn gate_and_vec(&self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| self.gate_and(x, y, solver))
            .collect()
    }

    fn gate_or_vec(&self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| self.gate_or(x, y, solver))
            .collect()
    }

    fn gate_xor_vec(&self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| self.gate_xor(x, y, solver))
            .collect()
    }

    /// Ripple-carry adder circuit.
    fn circuit_adder(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len().min(b.len());
        let mut sum = Vec::with_capacity(len);
        let mut carry = !self.get_true_lit(solver); // 0

        for i in 0..len {
            let s = self.gate_xor(self.gate_xor(a[i], b[i], solver), carry, solver);
            sum.push(s);

            let a_and_b = self.gate_and(a[i], b[i], solver);
            let a_xor_b = self.gate_xor(a[i], b[i], solver);
            let c_and_xor = self.gate_and(carry, a_xor_b, solver);
            carry = self.gate_or(a_and_b, c_and_xor, solver);
        }

        sum
    }

    /// Subtractor: `A - B = A + (!B) + 1`.
    fn circuit_subtractor(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let not_b: Vec<Lit> = b.iter().map(|&x| !x).collect();
        let len = a.len().min(b.len());
        let mut sum = Vec::with_capacity(len);
        let mut carry = self.get_true_lit(solver); // +1

        for i in 0..len {
            let s = self.gate_xor(self.gate_xor(a[i], not_b[i], solver), carry, solver);
            sum.push(s);

            let a_and_b = self.gate_and(a[i], not_b[i], solver);
            let a_xor_b = self.gate_xor(a[i], not_b[i], solver);
            let c_and_xor = self.gate_and(carry, a_xor_b, solver);
            carry = self.gate_or(a_and_b, c_and_xor, solver);
        }

        sum
    }

    /// Shift-and-add array multiplier.
    fn circuit_multiplier(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        let false_l = !self.get_true_lit(solver);
        let mut acc = vec![false_l; len];

        for i in 0..len {
            // Compute a shifted by i, masked by b[i]
            let mut shifted_a = vec![false_l; len];
            for j in 0..len - i {
                shifted_a[i + j] = self.gate_and(a[j], b[i], solver);
            }
            acc = self.circuit_adder(&acc, &shifted_a, solver);
        }

        acc
    }

    /// Barrel shifter for `shl`.
    fn circuit_shl(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        let mut curr = a.to_vec();
        let false_l = !self.get_true_lit(solver);

        for (stage, &b_bit) in b.iter().enumerate() {
            let shift = 1 << stage;
            if shift >= len {
                break;
            }
            let mut next = vec![false_l; len];
            for i in 0..len {
                let shifted_in = if i >= shift { curr[i - shift] } else { false_l };
                next[i] = self.gate_ite(b_bit, shifted_in, curr[i], solver);
            }
            curr = next;
        }

        curr
    }

    /// Logical shift right.
    fn circuit_lshr(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        let mut curr = a.to_vec();
        let false_l = !self.get_true_lit(solver);

        for (stage, &b_bit) in b.iter().enumerate() {
            let shift = 1 << stage;
            if shift >= len {
                break;
            }
            let mut next = vec![false_l; len];
            for i in 0..len {
                let shifted_in = if i + shift < len {
                    curr[i + shift]
                } else {
                    false_l
                };
                next[i] = self.gate_ite(b_bit, shifted_in, curr[i], solver);
            }
            curr = next;
        }

        curr
    }

    /// Arithmetic shift right.
    fn circuit_ashr(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        let mut curr = a.to_vec();
        let sign_bit = a[len - 1];

        for (stage, &b_bit) in b.iter().enumerate() {
            let shift = 1 << stage;
            if shift >= len {
                break;
            }
            let mut next = vec![sign_bit; len];
            for i in 0..len {
                let shifted_in = if i + shift < len {
                    curr[i + shift]
                } else {
                    sign_bit
                };
                next[i] = self.gate_ite(b_bit, shifted_in, curr[i], solver);
            }
            curr = next;
        }

        curr
    }

    /// Equality comparison: `a == b <=> AND_{i} (a_i <=> b_i)`.
    pub fn circuit_eq(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Lit {
        let mut eq_bits = Vec::with_capacity(a.len());
        for (&x, &y) in a.iter().zip(b.iter()) {
            let xor = self.gate_xor(x, y, solver);
            eq_bits.push(!xor);
        }

        let mut res = self.get_true_lit(solver);
        for bit in eq_bits {
            res = self.gate_and(res, bit, solver);
        }
        res
    }

    /// Unsigned less-than comparison.
    pub fn circuit_ult(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Lit {
        let len = a.len();
        let not_b: Vec<Lit> = b.iter().map(|&x| !x).collect();
        let mut carry = self.get_true_lit(solver);

        for i in 0..len {
            let a_and_b = self.gate_and(a[i], not_b[i], solver);
            let a_xor_b = self.gate_xor(a[i], not_b[i], solver);
            let c_and_xor = self.gate_and(carry, a_xor_b, solver);
            carry = self.gate_or(a_and_b, c_and_xor, solver);
        }

        // Ult is true if and only if carry out of a + (!b) + 1 is false (borrow generated)
        !carry
    }

    /// Signed less-than comparison.
    pub fn circuit_slt(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Lit {
        let len = a.len();
        let sign_a = a[len - 1];
        let sign_b = b[len - 1];

        let ult = self.circuit_ult(a, b, solver);
        let signs_diff = self.gate_xor(sign_a, sign_b, solver);

        // If signs differ: a < b <=> a is negative (sign_a == 1)
        // If signs match: a < b <=> ult(a, b)
        self.gate_ite(signs_diff, sign_a, ult, solver)
    }

    /// Bitvector 2's complement negation: `-a`.
    fn circuit_neg(&mut self, a: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        let not_a: Vec<Lit> = a.iter().map(|&b| !b).collect();
        let true_l = self.get_true_lit(solver);
        let false_l = !true_l;
        let mut one_bits = vec![false_l; len];
        if len > 0 {
            one_bits[0] = true_l;
        }
        self.circuit_adder(&not_a, &one_bits, solver)
    }

    /// Checks if bitvector is identically zero: `AND_{i} !b_i`.
    fn circuit_is_zero(&mut self, b: &[Lit], solver: &mut SatSolver) -> Lit {
        let mut is_zero = self.get_true_lit(solver);
        for &bit in b {
            is_zero = self.gate_and(is_zero, !bit, solver);
        }
        is_zero
    }

    /// Restoring binary divider producing (quotient, remainder) adhering to SMT-LIB 2.6:
    /// - If divisor == 0: quotient = all 1s (2^w - 1), remainder = dividend.
    pub fn circuit_udiv_urem(
        &mut self,
        a: &[Lit],
        b: &[Lit],
        solver: &mut SatSolver,
    ) -> (Vec<Lit>, Vec<Lit>) {
        let len = a.len();
        let false_l = !self.get_true_lit(solver);
        let true_l = self.get_true_lit(solver);

        if len == 0 {
            return (Vec::new(), Vec::new());
        }

        let mut q = vec![false_l; len];
        let mut r = vec![false_l; len];

        for i in (0..len).rev() {
            // Shift r left by 1 and insert a[i] as LSB
            let mut r_next = vec![false_l; len];
            r_next[1..len].copy_from_slice(&r[..(len - 1)]);
            r_next[0] = a[i];
            let overflow = r[len - 1];

            // Condition to subtract: overflow == 1 OR r_next >= b (i.e. !ult(r_next, b))
            let r_lt_b = self.circuit_ult(&r_next, b, solver);
            let r_ge_b = !r_lt_b;
            let do_sub = self.gate_or(overflow, r_ge_b, solver);

            q[i] = do_sub;
            let sub_res = self.circuit_subtractor(&r_next, b, solver);

            for k in 0..len {
                r[k] = self.gate_ite(do_sub, sub_res[k], r_next[k], solver);
            }
        }

        // Handle division by zero according to SMT-LIB standard:
        // udiv(a, 0) = all 1s
        // urem(a, 0) = a
        let is_zero = self.circuit_is_zero(b, solver);
        let mut final_q = Vec::with_capacity(len);
        let mut final_r = Vec::with_capacity(len);

        for i in 0..len {
            final_q.push(self.gate_ite(is_zero, true_l, q[i], solver));
            final_r.push(self.gate_ite(is_zero, a[i], r[i], solver));
        }

        (final_q, final_r)
    }

    /// Signed division adhering to SMT-LIB 2.6:
    /// - If divisor == 0:
    ///   sdiv(s, 0) = all 1s (-1) if s >= 0, else 1
    /// - sdiv(s, t) = if s_sign != t_sign then -udiv(|s|, |t|) else udiv(|s|, |t|)
    pub fn circuit_sdiv(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        if len == 0 {
            return Vec::new();
        }
        let true_l = self.get_true_lit(solver);
        let false_l = !true_l;

        let sign_a = a[len - 1];
        let sign_b = b[len - 1];

        let abs_a = {
            let neg_a = self.circuit_neg(a, solver);
            let mut v = Vec::with_capacity(len);
            for i in 0..len {
                v.push(self.gate_ite(sign_a, neg_a[i], a[i], solver));
            }
            v
        };

        let abs_b = {
            let neg_b = self.circuit_neg(b, solver);
            let mut v = Vec::with_capacity(len);
            for i in 0..len {
                v.push(self.gate_ite(sign_b, neg_b[i], b[i], solver));
            }
            v
        };

        let (q_abs, _) = self.circuit_udiv_urem(&abs_a, &abs_b, solver);
        let neg_q = self.circuit_neg(&q_abs, solver);

        let signs_diff = self.gate_xor(sign_a, sign_b, solver);
        let mut normal_res = Vec::with_capacity(len);
        for i in 0..len {
            normal_res.push(self.gate_ite(signs_diff, neg_q[i], q_abs[i], solver));
        }

        // Division by zero special case:
        // if a is negative (sign_a == 1): 1 (i.e. #b000...01)
        // if a is positive (sign_a == 0): all 1s (-1)
        let is_b_zero = self.circuit_is_zero(b, solver);
        let mut div0_res = Vec::with_capacity(len);
        for (i, &normal_bit) in normal_res.iter().enumerate().take(len) {
            let bit_if_pos = true_l;
            let bit_if_neg = if i == 0 { true_l } else { false_l };
            let bit_div0 = self.gate_ite(sign_a, bit_if_neg, bit_if_pos, solver);
            div0_res.push(self.gate_ite(is_b_zero, bit_div0, normal_bit, solver));
        }

        div0_res
    }

    /// Signed remainder adhering to SMT-LIB 2.6:
    /// - If divisor == 0: srem(s, 0) = s
    /// - srem(s, t) = if s_sign then -urem(|s|, |t|) else urem(|s|, |t|)
    pub fn circuit_srem(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        if len == 0 {
            return Vec::new();
        }

        let sign_a = a[len - 1];
        let sign_b = b[len - 1];

        let abs_a = {
            let neg_a = self.circuit_neg(a, solver);
            let mut v = Vec::with_capacity(len);
            for i in 0..len {
                v.push(self.gate_ite(sign_a, neg_a[i], a[i], solver));
            }
            v
        };

        let abs_b = {
            let neg_b = self.circuit_neg(b, solver);
            let mut v = Vec::with_capacity(len);
            for i in 0..len {
                v.push(self.gate_ite(sign_b, neg_b[i], b[i], solver));
            }
            v
        };

        let (_, r_abs) = self.circuit_udiv_urem(&abs_a, &abs_b, solver);
        let neg_r = self.circuit_neg(&r_abs, solver);

        let mut normal_res = Vec::with_capacity(len);
        for i in 0..len {
            normal_res.push(self.gate_ite(sign_a, neg_r[i], r_abs[i], solver));
        }

        let is_b_zero = self.circuit_is_zero(b, solver);
        let mut final_res = Vec::with_capacity(len);
        for i in 0..len {
            final_res.push(self.gate_ite(is_b_zero, a[i], normal_res[i], solver));
        }

        final_res
    }

    /// Signed modulo adhering to SMT-LIB 2.6:
    /// - If divisor == 0: smod(s, 0) = s
    /// - smod(s, t) = s - t * floor(s / t)
    pub fn circuit_smod(&mut self, a: &[Lit], b: &[Lit], solver: &mut SatSolver) -> Vec<Lit> {
        let len = a.len();
        if len == 0 {
            return Vec::new();
        }

        let rem = self.circuit_srem(a, b, solver);
        let is_rem_zero = self.circuit_is_zero(&rem, solver);

        let sign_a = a[len - 1];
        let sign_b = b[len - 1];
        let signs_diff = self.gate_xor(sign_a, sign_b, solver);

        // If rem == 0, result is 0
        // If signs match (signs_diff is false), result is rem
        // If signs differ (signs_diff is true), result is rem + b
        let rem_plus_b = self.circuit_adder(&rem, b, solver);

        let mut adjusted = Vec::with_capacity(len);
        for i in 0..len {
            let non_zero_case = self.gate_ite(signs_diff, rem_plus_b[i], rem[i], solver);
            let false_l = !self.get_true_lit(solver);
            adjusted.push(self.gate_ite(is_rem_zero, false_l, non_zero_case, solver));
        }

        let is_b_zero = self.circuit_is_zero(b, solver);
        let mut final_res = Vec::with_capacity(len);
        for i in 0..len {
            final_res.push(self.gate_ite(is_b_zero, a[i], adjusted[i], solver));
        }

        final_res
    }
}
