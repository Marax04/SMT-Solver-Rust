//! Concrete model validator: verifies that a candidate model satisfies all asserted formulas.

use crate::model::Model;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use smt_core::diagnostics::{SmtError, SmtResult};
use smt_core::sort::{Sort, SortArena, SortId};
use smt_core::term::{Op, TermArena, TermId};
use smt_core::value::Value;
use std::collections::HashMap;

/// Validates candidate models against original assertions.
#[derive(Debug, Default)]
pub struct ModelValidator {
    memo: HashMap<TermId, Value>,
    fn_table: HashMap<(String, Vec<Value>), Value>,
}

impl ModelValidator {
    pub fn new() -> Self {
        Self {
            memo: HashMap::new(),
            fn_table: HashMap::new(),
        }
    }

    /// Verifies all assertions against the model.
    pub fn validate(
        &mut self,
        assertions: &[TermId],
        model: &Model,
        terms: &TermArena,
        sorts: &SortArena,
    ) -> SmtResult<bool> {
        self.memo.clear();
        self.fn_table.clear();
        for &assertion in assertions {
            let val = self.evaluate(assertion, model, terms, sorts)?;
            if val != Value::Bool(true) {
                return Err(SmtError::Internal {
                    details: format!(
                        "Model validation failed for assertion {:?}: evaluated to {}",
                        assertion, val
                    ),
                });
            }
        }
        Ok(true)
    }

    /// Evaluates a term under the given model valuation.
    pub fn evaluate(
        &mut self,
        term_id: TermId,
        model: &Model,
        terms: &TermArena,
        sorts: &SortArena,
    ) -> SmtResult<Value> {
        if let Some(val) = self.memo.get(&term_id) {
            return Ok(val.clone());
        }

        let term = terms.get(term_id);
        let res = match &term.op {
            Op::True => Value::Bool(true),
            Op::False => Value::Bool(false),
            Op::Var(name) => {
                if let Some(val) = model.get(name) {
                    val.clone()
                } else {
                    self.default_for_sort(term.sort, sorts)
                }
            }
            Op::Not => {
                let inner = self.evaluate(term.args[0], model, terms, sorts)?;
                match inner {
                    Value::Bool(b) => Value::Bool(!b),
                    _ => return Err(self.type_err("Not expects Bool")),
                }
            }
            Op::And => {
                let mut b = true;
                for &arg in &term.args {
                    let v = self.evaluate(arg, model, terms, sorts)?;
                    if v != Value::Bool(true) {
                        b = false;
                        break;
                    }
                }
                Value::Bool(b)
            }
            Op::Or => {
                let mut b = false;
                for &arg in &term.args {
                    let v = self.evaluate(arg, model, terms, sorts)?;
                    if v == Value::Bool(true) {
                        b = true;
                        break;
                    }
                }
                Value::Bool(b)
            }
            Op::Xor => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Bool(va), Value::Bool(vb)) => Value::Bool(va ^ vb),
                    _ => return Err(self.type_err("Xor expects Bool")),
                }
            }
            Op::Implies => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Bool(va), Value::Bool(vb)) => Value::Bool(!va || vb),
                    _ => return Err(self.type_err("Implies expects Bool")),
                }
            }
            Op::Ite => {
                let c = self.evaluate(term.args[0], model, terms, sorts)?;
                match c {
                    Value::Bool(true) => self.evaluate(term.args[1], model, terms, sorts)?,
                    Value::Bool(false) => self.evaluate(term.args[2], model, terms, sorts)?,
                    _ => return Err(self.type_err("Ite condition expects Bool")),
                }
            }
            Op::Eq => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                Value::Bool(a == b)
            }
            Op::Distinct => {
                let mut vals = Vec::with_capacity(term.args.len());
                for &arg in &term.args {
                    vals.push(self.evaluate(arg, model, terms, sorts)?);
                }
                let mut distinct = true;
                for i in 0..vals.len() {
                    for j in i + 1..vals.len() {
                        if vals[i] == vals[j] {
                            distinct = false;
                            break;
                        }
                    }
                    if !distinct {
                        break;
                    }
                }
                Value::Bool(distinct)
            }
            Op::BvConst { value, width } => Value::BitVec {
                value: value.clone(),
                width: *width,
            },
            Op::BvAdd => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::new_bv(va + vb, wa)
            }
            Op::BvSub => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                let modulus = BigUint::from(1u32) << wa;
                let res = (va + &modulus - (vb % &modulus)) % &modulus;
                Value::new_bv(res, wa)
            }
            Op::BvMul => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::new_bv(va * vb, wa)
            }
            Op::BvUdiv => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                if vb.is_zero() {
                    let max_val = (BigUint::from(1u32) << wa) - 1u32;
                    Value::BitVec {
                        value: max_val,
                        width: wa,
                    }
                } else {
                    Value::new_bv(va / vb, wa)
                }
            }
            Op::BvUrem => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                if vb.is_zero() {
                    Value::new_bv(va, wa)
                } else {
                    Value::new_bv(va % vb, wa)
                }
            }
            Op::BvNeg => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let modulus = BigUint::from(1u32) << wa;
                let res = (&modulus - (va % &modulus)) % &modulus;
                Value::new_bv(res, wa)
            }
            Op::BvAnd => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::new_bv(va & vb, wa)
            }
            Op::BvOr => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::new_bv(va | vb, wa)
            }
            Op::BvXor => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::new_bv(va ^ vb, wa)
            }
            Op::BvNot => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let mask = (BigUint::from(1u32) << wa) - 1u32;
                Value::new_bv(mask ^ va, wa)
            }
            Op::BvShl => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                let shift = vb.to_u32().unwrap_or(wa);
                if shift >= wa {
                    Value::new_bv(BigUint::zero(), wa)
                } else {
                    Value::new_bv(va << shift, wa)
                }
            }
            Op::BvLshr => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                let shift = vb.to_u32().unwrap_or(wa);
                if shift >= wa {
                    Value::new_bv(BigUint::zero(), wa)
                } else {
                    Value::new_bv(va >> shift, wa)
                }
            }
            Op::BvConcat => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, wb) = self.eval_bv(term.args[1], model, terms, sorts)?;
                let res = (va << wb) | vb;
                Value::new_bv(res, wa + wb)
            }
            Op::BvExtract { high, low } => {
                let (va, _) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let shifted = va >> low;
                let w = high - low + 1;
                Value::new_bv(shifted, w)
            }
            Op::BvZeroExtend(n) => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                Value::BitVec {
                    value: va,
                    width: wa + n,
                }
            }
            Op::BvSignExtend(n) => {
                let (va, wa) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let sign_bit = (&va >> (wa - 1)) & BigUint::from(1u32);
                let mut res = va;
                if sign_bit == BigUint::from(1u32) {
                    let ext_mask = ((BigUint::from(1u32) << n) - 1u32) << wa;
                    res |= ext_mask;
                }
                Value::BitVec {
                    value: res,
                    width: wa + n,
                }
            }
            Op::BvUlt => {
                let (va, _) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::Bool(va < vb)
            }
            Op::BvUle => {
                let (va, _) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::Bool(va <= vb)
            }
            Op::BvUgt => {
                let (va, _) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::Bool(va > vb)
            }
            Op::BvUge => {
                let (va, _) = self.eval_bv(term.args[0], model, terms, sorts)?;
                let (vb, _) = self.eval_bv(term.args[1], model, terms, sorts)?;
                Value::Bool(va >= vb)
            }
            Op::IntConst(i) => Value::Int(i.clone()),
            Op::RealConst(r) => Value::Real(r.clone()),
            Op::Add => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Int(ia + ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Real(ra + rb),
                    _ => return Err(self.type_err("Add expects Int or Real")),
                }
            }
            Op::Sub => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Int(ia - ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Real(ra - rb),
                    _ => return Err(self.type_err("Sub expects Int or Real")),
                }
            }
            Op::Mul => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Int(ia * ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Real(ra * rb),
                    _ => return Err(self.type_err("Mul expects Int or Real")),
                }
            }
            Op::Div => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Real(ra), Value::Real(rb)) => {
                        if rb.is_zero() {
                            Value::Real(BigRational::zero())
                        } else {
                            Value::Real(ra / rb)
                        }
                    }
                    _ => return Err(self.type_err("Div expects Real")),
                }
            }
            Op::Lt => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Bool(ia < ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Bool(ra < rb),
                    _ => return Err(self.type_err("Lt expects Int or Real")),
                }
            }
            Op::Le => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Bool(ia <= ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Bool(ra <= rb),
                    _ => return Err(self.type_err("Le expects Int or Real")),
                }
            }
            Op::Gt => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Bool(ia > ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Bool(ra > rb),
                    _ => return Err(self.type_err("Gt expects Int or Real")),
                }
            }
            Op::Ge => {
                let a = self.evaluate(term.args[0], model, terms, sorts)?;
                let b = self.evaluate(term.args[1], model, terms, sorts)?;
                match (a, b) {
                    (Value::Int(ia), Value::Int(ib)) => Value::Bool(ia >= ib),
                    (Value::Real(ra), Value::Real(rb)) => Value::Bool(ra >= rb),
                    _ => return Err(self.type_err("Ge expects Int or Real")),
                }
            }
            Op::Apply(func_name) => {
                let mut arg_vals = Vec::with_capacity(term.args.len());
                for &arg in &term.args {
                    arg_vals.push(self.evaluate(arg, model, terms, sorts)?);
                }
                let key = (func_name.clone(), arg_vals);
                if let Some(res) = self.fn_table.get(&key) {
                    res.clone()
                } else {
                    let res = self.default_for_sort(term.sort, sorts);
                    self.fn_table.insert(key, res.clone());
                    res
                }
            }
            _ => self.default_for_sort(term.sort, sorts),
        };

        self.memo.insert(term_id, res.clone());
        Ok(res)
    }

    fn eval_bv(
        &mut self,
        term_id: TermId,
        model: &Model,
        terms: &TermArena,
        sorts: &SortArena,
    ) -> SmtResult<(BigUint, u32)> {
        let val = self.evaluate(term_id, model, terms, sorts)?;
        match val {
            Value::BitVec { value, width } => Ok((value, width)),
            _ => Err(self.type_err("Expected BitVec value")),
        }
    }

    fn default_for_sort(&self, sort_id: SortId, sorts: &SortArena) -> Value {
        match sorts.get(sort_id) {
            Sort::Bool => Value::Bool(false),
            Sort::BitVec(w) => Value::BitVec {
                value: BigUint::zero(),
                width: *w,
            },
            Sort::Int => Value::Int(BigInt::zero()),
            Sort::Real => Value::Real(BigRational::zero()),
            _ => Value::Bool(false),
        }
    }

    fn type_err(&self, msg: &str) -> SmtError {
        SmtError::Type {
            expected: "Valid type".to_string(),
            found: msg.to_string(),
            context: "Model validation".to_string(),
        }
    }
}
