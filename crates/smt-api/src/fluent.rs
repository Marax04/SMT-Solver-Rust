//! Fluent Rust programmatic builder API for symbolic execution engines.

use num_bigint::BigUint;
use smt_core::sort::{SortArena, SortId};
use smt_core::term::{Op, TermArena, TermId};
use smt_core::value::Value;
use smt_solver::engine::{CheckSatResult, Solver};

/// A shared expression node in the fluent API.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Expr {
    pub id: TermId,
    pub sort: SortId,
}

/// Context managing sort and term allocation for fluent builders.
#[derive(Debug, Clone)]
pub struct Context {
    pub sorts: SortArena,
    pub terms: TermArena,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// Creates a new fluent context.
    ///
    /// # Example
    /// ```rust
    /// use smt_api::Context;
    /// let mut ctx = Context::new();
    /// let x = ctx.bv_var("x", 32);
    /// assert_eq!(x.sort, ctx.sorts.bv(32));
    /// ```
    pub fn new() -> Self {
        let mut sorts = SortArena::new();
        let terms = TermArena::new(&mut sorts);
        Self { sorts, terms }
    }

    /// Creates a boolean variable.
    pub fn bool_var(&mut self, name: &str) -> Expr {
        let sort = self.sorts.bool_sort;
        let id = self.terms.var(name, sort);
        Expr { id, sort }
    }

    /// Creates a bit-vector variable.
    pub fn bv_var(&mut self, name: &str, width: u32) -> Expr {
        let sort = self.sorts.bv(width);
        let id = self.terms.var(name, sort);
        Expr { id, sort }
    }

    /// Creates a bit-vector constant from integer.
    pub fn bv_const(&mut self, val: u64, width: u32) -> Expr {
        let sort = self.sorts.bv(width);
        let id = self
            .terms
            .bv_const(BigUint::from(val), width, &mut self.sorts);
        Expr { id, sort }
    }

    /// Bit-vector addition.
    pub fn bv_add(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvAdd, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector subtraction.
    pub fn bv_sub(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvSub, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector multiplication.
    pub fn bv_mul(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvMul, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise XOR.
    pub fn bv_xor(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvXor, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise AND.
    pub fn bv_and(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvAnd, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise OR.
    pub fn bv_or(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.terms.bv_binop(Op::BvOr, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Equality of two expressions.
    pub fn eq(&mut self, a: Expr, b: Expr) -> Expr {
        let sort = self.sorts.bool_sort;
        let id = self.terms.eq(a.id, b.id, &self.sorts);
        Expr { id, sort }
    }

    /// Boolean NOT.
    pub fn not(&mut self, a: Expr) -> Expr {
        let id = self.terms.not(a.id);
        Expr { id, sort: a.sort }
    }

    /// Boolean AND.
    pub fn and(&mut self, args: &[Expr]) -> Expr {
        let term_ids: Vec<TermId> = args.iter().map(|e| e.id).collect();
        let id = self.terms.and(term_ids, &self.sorts);
        Expr {
            id,
            sort: self.sorts.bool_sort,
        }
    }

    /// Boolean OR.
    pub fn or(&mut self, args: &[Expr]) -> Expr {
        let term_ids: Vec<TermId> = args.iter().map(|e| e.id).collect();
        let id = self.terms.or(term_ids, &self.sorts);
        Expr {
            id,
            sort: self.sorts.bool_sort,
        }
    }

    /// If-then-else.
    pub fn ite(&mut self, cond: Expr, then_b: Expr, else_b: Expr) -> Expr {
        let id = self.terms.ite(cond.id, then_b.id, else_b.id);
        Expr {
            id,
            sort: then_b.sort,
        }
    }
}

/// Fluent Solver wrapping the underlying SMT engine.
pub struct FluentSolver {
    pub inner: Solver,
}

impl Default for FluentSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl FluentSolver {
    /// Creates a fluent solver.
    ///
    /// # Example
    /// ```rust
    /// use smt_api::FluentSolver;
    /// use smt_solver::engine::CheckSatResult;
    /// let mut solver = FluentSolver::new();
    /// assert_eq!(solver.check(), CheckSatResult::Sat);
    /// ```
    pub fn new() -> Self {
        Self {
            inner: Solver::new(),
        }
    }

    /// Asserts an expression into the solver.
    pub fn assert(&mut self, expr: Expr) {
        self.inner.assert_formula(expr.id);
    }

    /// Creates a boolean variable.
    pub fn bool_var(&mut self, name: &str) -> Expr {
        let sort = self.inner.sorts.bool_sort;
        let id = self.inner.declare_const(name, sort);
        Expr { id, sort }
    }

    /// Creates a bit-vector variable.
    pub fn bv_var(&mut self, name: &str, width: u32) -> Expr {
        let sort = self.inner.sorts.bv(width);
        let id = self.inner.declare_const(name, sort);
        Expr { id, sort }
    }

    /// Creates a bit-vector constant from integer.
    pub fn bv_const(&mut self, val: u64, width: u32) -> Expr {
        let sort = self.inner.sorts.bv(width);
        let id = self
            .inner
            .terms
            .bv_const(BigUint::from(val), width, &mut self.inner.sorts);
        Expr { id, sort }
    }

    /// Bit-vector addition.
    pub fn bv_add(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvAdd, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector subtraction.
    pub fn bv_sub(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvSub, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector multiplication.
    pub fn bv_mul(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvMul, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise XOR.
    pub fn bv_xor(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvXor, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise AND.
    pub fn bv_and(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvAnd, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Bit-vector bitwise OR.
    pub fn bv_or(&mut self, a: Expr, b: Expr) -> Expr {
        let id = self.inner.terms.bv_binop(Op::BvOr, a.id, b.id).unwrap();
        Expr { id, sort: a.sort }
    }

    /// Equality of two expressions.
    pub fn eq(&mut self, a: Expr, b: Expr) -> Expr {
        let sort = self.inner.sorts.bool_sort;
        let id = self.inner.terms.eq(a.id, b.id, &self.inner.sorts);
        Expr { id, sort }
    }

    /// Boolean NOT.
    pub fn not(&mut self, a: Expr) -> Expr {
        let id = self.inner.terms.not(a.id);
        Expr { id, sort: a.sort }
    }

    /// Boolean AND.
    pub fn and(&mut self, args: &[Expr]) -> Expr {
        let term_ids: Vec<TermId> = args.iter().map(|e| e.id).collect();
        let id = self.inner.terms.and(term_ids, &self.inner.sorts);
        Expr {
            id,
            sort: self.inner.sorts.bool_sort,
        }
    }

    /// Boolean OR.
    pub fn or(&mut self, args: &[Expr]) -> Expr {
        let term_ids: Vec<TermId> = args.iter().map(|e| e.id).collect();
        let id = self.inner.terms.or(term_ids, &self.inner.sorts);
        Expr {
            id,
            sort: self.inner.sorts.bool_sort,
        }
    }

    /// If-then-else.
    pub fn ite(&mut self, cond: Expr, then_b: Expr, else_b: Expr) -> Expr {
        let id = self.inner.terms.ite(cond.id, then_b.id, else_b.id);
        Expr {
            id,
            sort: then_b.sort,
        }
    }

    /// Checks satisfiability.
    pub fn check(&mut self) -> CheckSatResult {
        self.inner.check_sat()
    }

    /// Retrieves an evaluated bit-vector value as `u64`.
    pub fn get_bv_u64(&self, name: &str) -> Option<u64> {
        let model = self.inner.get_model()?;
        if let Some(Value::BitVec { value, .. }) = model.get(name) {
            num_traits::ToPrimitive::to_u64(value)
        } else {
            None
        }
    }
}
