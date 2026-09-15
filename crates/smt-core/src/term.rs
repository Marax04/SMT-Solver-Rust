//! Intermediate Representation (IR) with Hash-Consing.

use crate::diagnostics::{SmtError, SmtResult};
use crate::sort::{Sort, SortArena, SortId};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use std::collections::HashMap;
use std::fmt;

/// Unique identifier for an interned Term in the `TermArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermId(pub u32);

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t#{}", self.0)
    }
}

/// SMT operators spanning Booleans, Bit-Vectors, Linear Arithmetic, Arrays, and EUF.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    // --- Boolean Core ---
    True,
    False,
    Not,
    And,
    Or,
    Xor,
    Implies,
    Ite,

    // --- Polymorphic Equality & Disequality ---
    Eq,
    Distinct,

    // --- Bit-Vectors (QF_BV) ---
    BvConst { value: BigUint, width: u32 },
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvSdiv,
    BvUrem,
    BvSrem,
    BvSmod,
    BvNeg,
    BvAnd,
    BvOr,
    BvXor,
    BvNot,
    BvNand,
    BvNor,
    BvXnor,
    BvShl,
    BvLshr,
    BvAshr,
    BvRotateLeft(u32),
    BvRotateRight(u32),
    BvConcat,
    BvExtract { high: u32, low: u32 },
    BvSignExtend(u32),
    BvZeroExtend(u32),
    BvRepeat(u32),
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,

    // --- Linear & Non-Linear Arithmetic (Int / Real) ---
    IntConst(BigInt),
    RealConst(BigRational),
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Rem,
    Neg,
    Lt,
    Le,
    Gt,
    Ge,
    ToReal,
    ToInt,
    IsInt,

    // --- Arrays ---
    Select,
    Store,
    ConstArray(SortId),

    // --- Uninterpreted Functions & Variables ---
    Var(String),
    Apply(String),
}

/// Canonical data representation of an interned term node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermData {
    pub op: Op,
    pub args: Vec<TermId>,
    pub sort: SortId,
}

/// Hash-consing storage engine for intermediate terms.
#[derive(Debug, Clone)]
pub struct TermArena {
    terms: Vec<TermData>,
    lookup: HashMap<(Op, Vec<TermId>), TermId>,
    pub true_id: TermId,
    pub false_id: TermId,
}

impl TermArena {
    /// Initializes an arena with pre-allocated canonical `true` and `false` terms.
    pub fn new(sorts: &mut SortArena) -> Self {
        let mut arena = Self {
            terms: Vec::with_capacity(1024),
            lookup: HashMap::with_capacity(1024),
            true_id: TermId(0),
            false_id: TermId(0),
        };
        let bool_sort = sorts.bool_sort;
        arena.true_id = arena.intern(Op::True, Vec::new(), bool_sort);
        arena.false_id = arena.intern(Op::False, Vec::new(), bool_sort);
        arena
    }

    /// Interns a term with given operator, arguments, and sort. Returns its unique `TermId`.
    pub fn intern(&mut self, op: Op, args: Vec<TermId>, sort: SortId) -> TermId {
        let key = (op.clone(), args.clone());
        if let Some(&id) = self.lookup.get(&key) {
            return id;
        }
        let id = TermId(self.terms.len() as u32);
        self.terms.push(TermData { op, args, sort });
        self.lookup.insert(key, id);
        id
    }

    /// Fetches the term data associated with a `TermId`.
    pub fn get(&self, id: TermId) -> &TermData {
        &self.terms[id.0 as usize]
    }

    /// Fetches the operator of the term.
    pub fn op_of(&self, id: TermId) -> &Op {
        &self.terms[id.0 as usize].op
    }

    /// Fetches the arguments of the term.
    pub fn args_of(&self, id: TermId) -> &[TermId] {
        &self.terms[id.0 as usize].args
    }

    /// Fetches the SortId of the term.
    pub fn sort_of(&self, id: TermId) -> SortId {
        self.terms[id.0 as usize].sort
    }

    /// Returns the total count of interned terms.
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Returns true if the arena is empty.
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    // --- Helper Constructors with Static Validation ---

    /// Creates or returns a variable term.
    pub fn var(&mut self, name: impl Into<String>, sort: SortId) -> TermId {
        self.intern(Op::Var(name.into()), Vec::new(), sort)
    }

    /// Logical negation: `(not a)`.
    pub fn not(&mut self, a: TermId) -> TermId {
        if a == self.true_id {
            return self.false_id;
        }
        if a == self.false_id {
            return self.true_id;
        }
        let sort = self.sort_of(a);
        self.intern(Op::Not, vec![a], sort)
    }

    /// Logical conjunction: `(and a b ...)`.
    pub fn and(&mut self, args: Vec<TermId>, sorts: &SortArena) -> TermId {
        if args.is_empty() {
            return self.true_id;
        }
        let mut flat = Vec::with_capacity(args.len());
        for arg in args {
            if arg == self.false_id {
                return self.false_id;
            }
            if arg != self.true_id {
                flat.push(arg);
            }
        }
        if flat.is_empty() {
            return self.true_id;
        }
        if flat.len() == 1 {
            return flat[0];
        }
        self.intern(Op::And, flat, sorts.bool_sort)
    }

    /// Logical disjunction: `(or a b ...)`.
    pub fn or(&mut self, args: Vec<TermId>, sorts: &SortArena) -> TermId {
        if args.is_empty() {
            return self.false_id;
        }
        let mut flat = Vec::with_capacity(args.len());
        for arg in args {
            if arg == self.true_id {
                return self.true_id;
            }
            if arg != self.false_id {
                flat.push(arg);
            }
        }
        if flat.is_empty() {
            return self.false_id;
        }
        if flat.len() == 1 {
            return flat[0];
        }
        self.intern(Op::Or, flat, sorts.bool_sort)
    }

    /// Logical exclusive-or: `(xor a b)`.
    pub fn xor(&mut self, a: TermId, b: TermId, sorts: &SortArena) -> TermId {
        self.intern(Op::Xor, vec![a, b], sorts.bool_sort)
    }

    /// Logical implication: `(=> a b)`.
    pub fn implies(&mut self, a: TermId, b: TermId, sorts: &SortArena) -> TermId {
        self.intern(Op::Implies, vec![a, b], sorts.bool_sort)
    }

    /// If-then-else: `(ite cond then_branch else_branch)`.
    pub fn ite(&mut self, cond: TermId, then_b: TermId, else_b: TermId) -> TermId {
        if cond == self.true_id {
            return then_b;
        }
        if cond == self.false_id {
            return else_b;
        }
        if then_b == else_b {
            return then_b;
        }
        let sort = self.sort_of(then_b);
        self.intern(Op::Ite, vec![cond, then_b, else_b], sort)
    }

    /// Equality: `(= a b)`.
    pub fn eq(&mut self, a: TermId, b: TermId, sorts: &SortArena) -> TermId {
        if a == b {
            return self.true_id;
        }
        self.intern(Op::Eq, vec![a, b], sorts.bool_sort)
    }

    /// Distinct: `(distinct a b ...)`.
    pub fn distinct(&mut self, args: Vec<TermId>, sorts: &SortArena) -> TermId {
        self.intern(Op::Distinct, args, sorts.bool_sort)
    }

    /// Bit-vector constant.
    pub fn bv_const(&mut self, mut value: BigUint, width: u32, sorts: &mut SortArena) -> TermId {
        let mask = if width > 0 {
            (BigUint::from(1u32) << width) - 1u32
        } else {
            BigUint::from(0u32)
        };
        value &= mask;
        let sort = sorts.bv(width);
        self.intern(Op::BvConst { value, width }, Vec::new(), sort)
    }

    /// Binary Bit-Vector arithmetic operations.
    pub fn bv_binop(&mut self, op: Op, a: TermId, b: TermId) -> SmtResult<TermId> {
        let sort_a = self.sort_of(a);
        let sort_b = self.sort_of(b);
        if sort_a != sort_b {
            return Err(SmtError::Type {
                expected: format!("{}", sort_a),
                found: format!("{}", sort_b),
                context: "BitVector binary operation sort match".to_string(),
            });
        }
        Ok(self.intern(op, vec![a, b], sort_a))
    }

    /// Unary Bit-Vector operations (bvnot, bvneg).
    pub fn bv_unop(&mut self, op: Op, a: TermId) -> SmtResult<TermId> {
        let sort_a = self.sort_of(a);
        Ok(self.intern(op, vec![a], sort_a))
    }

    /// Bit-Vector extraction: `((_ extract high low) term)`.
    pub fn bv_extract(
        &mut self,
        high: u32,
        low: u32,
        arg: TermId,
        sorts: &mut SortArena,
    ) -> SmtResult<TermId> {
        let sort = self.sort_of(arg);
        match sorts.get(sort) {
            Sort::BitVec(w) => {
                if high >= *w || high < low {
                    return Err(SmtError::Type {
                        expected: format!("0 <= low <= high < {}", w),
                        found: format!("extract {}:{}", high, low),
                        context: "bv_extract bounds".to_string(),
                    });
                }
                let res_width = high - low + 1;
                let res_sort = sorts.bv(res_width);
                Ok(self.intern(Op::BvExtract { high, low }, vec![arg], res_sort))
            }
            _ => Err(SmtError::Type {
                expected: "BitVec sort".to_string(),
                found: format!("{:?}", sorts.get(sort)),
                context: "bv_extract operand".to_string(),
            }),
        }
    }

    /// Bit-Vector concatenation: `(concat a b)`.
    pub fn bv_concat(&mut self, a: TermId, b: TermId, sorts: &mut SortArena) -> SmtResult<TermId> {
        let sort_a = self.sort_of(a);
        let sort_b = self.sort_of(b);
        let w_a = match sorts.get(sort_a) {
            Sort::BitVec(w) => *w,
            _ => {
                return Err(SmtError::Type {
                    expected: "BitVec".to_string(),
                    found: format!("{:?}", sorts.get(sort_a)),
                    context: "concat left arg".to_string(),
                })
            }
        };
        let w_b = match sorts.get(sort_b) {
            Sort::BitVec(w) => *w,
            _ => {
                return Err(SmtError::Type {
                    expected: "BitVec".to_string(),
                    found: format!("{:?}", sorts.get(sort_b)),
                    context: "concat right arg".to_string(),
                })
            }
        };
        let res_sort = sorts.bv(w_a + w_b);
        Ok(self.intern(Op::BvConcat, vec![a, b], res_sort))
    }

    /// Int constant.
    pub fn int_const(&mut self, value: BigInt, sorts: &SortArena) -> TermId {
        self.intern(Op::IntConst(value), Vec::new(), sorts.int_sort)
    }

    /// Real constant.
    pub fn real_const(&mut self, value: BigRational, sorts: &SortArena) -> TermId {
        self.intern(Op::RealConst(value), Vec::new(), sorts.real_sort)
    }

    /// Array select: `(select arr idx)`.
    pub fn select(&mut self, arr: TermId, idx: TermId, sorts: &SortArena) -> SmtResult<TermId> {
        let arr_sort = self.sort_of(arr);
        match sorts.get(arr_sort) {
            Sort::Array { index, element } => {
                let idx_sort = self.sort_of(idx);
                if *index != idx_sort {
                    return Err(SmtError::Type {
                        expected: format!("{}", index),
                        found: format!("{}", idx_sort),
                        context: "array select index".to_string(),
                    });
                }
                Ok(self.intern(Op::Select, vec![arr, idx], *element))
            }
            _ => Err(SmtError::Type {
                expected: "Array sort".to_string(),
                found: format!("{:?}", sorts.get(arr_sort)),
                context: "array select base".to_string(),
            }),
        }
    }

    /// Array store: `(store arr idx val)`.
    pub fn store(
        &mut self,
        arr: TermId,
        idx: TermId,
        val: TermId,
        sorts: &SortArena,
    ) -> SmtResult<TermId> {
        let arr_sort = self.sort_of(arr);
        match sorts.get(arr_sort) {
            Sort::Array { index, element } => {
                let idx_sort = self.sort_of(idx);
                let val_sort = self.sort_of(val);
                if *index != idx_sort {
                    return Err(SmtError::Type {
                        expected: format!("{}", index),
                        found: format!("{}", idx_sort),
                        context: "array store index".to_string(),
                    });
                }
                if *element != val_sort {
                    return Err(SmtError::Type {
                        expected: format!("{}", element),
                        found: format!("{}", val_sort),
                        context: "array store value".to_string(),
                    });
                }
                Ok(self.intern(Op::Store, vec![arr, idx, val], arr_sort))
            }
            _ => Err(SmtError::Type {
                expected: "Array sort".to_string(),
                found: format!("{:?}", sorts.get(arr_sort)),
                context: "array store base".to_string(),
            }),
        }
    }

    /// Uninterpreted function application: `(apply fname args...)`.
    pub fn apply(
        &mut self,
        name: impl Into<String>,
        args: Vec<TermId>,
        return_sort: SortId,
    ) -> TermId {
        self.intern(Op::Apply(name.into()), args, return_sort)
    }

    /// Formats an interned term recursively into standard SMT-LIB2 syntax.
    pub fn display_term(&self, id: TermId) -> String {
        let term = self.get(id);
        if term.args.is_empty() {
            match &term.op {
                Op::True => "true".to_string(),
                Op::False => "false".to_string(),
                Op::Var(v) => v.clone(),
                Op::BvConst { value, width } => {
                    let hex_len = width.div_ceil(4) as usize;
                    format!("#x{:0>width$x}", value, width = hex_len)
                }
                Op::IntConst(i) => {
                    if i < &BigInt::from(0) {
                        format!("(- {})", -i)
                    } else {
                        format!("{}", i)
                    }
                }
                Op::RealConst(r) => {
                    if r.is_integer() {
                        format!("{}.0", r.to_integer())
                    } else {
                        format!("(/ {} {})", r.numer(), r.denom())
                    }
                }
                Op::ConstArray(sort) => format!("((as const (Array _ _)) {})", sort),
                _ => format!("{:?}", term.op),
            }
        } else {
            let rendered_args: Vec<String> =
                term.args.iter().map(|&a| self.display_term(a)).collect();
            let op_str = match &term.op {
                Op::Not => "not".to_string(),
                Op::And => "and".to_string(),
                Op::Or => "or".to_string(),
                Op::Xor => "xor".to_string(),
                Op::Implies => "=>".to_string(),
                Op::Ite => "ite".to_string(),
                Op::Eq => "=".to_string(),
                Op::Distinct => "distinct".to_string(),
                Op::BvAdd => "bvadd".to_string(),
                Op::BvSub => "bvsub".to_string(),
                Op::BvMul => "bvmul".to_string(),
                Op::BvUdiv => "bvudiv".to_string(),
                Op::BvSdiv => "bvsdiv".to_string(),
                Op::BvUrem => "bvurem".to_string(),
                Op::BvSrem => "bvsrem".to_string(),
                Op::BvSmod => "bvsmod".to_string(),
                Op::BvNeg => "bvneg".to_string(),
                Op::BvAnd => "bvand".to_string(),
                Op::BvOr => "bvor".to_string(),
                Op::BvXor => "bvxor".to_string(),
                Op::BvNot => "bvnot".to_string(),
                Op::BvNand => "bvnand".to_string(),
                Op::BvNor => "bvnor".to_string(),
                Op::BvXnor => "bvxnor".to_string(),
                Op::BvShl => "bvshl".to_string(),
                Op::BvLshr => "bvlshr".to_string(),
                Op::BvAshr => "bvashr".to_string(),
                Op::BvRotateLeft(n) => format!("(_ rotate_left {})", n),
                Op::BvRotateRight(n) => format!("(_ rotate_right {})", n),
                Op::BvConcat => "concat".to_string(),
                Op::BvExtract { high, low } => format!("(_ extract {} {})", high, low),
                Op::BvSignExtend(n) => format!("(_ sign_extend {})", n),
                Op::BvZeroExtend(n) => format!("(_ zero_extend {})", n),
                Op::BvRepeat(n) => format!("(_ repeat {})", n),
                Op::BvUlt => "bvult".to_string(),
                Op::BvUle => "bvule".to_string(),
                Op::BvUgt => "bvugt".to_string(),
                Op::BvUge => "bvuge".to_string(),
                Op::BvSlt => "bvslt".to_string(),
                Op::BvSle => "bvsle".to_string(),
                Op::BvSgt => "bvsgt".to_string(),
                Op::BvSge => "bvsge".to_string(),
                Op::Add => "+".to_string(),
                Op::Sub => "-".to_string(),
                Op::Mul => "*".to_string(),
                Op::Div => "/".to_string(),
                Op::Mod => "mod".to_string(),
                Op::Rem => "rem".to_string(),
                Op::Neg => "-".to_string(),
                Op::Lt => "<".to_string(),
                Op::Le => "<=".to_string(),
                Op::Gt => ">".to_string(),
                Op::Ge => ">=".to_string(),
                Op::ToReal => "to_real".to_string(),
                Op::ToInt => "to_int".to_string(),
                Op::IsInt => "is_int".to_string(),
                Op::Select => "select".to_string(),
                Op::Store => "store".to_string(),
                Op::Apply(name) => name.clone(),
                _ => format!("{:?}", term.op),
            };
            format!("({} {})", op_str, rendered_args.join(" "))
        }
    }
}
