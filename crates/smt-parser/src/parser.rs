//! SMT-LIB 2.6 Full Command & Term Parser.

use crate::ast::Command;
use crate::lexer::Token;
use crate::sexpr::{parse_sexprs, SExpr};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use smt_core::diagnostics::{SmtError, Span};
use smt_core::sort::{Sort, SortArena, SortId};
use smt_core::term::{Op, TermArena, TermId};
use std::collections::HashMap;

/// Parser translating S-expressions into SMT-LIB commands and Hash-consed terms.
pub struct Parser<'a> {
    pub sorts: &'a mut SortArena,
    pub terms: &'a mut TermArena,
    sort_env: HashMap<String, SortId>,
    var_env: HashMap<String, SortId>,
    fun_env: HashMap<String, (Vec<SortId>, SortId)>,
    let_scopes: Vec<HashMap<String, TermId>>,
}

impl<'a> Parser<'a> {
    /// Creates a new parser pre-loaded with core types.
    ///
    /// # Example
    /// ```rust
    /// use smt_core::sort::SortArena;
    /// use smt_core::term::TermArena;
    /// use smt_parser::Parser;
    /// let mut sorts = SortArena::new();
    /// let mut terms = TermArena::new(&mut sorts);
    /// let parser = Parser::new(&mut sorts, &mut terms);
    /// ```
    pub fn new(sorts: &'a mut SortArena, terms: &'a mut TermArena) -> Self {
        let mut sort_env = HashMap::new();
        sort_env.insert("Bool".to_string(), sorts.bool_sort);
        sort_env.insert("Int".to_string(), sorts.int_sort);
        sort_env.insert("Real".to_string(), sorts.real_sort);

        Self {
            sorts,
            terms,
            sort_env,
            var_env: HashMap::new(),
            fun_env: HashMap::new(),
            let_scopes: Vec::new(),
        }
    }

    /// Parses an entire SMT-LIB2 script string.
    ///
    /// # Example
    /// ```rust
    /// use smt_core::sort::SortArena;
    /// use smt_core::term::TermArena;
    /// use smt_parser::Parser;
    /// let mut sorts = SortArena::new();
    /// let mut terms = TermArena::new(&mut sorts);
    /// let mut parser = Parser::new(&mut sorts, &mut terms);
    /// let cmds = parser.parse_script("(check-sat)").unwrap();
    /// assert_eq!(cmds.len(), 1);
    /// ```
    pub fn parse_script(&mut self, input: &str) -> Result<Vec<Command>, SmtError> {
        let sexprs = parse_sexprs(input)?;
        let mut commands = Vec::with_capacity(sexprs.len());
        for expr in &sexprs {
            commands.push(self.parse_command(expr)?);
        }
        Ok(commands)
    }

    /// Parses a single top-level command.
    pub fn parse_command(&mut self, expr: &SExpr) -> Result<Command, SmtError> {
        let list = match expr {
            SExpr::List(l, _) if !l.is_empty() => l,
            _ => {
                return Err(SmtError::Parse {
                    message: "Expected command list: (cmd args...)".to_string(),
                    span: expr.span(),
                })
            }
        };

        let cmd_name = match &list[0] {
            SExpr::Atom(Token::Symbol(s), _) => s.as_str(),
            _ => {
                return Err(SmtError::Parse {
                    message: "Expected command name symbol".to_string(),
                    span: list[0].span(),
                })
            }
        };

        match cmd_name {
            "set-logic" => {
                let logic = self.expect_symbol(&list[1])?;
                Ok(Command::SetLogic(logic.to_string()))
            }
            "set-info" => {
                let kw = self.expect_keyword_or_symbol(&list[1])?;
                let val = format!("{:?}", list[2]);
                Ok(Command::SetInfo(kw, val))
            }
            "set-option" => {
                let kw = self.expect_keyword_or_symbol(&list[1])?;
                let val = format!("{:?}", list[2]);
                Ok(Command::SetOption(kw, val))
            }
            "declare-sort" => {
                let name = self.expect_symbol(&list[1])?;
                let arity = if list.len() > 2 {
                    self.expect_numeral(&list[2])?.to_u32().unwrap_or(0)
                } else {
                    0
                };
                let id = self.sorts.uninterpreted(name);
                self.sort_env.insert(name.to_string(), id);
                Ok(Command::DeclareSort(name.to_string(), arity))
            }
            "declare-const" => {
                let name = self.expect_symbol(&list[1])?;
                let sort = self.parse_sort(&list[2])?;
                self.var_env.insert(name.to_string(), sort);
                Ok(Command::DeclareConst(name.to_string(), sort))
            }
            "declare-fun" => {
                let name = self.expect_symbol(&list[1])?;
                let arg_sorts = match &list[2] {
                    SExpr::List(args, _) => {
                        let mut res = Vec::with_capacity(args.len());
                        for a in args {
                            res.push(self.parse_sort(a)?);
                        }
                        res
                    }
                    _ => {
                        return Err(SmtError::Parse {
                            message: "Expected argument sorts list in declare-fun".to_string(),
                            span: list[2].span(),
                        })
                    }
                };
                let ret_sort = self.parse_sort(&list[3])?;

                if arg_sorts.is_empty() {
                    self.var_env.insert(name.to_string(), ret_sort);
                } else {
                    self.fun_env
                        .insert(name.to_string(), (arg_sorts.clone(), ret_sort));
                }

                Ok(Command::DeclareFun(name.to_string(), arg_sorts, ret_sort))
            }
            "assert" => {
                let term = self.parse_term(&list[1])?;
                Ok(Command::Assert(term))
            }
            "check-sat" => Ok(Command::CheckSat),
            "check-sat-assuming" => {
                let prop_list = match &list[1] {
                    SExpr::List(l, _) => l,
                    _ => {
                        return Err(SmtError::Parse {
                            message: "Expected proposition list in check-sat-assuming".to_string(),
                            span: list[1].span(),
                        })
                    }
                };
                let mut props = Vec::with_capacity(prop_list.len());
                for p in prop_list {
                    props.push(self.parse_term(p)?);
                }
                Ok(Command::CheckSatAssuming(props))
            }
            "get-model" => Ok(Command::GetModel),
            "get-unsat-core" => Ok(Command::GetUnsatCore),
            "get-value" => {
                let terms_list = match &list[1] {
                    SExpr::List(l, _) => l,
                    _ => {
                        return Err(SmtError::Parse {
                            message: "Expected terms list in get-value".to_string(),
                            span: list[1].span(),
                        })
                    }
                };
                let mut terms = Vec::with_capacity(terms_list.len());
                for t in terms_list {
                    terms.push(self.parse_term(t)?);
                }
                Ok(Command::GetValue(terms))
            }
            "push" => {
                let n = if list.len() > 1 {
                    self.expect_numeral(&list[1])?.to_u32().unwrap_or(1)
                } else {
                    1
                };
                Ok(Command::Push(n))
            }
            "pop" => {
                let n = if list.len() > 1 {
                    self.expect_numeral(&list[1])?.to_u32().unwrap_or(1)
                } else {
                    1
                };
                Ok(Command::Pop(n))
            }
            "reset" => Ok(Command::Reset),
            "exit" => Ok(Command::Exit),
            _ => Err(SmtError::Parse {
                message: format!("Unknown command: '{}'", cmd_name),
                span: expr.span(),
            }),
        }
    }

    /// Parses a sort expression into a SortId.
    pub fn parse_sort(&mut self, expr: &SExpr) -> Result<SortId, SmtError> {
        match expr {
            SExpr::Atom(Token::Symbol(name), span) => {
                if let Some(&id) = self.sort_env.get(name) {
                    Ok(id)
                } else {
                    Err(SmtError::Parse {
                        message: format!("Undefined sort: '{}'", name),
                        span: *span,
                    })
                }
            }
            SExpr::List(list, span) => {
                if list.is_empty() {
                    return Err(SmtError::Parse {
                        message: "Empty sort expression".to_string(),
                        span: *span,
                    });
                }
                // (_ BitVec m)
                if list.len() == 3
                    && list[0].as_symbol() == Some("_")
                    && list[1].as_symbol() == Some("BitVec")
                {
                    let width =
                        self.expect_numeral(&list[2])?
                            .to_u32()
                            .ok_or_else(|| SmtError::Parse {
                                message: "Invalid bit-width".to_string(),
                                span: list[2].span(),
                            })?;
                    let id = self.sorts.bv(width);
                    return Ok(id);
                }
                // (Array Index Element)
                if list.len() == 3 && list[0].as_symbol() == Some("Array") {
                    let index_sort = self.parse_sort(&list[1])?;
                    let elem_sort = self.parse_sort(&list[2])?;
                    let id = self.sorts.array(index_sort, elem_sort);
                    return Ok(id);
                }

                Err(SmtError::Parse {
                    message: "Unrecognized parametric sort".to_string(),
                    span: *span,
                })
            }
            _ => Err(SmtError::Parse {
                message: "Expected sort expression".to_string(),
                span: expr.span(),
            }),
        }
    }

    /// Parses a term S-expression into a hash-consed TermId.
    pub fn parse_term(&mut self, expr: &SExpr) -> Result<TermId, SmtError> {
        match expr {
            SExpr::Atom(token, span) => match token {
                Token::Symbol(sym) => {
                    if sym == "true" {
                        return Ok(self.terms.true_id);
                    }
                    if sym == "false" {
                        return Ok(self.terms.false_id);
                    }
                    // Check let scopes
                    for scope in self.let_scopes.iter().rev() {
                        if let Some(&id) = scope.get(sym) {
                            return Ok(id);
                        }
                    }
                    // Check declared variable
                    if let Some(&sort) = self.var_env.get(sym) {
                        return Ok(self.terms.var(sym, sort));
                    }
                    Err(SmtError::Parse {
                        message: format!("Undefined symbol: '{}'", sym),
                        span: *span,
                    })
                }
                Token::Numeral(num) => Ok(self.terms.int_const(num.clone(), self.sorts)),
                Token::Decimal(dec) => Ok(self.terms.real_const(dec.clone(), self.sorts)),
                Token::HexLiteral { value, width } => {
                    Ok(self.terms.bv_const(value.clone(), *width, self.sorts))
                }
                Token::BinaryLiteral { value, width } => {
                    Ok(self.terms.bv_const(value.clone(), *width, self.sorts))
                }
                _ => Err(SmtError::Parse {
                    message: "Unexpected atom in term".to_string(),
                    span: *span,
                }),
            },
            SExpr::List(list, span) => {
                if list.is_empty() {
                    return Err(SmtError::Parse {
                        message: "Empty term expression".to_string(),
                        span: *span,
                    });
                }

                // Handle bit-vector constants: (_ bvX m)
                if list[0].as_symbol() == Some("_") && list.len() == 3 {
                    if let Some(sym) = list[1].as_symbol() {
                        if let Some(stripped) = sym.strip_prefix("bv") {
                            if let Ok(val) = stripped.parse::<BigUint>() {
                                let width = self.expect_numeral(&list[2])?.to_u32().unwrap();
                                return Ok(self.terms.bv_const(val, width, self.sorts));
                            }
                        }
                    }
                }

                // Handle (let ((v1 t1) ...) body)
                if list[0].as_symbol() == Some("let") {
                    return self.parse_let(list, *span);
                }

                // Handle indexed operators: ((_ extract high low) term), ((_ zero_extend n) term), ((_ sign_extend n) term)
                if let SExpr::List(op_list, _) = &list[0] {
                    if !op_list.is_empty() && op_list[0].as_symbol() == Some("_") {
                        let indexed_op = op_list[1].as_symbol().unwrap_or("");
                        match indexed_op {
                            "extract" => {
                                let high = self.expect_numeral(&op_list[2])?.to_u32().unwrap();
                                let low = self.expect_numeral(&op_list[3])?.to_u32().unwrap();
                                let arg = self.parse_term(&list[1])?;
                                return self.terms.bv_extract(high, low, arg, self.sorts);
                            }
                            "zero_extend" => {
                                let n = self.expect_numeral(&op_list[2])?.to_u32().unwrap();
                                let arg = self.parse_term(&list[1])?;
                                let zeroes =
                                    self.terms.bv_const(BigUint::from(0u32), n, self.sorts);
                                return self.terms.bv_concat(zeroes, arg, self.sorts);
                            }
                            "sign_extend" => {
                                let n = self.expect_numeral(&op_list[2])?.to_u32().unwrap();
                                let arg = self.parse_term(&list[1])?;
                                let arg_sort = self.terms.sort_of(arg);
                                let w = match self.sorts.get(arg_sort) {
                                    Sort::BitVec(w) => *w,
                                    _ => 1,
                                };
                                let res_sort = self.sorts.bv(w + n);
                                return Ok(self.terms.intern(
                                    Op::BvSignExtend(n),
                                    vec![arg],
                                    res_sort,
                                ));
                            }
                            _ => {}
                        }
                    }
                }

                let op_sym = match &list[0] {
                    SExpr::Atom(Token::Symbol(s), _) => s.as_str(),
                    _ => {
                        return Err(SmtError::Parse {
                            message: "Expected operator symbol".to_string(),
                            span: list[0].span(),
                        })
                    }
                };

                let mut arg_terms = Vec::with_capacity(list.len() - 1);
                for arg_expr in &list[1..] {
                    arg_terms.push(self.parse_term(arg_expr)?);
                }

                self.construct_op(op_sym, arg_terms, *span)
            }
        }
    }

    fn construct_op(
        &mut self,
        op_sym: &str,
        args: Vec<TermId>,
        span: Span,
    ) -> Result<TermId, SmtError> {
        match op_sym {
            "not" => Ok(self.terms.not(args[0])),
            "and" => Ok(self.terms.and(args, self.sorts)),
            "or" => Ok(self.terms.or(args, self.sorts)),
            "xor" => Ok(self.terms.xor(args[0], args[1], self.sorts)),
            "=>" => Ok(self.terms.implies(args[0], args[1], self.sorts)),
            "ite" => Ok(self.terms.ite(args[0], args[1], args[2])),
            "=" => Ok(self.terms.eq(args[0], args[1], self.sorts)),
            "distinct" => Ok(self.terms.distinct(args, self.sorts)),
            // Bit-vectors
            "bvadd" => self.terms.bv_binop(Op::BvAdd, args[0], args[1]),
            "bvsub" => self.terms.bv_binop(Op::BvSub, args[0], args[1]),
            "bvmul" => self.terms.bv_binop(Op::BvMul, args[0], args[1]),
            "bvudiv" => self.terms.bv_binop(Op::BvUdiv, args[0], args[1]),
            "bvsdiv" => self.terms.bv_binop(Op::BvSdiv, args[0], args[1]),
            "bvurem" => self.terms.bv_binop(Op::BvUrem, args[0], args[1]),
            "bvsrem" => self.terms.bv_binop(Op::BvSrem, args[0], args[1]),
            "bvand" => self.terms.bv_binop(Op::BvAnd, args[0], args[1]),
            "bvor" => self.terms.bv_binop(Op::BvOr, args[0], args[1]),
            "bvxor" => self.terms.bv_binop(Op::BvXor, args[0], args[1]),
            "bvnot" => {
                let sort = self.terms.sort_of(args[0]);
                Ok(self.terms.intern(Op::BvNot, vec![args[0]], sort))
            }
            "bvneg" => {
                let sort = self.terms.sort_of(args[0]);
                Ok(self.terms.intern(Op::BvNeg, vec![args[0]], sort))
            }
            "bvshl" => self.terms.bv_binop(Op::BvShl, args[0], args[1]),
            "bvlshr" => self.terms.bv_binop(Op::BvLshr, args[0], args[1]),
            "bvashr" => self.terms.bv_binop(Op::BvAshr, args[0], args[1]),
            "concat" => self.terms.bv_concat(args[0], args[1], self.sorts),
            "bvult" => Ok(self.terms.intern(Op::BvUlt, args, self.sorts.bool_sort)),
            "bvule" => Ok(self.terms.intern(Op::BvUle, args, self.sorts.bool_sort)),
            "bvugt" => Ok(self.terms.intern(Op::BvUgt, args, self.sorts.bool_sort)),
            "bvuge" => Ok(self.terms.intern(Op::BvUge, args, self.sorts.bool_sort)),
            "bvslt" => Ok(self.terms.intern(Op::BvSlt, args, self.sorts.bool_sort)),
            "bvsle" => Ok(self.terms.intern(Op::BvSle, args, self.sorts.bool_sort)),
            "bvsgt" => Ok(self.terms.intern(Op::BvSgt, args, self.sorts.bool_sort)),
            "bvsge" => Ok(self.terms.intern(Op::BvSge, args, self.sorts.bool_sort)),
            // Arithmetic
            "+" => {
                let sort = self.terms.sort_of(args[0]);
                Ok(self.terms.intern(Op::Add, args, sort))
            }
            "-" => {
                let sort = self.terms.sort_of(args[0]);
                if args.len() == 1 {
                    Ok(self.terms.intern(Op::Neg, args, sort))
                } else {
                    Ok(self.terms.intern(Op::Sub, args, sort))
                }
            }
            "*" => {
                let sort = self.terms.sort_of(args[0]);
                Ok(self.terms.intern(Op::Mul, args, sort))
            }
            "/" => Ok(self.terms.intern(Op::Div, args, self.sorts.real_sort)),
            "<" => Ok(self.terms.intern(Op::Lt, args, self.sorts.bool_sort)),
            "<=" => Ok(self.terms.intern(Op::Le, args, self.sorts.bool_sort)),
            ">" => Ok(self.terms.intern(Op::Gt, args, self.sorts.bool_sort)),
            ">=" => Ok(self.terms.intern(Op::Ge, args, self.sorts.bool_sort)),
            // Arrays
            "select" => self.terms.select(args[0], args[1], self.sorts),
            "store" => self.terms.store(args[0], args[1], args[2], self.sorts),
            // Uninterpreted function call
            func_name => {
                if let Some((_, ret_sort)) = self.fun_env.get(func_name) {
                    Ok(self.terms.apply(func_name, args, *ret_sort))
                } else {
                    Err(SmtError::Parse {
                        message: format!("Unknown function or operator: '{}'", func_name),
                        span,
                    })
                }
            }
        }
    }

    fn parse_let(&mut self, list: &[SExpr], span: Span) -> Result<TermId, SmtError> {
        if list.len() < 3 {
            return Err(SmtError::Parse {
                message: "Malformed let expression: expected (let ((v1 t1)...) body)".to_string(),
                span,
            });
        }
        let bindings_expr = match &list[1] {
            SExpr::List(b, _) => b,
            _ => {
                return Err(SmtError::Parse {
                    message: "Expected bindings list in let".to_string(),
                    span: list[1].span(),
                })
            }
        };

        let mut scope = HashMap::new();
        for b in bindings_expr {
            if let SExpr::List(pair, _) = b {
                let var_name = self.expect_symbol(&pair[0])?;
                let val_term = self.parse_term(&pair[1])?;
                scope.insert(var_name.to_string(), val_term);
            }
        }

        self.let_scopes.push(scope);
        let res = self.parse_term(&list[2]);
        self.let_scopes.pop();
        res
    }

    fn expect_symbol<'b>(&self, expr: &'b SExpr) -> Result<&'b str, SmtError> {
        match expr {
            SExpr::Atom(Token::Symbol(s), _) => Ok(s.as_str()),
            _ => Err(SmtError::Parse {
                message: "Expected symbol".to_string(),
                span: expr.span(),
            }),
        }
    }

    fn expect_keyword_or_symbol(&self, expr: &SExpr) -> Result<String, SmtError> {
        match expr {
            SExpr::Atom(Token::Keyword(k), _) => Ok(k.clone()),
            SExpr::Atom(Token::Symbol(s), _) => Ok(s.clone()),
            _ => Err(SmtError::Parse {
                message: "Expected keyword or symbol".to_string(),
                span: expr.span(),
            }),
        }
    }

    fn expect_numeral<'b>(&self, expr: &'b SExpr) -> Result<&'b num_bigint::BigInt, SmtError> {
        match expr {
            SExpr::Atom(Token::Numeral(n), _) => Ok(n),
            _ => Err(SmtError::Parse {
                message: "Expected numeral".to_string(),
                span: expr.span(),
            }),
        }
    }
}
