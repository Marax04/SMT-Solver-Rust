//! Concrete binary lifting and symbolic execution pipeline.
//!
//! Bridges low-level disassembly IR instructions (x86_64 / ARM64 style),
//! builds symbolic path conditions, applies MBA deobfuscation, and eliminates
//! opaque branches/dead code via the SMT solver oracle.

use crate::engine::{CheckSatResult, Solver};
use smt_core::sort::SortArena;
use smt_core::term::{Op, TermArena, TermId};
use smt_mba::MbaSimplifier;
use std::collections::HashMap;

/// Low-level operand representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    /// Named register with bit width (e.g. ("rax", 64), ("eax", 32)).
    Reg(String, u32),
    /// Immediate constant value with bit width.
    Imm(u64, u32),
}

/// Conditional branch predicates for control flow transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchCondition {
    Equal,
    NotEqual,
    Zero,
    NotZero,
    UnsignedLess,
    UnsignedGreaterEqual,
}

/// Basic IR instructions lifted from machine code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrInstruction {
    Mov {
        dst: Operand,
        src: Operand,
    },
    Add {
        dst: Operand,
        src: Operand,
    },
    Sub {
        dst: Operand,
        src: Operand,
    },
    Xor {
        dst: Operand,
        src: Operand,
    },
    And {
        dst: Operand,
        src: Operand,
    },
    Or {
        dst: Operand,
        src: Operand,
    },
    Cmp {
        left: Operand,
        right: Operand,
    },
    Jcc {
        cond: BranchCondition,
        target_true: u64,
        target_false: u64,
    },
    Jmp {
        target: u64,
    },
}

/// A basic block consisting of a linear sequence of IR instructions.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub address: u64,
    pub instructions: Vec<IrInstruction>,
}

impl BasicBlock {
    pub fn new(address: u64) -> Self {
        Self {
            address,
            instructions: Vec::new(),
        }
    }

    pub fn push(&mut self, inst: IrInstruction) {
        self.instructions.push(inst);
    }
}

/// Outcome of analyzing and pruning a conditional branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BranchResolution {
    /// The branch condition is invariant: execution unconditionally branches to target.
    Deterministic(u64),
    /// The branch is genuinely dynamic depending on symbolic inputs.
    Conditional { true_target: u64, false_target: u64 },
    /// Both branches are unsatisfiable under current path constraints.
    Unreachable,
}

/// Symbolic lifter and path condition analyzer.
pub struct Lifter {
    pub sorts: SortArena,
    pub terms: TermArena,
    reg_state: HashMap<String, TermId>,
    zero_flag: Option<TermId>,
}

impl Default for Lifter {
    fn default() -> Self {
        Self::new()
    }
}

impl Lifter {
    pub fn new() -> Self {
        let mut sorts = SortArena::new();
        let terms = TermArena::new(&mut sorts);
        Self {
            sorts,
            terms,
            reg_state: HashMap::new(),
            zero_flag: None,
        }
    }

    /// Initializes a symbolic register as an unconstrained free input variable.
    pub fn init_register(&mut self, name: &str, width: u32) -> TermId {
        let sort = self.sorts.bv(width);
        let var = self.terms.var(name, sort);
        self.reg_state.insert(name.to_string(), var);
        var
    }

    /// Gets or creates the symbolic term for an operand.
    pub fn eval_operand(&mut self, op: &Operand) -> TermId {
        match op {
            Operand::Reg(name, width) => {
                if let Some(&term) = self.reg_state.get(name) {
                    term
                } else {
                    self.init_register(name, *width)
                }
            }
            Operand::Imm(val, width) => self.terms.bv_const((*val).into(), *width, &mut self.sorts),
        }
    }

    /// Executes a single instruction symbolically, updating internal register and flag states.
    pub fn step(&mut self, inst: &IrInstruction) {
        match inst {
            IrInstruction::Mov { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let src_term = self.eval_operand(src);
                    self.reg_state.insert(name.clone(), src_term);
                }
            }
            IrInstruction::Add { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let d = self.eval_operand(dst);
                    let s = self.eval_operand(src);
                    if let Ok(res) = self.terms.bv_binop(Op::BvAdd, d, s) {
                        self.reg_state.insert(name.clone(), res);
                    }
                }
            }
            IrInstruction::Sub { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let d = self.eval_operand(dst);
                    let s = self.eval_operand(src);
                    if let Ok(res) = self.terms.bv_binop(Op::BvSub, d, s) {
                        self.reg_state.insert(name.clone(), res);
                    }
                }
            }
            IrInstruction::Xor { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let d = self.eval_operand(dst);
                    let s = self.eval_operand(src);
                    if let Ok(res) = self.terms.bv_binop(Op::BvXor, d, s) {
                        self.reg_state.insert(name.clone(), res);
                    }
                }
            }
            IrInstruction::And { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let d = self.eval_operand(dst);
                    let s = self.eval_operand(src);
                    if let Ok(res) = self.terms.bv_binop(Op::BvAnd, d, s) {
                        self.reg_state.insert(name.clone(), res);
                    }
                }
            }
            IrInstruction::Or { dst, src } => {
                if let Operand::Reg(ref name, _) = dst {
                    let d = self.eval_operand(dst);
                    let s = self.eval_operand(src);
                    if let Ok(res) = self.terms.bv_binop(Op::BvOr, d, s) {
                        self.reg_state.insert(name.clone(), res);
                    }
                }
            }
            IrInstruction::Cmp { left, right } => {
                let l = self.eval_operand(left);
                let r = self.eval_operand(right);
                let zf = self.terms.eq(l, r, &self.sorts);
                self.zero_flag = Some(zf);
            }
            IrInstruction::Jcc { .. } | IrInstruction::Jmp { .. } => {}
        }
    }

    /// Lifts and executes a full basic block symbolically.
    pub fn execute_block(&mut self, block: &BasicBlock) {
        for inst in &block.instructions {
            self.step(inst);
        }
    }

    /// Simplifies all active register symbolic expressions using MBA and algebraic simplification.
    pub fn simplify_state(&mut self) {
        let mut mba = MbaSimplifier::new();
        let keys: Vec<String> = self.reg_state.keys().cloned().collect();
        for k in keys {
            if let Some(&tid) = self.reg_state.get(&k) {
                let simplified = mba.simplify(tid, &mut self.terms, &mut self.sorts);
                self.reg_state.insert(k, simplified);
            }
        }
    }

    /// Resolves the terminator of a basic block. If a conditional branch is found,
    /// queries the SMT solver to check if either target is UNSAT (opaque predicate elimination).
    pub fn resolve_branch(
        &mut self,
        terminator: &IrInstruction,
        path_constraints: &[TermId],
    ) -> BranchResolution {
        match terminator {
            IrInstruction::Jmp { target } => BranchResolution::Deterministic(*target),
            IrInstruction::Jcc {
                cond,
                target_true,
                target_false,
            } => {
                let cond_term = match cond {
                    BranchCondition::Equal | BranchCondition::Zero => {
                        self.zero_flag.expect("ZF flag required for Jcc Equal/Zero")
                    }
                    BranchCondition::NotEqual | BranchCondition::NotZero => {
                        let zf = self
                            .zero_flag
                            .expect("ZF flag required for Jcc NotEqual/NotZero");
                        self.terms.not(zf)
                    }
                    _ => {
                        return BranchResolution::Conditional {
                            true_target: *target_true,
                            false_target: *target_false,
                        }
                    }
                };

                // Check satisfiability of True branch: path_constraints && cond_term
                let true_sat = {
                    let mut solver = Solver::new();
                    solver.sorts = self.sorts.clone();
                    solver.terms = self.terms.clone();
                    solver.set_logic("QF_BV");
                    for (name, &term) in &self.reg_state {
                        let sort = self.terms.sort_of(term);
                        solver.declare_const(name, sort);
                    }
                    for &c in path_constraints {
                        solver.assert_formula(c);
                    }
                    solver.assert_formula(cond_term);
                    solver.check_sat() == CheckSatResult::Sat
                };

                // Check satisfiability of False branch: path_constraints && !cond_term
                let not_cond = self.terms.not(cond_term);
                let false_sat = {
                    let mut solver = Solver::new();
                    solver.sorts = self.sorts.clone();
                    solver.terms = self.terms.clone();
                    solver.set_logic("QF_BV");
                    for (name, &term) in &self.reg_state {
                        let sort = self.terms.sort_of(term);
                        solver.declare_const(name, sort);
                    }
                    for &c in path_constraints {
                        solver.assert_formula(c);
                    }
                    solver.assert_formula(not_cond);
                    solver.check_sat() == CheckSatResult::Sat
                };

                match (true_sat, false_sat) {
                    (true, false) => BranchResolution::Deterministic(*target_true),
                    (false, true) => BranchResolution::Deterministic(*target_false),
                    (true, true) => BranchResolution::Conditional {
                        true_target: *target_true,
                        false_target: *target_false,
                    },
                    (false, false) => BranchResolution::Unreachable,
                }
            }
            _ => BranchResolution::Unreachable,
        }
    }
}
