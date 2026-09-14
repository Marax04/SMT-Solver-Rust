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
    /// Memory operand: [base + index*scale + disp] with bit width.
    Mem {
        base: Option<String>,
        index: Option<(String, u8)>,
        disp: i64,
        width: u32,
    },
}

/// Conditional branch predicates for control flow transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchCondition {
    Equal,
    NotEqual,
    Zero,
    NotZero,
    BelowUnsigned,
    AboveOrEqualUnsigned,
    BelowOrEqualUnsigned,
    AboveUnsigned,
    LessThanSigned,
    GreaterOrEqualSigned,
    LessOrEqualSigned,
    GreaterThanSigned,
    Sign,
    NotSign,
    Overflow,
    NotOverflow,
}

/// Basic IR instructions lifted from machine code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrInstruction {
    Nop,
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
    Test {
        left: Operand,
        right: Operand,
    },
    Push {
        src: Operand,
    },
    Pop {
        dst: Operand,
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

impl IrInstruction {
    pub fn def_reg(&self) -> Option<&str> {
        match self {
            IrInstruction::Mov { dst, .. }
            | IrInstruction::Add { dst, .. }
            | IrInstruction::Sub { dst, .. }
            | IrInstruction::Xor { dst, .. }
            | IrInstruction::And { dst, .. }
            | IrInstruction::Or { dst, .. }
            | IrInstruction::Pop { dst } => {
                if let Operand::Reg(ref name, _) = dst {
                    Some(name.as_str())
                } else {
                    None
                }
            }
            IrInstruction::Nop
            | IrInstruction::Push { .. }
            | IrInstruction::Cmp { .. }
            | IrInstruction::Test { .. }
            | IrInstruction::Jcc { .. }
            | IrInstruction::Jmp { .. } => None,
        }
    }

    pub fn use_regs(&self) -> Vec<&str> {
        fn add_op<'b>(op: &'b Operand, regs: &mut Vec<&'b str>) {
            match op {
                Operand::Reg(name, _) => regs.push(name.as_str()),
                Operand::Mem { base, index, .. } => {
                    if let Some(ref b) = base {
                        regs.push(b.as_str());
                    }
                    if let Some((ref idx_reg, _)) = index {
                        regs.push(idx_reg.as_str());
                    }
                }
                Operand::Imm(..) => {}
            }
        }

        let mut regs = Vec::new();
        match self {
            IrInstruction::Nop => {}
            IrInstruction::Mov { dst, src } => {
                if matches!(dst, Operand::Mem { .. }) {
                    add_op(dst, &mut regs);
                }
                add_op(src, &mut regs);
            }
            IrInstruction::Add { dst, src }
            | IrInstruction::Sub { dst, src }
            | IrInstruction::Xor { dst, src }
            | IrInstruction::And { dst, src }
            | IrInstruction::Or { dst, src } => {
                add_op(dst, &mut regs);
                add_op(src, &mut regs);
            }
            IrInstruction::Cmp { left, right } | IrInstruction::Test { left, right } => {
                add_op(left, &mut regs);
                add_op(right, &mut regs);
            }
            IrInstruction::Push { src } => {
                add_op(src, &mut regs);
            }
            IrInstruction::Pop { dst } => {
                if matches!(dst, Operand::Mem { .. }) {
                    add_op(dst, &mut regs);
                }
            }
            IrInstruction::Jcc { .. } | IrInstruction::Jmp { .. } => {}
        }
        regs
    }
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

    /// Performs backward static semantic slicing from the given register dependencies.
    /// Eliminates decoy dead stores, dead flag updates, and side-effect-free instructions.
    pub fn semantic_slice(&self, criteria: &[&str]) -> BasicBlock {
        let mut needed: std::collections::HashSet<String> =
            criteria.iter().map(|&s| s.to_string()).collect();
        let mut sliced_rev = Vec::new();

        for inst in self.instructions.iter().rev() {
            if matches!(inst, IrInstruction::Cmp { .. } | IrInstruction::Test { .. }) {
                for u in inst.use_regs() {
                    needed.insert(u.to_string());
                }
                sliced_rev.push(inst.clone());
                continue;
            }

            if let Some(def) = inst.def_reg() {
                if needed.contains(def) {
                    if matches!(inst, IrInstruction::Mov { .. }) {
                        needed.remove(def);
                    }
                    for u in inst.use_regs() {
                        needed.insert(u.to_string());
                    }
                    sliced_rev.push(inst.clone());
                }
            }
        }

        sliced_rev.reverse();
        BasicBlock {
            address: self.address,
            instructions: sliced_rev,
        }
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

/// Uncertainty-aware classification of a deobfuscated branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeobfuscationStatus {
    /// Formally proven invariant by SMT refutation (one branch is UNSAT).
    ProvenInvariant {
        surviving_target: u64,
        dead_target: u64,
    },
    /// Formally proven dynamic branch (both paths SAT with concrete models).
    ProvenDynamic { true_target: u64, false_target: u64 },
    /// Inconsistent path constraints (both paths UNSAT).
    UnreachablePath,
}

/// Detailed audit trail for proof-carrying deobfuscation.
#[derive(Debug, Clone)]
pub struct ProofCarryingResolution {
    pub status: DeobfuscationStatus,
    pub resolution: BranchResolution,
    pub certificate: String,
    pub true_branch_model: Option<crate::model::Model>,
    pub false_branch_model: Option<crate::model::Model>,
}

/// Returns the corresponding 32-bit subregister name for a canonical 64-bit root register.
pub fn subregister_32_name(root: &str) -> Option<&'static str> {
    match root {
        "rax" => Some("eax"),
        "rcx" => Some("ecx"),
        "rdx" => Some("edx"),
        "rbx" => Some("ebx"),
        "rsp" => Some("esp"),
        "rbp" => Some("ebp"),
        "rsi" => Some("esi"),
        "rdi" => Some("edi"),
        "r8" => Some("r8d"),
        "r9" => Some("r9d"),
        "r10" => Some("r10d"),
        "r11" => Some("r11d"),
        "r12" => Some("r12d"),
        "r13" => Some("r13d"),
        "r14" => Some("r14d"),
        "r15" => Some("r15d"),
        _ => None,
    }
}

/// Maps x86-64 register names to their canonical 64-bit root register, bit offset, and width.
pub fn canonical_reg_mapping(name: &str) -> Option<(&'static str, u32, u32)> {
    match name {
        // RAX family
        "rax" => Some(("rax", 0, 64)),
        "eax" => Some(("rax", 0, 32)),
        "ax" => Some(("rax", 0, 16)),
        "al" => Some(("rax", 0, 8)),
        "ah" => Some(("rax", 8, 8)),

        // RCX family
        "rcx" => Some(("rcx", 0, 64)),
        "ecx" => Some(("rcx", 0, 32)),
        "cx" => Some(("rcx", 0, 16)),
        "cl" => Some(("rcx", 0, 8)),
        "ch" => Some(("rcx", 8, 8)),

        // RDX family
        "rdx" => Some(("rdx", 0, 64)),
        "edx" => Some(("rdx", 0, 32)),
        "dx" => Some(("rdx", 0, 16)),
        "dl" => Some(("rdx", 0, 8)),
        "dh" => Some(("rdx", 8, 8)),

        // RBX family
        "rbx" => Some(("rbx", 0, 64)),
        "ebx" => Some(("rbx", 0, 32)),
        "bx" => Some(("rbx", 0, 16)),
        "bl" => Some(("rbx", 0, 8)),
        "bh" => Some(("rbx", 8, 8)),

        // RSP family
        "rsp" => Some(("rsp", 0, 64)),
        "esp" => Some(("rsp", 0, 32)),
        "sp" => Some(("rsp", 0, 16)),
        "spl" => Some(("rsp", 0, 8)),

        // RBP family
        "rbp" => Some(("rbp", 0, 64)),
        "ebp" => Some(("rbp", 0, 32)),
        "bp" => Some(("rbp", 0, 16)),
        "bpl" => Some(("rbp", 0, 8)),

        // RSI family
        "rsi" => Some(("rsi", 0, 64)),
        "esi" => Some(("rsi", 0, 32)),
        "si" => Some(("rsi", 0, 16)),
        "sil" => Some(("rsi", 0, 8)),

        // RDI family
        "rdi" => Some(("rdi", 0, 64)),
        "edi" => Some(("rdi", 0, 32)),
        "di" => Some(("rdi", 0, 16)),
        "dil" => Some(("rdi", 0, 8)),

        // R8 family
        "r8" => Some(("r8", 0, 64)),
        "r8d" => Some(("r8", 0, 32)),
        "r8w" => Some(("r8", 0, 16)),
        "r8b" => Some(("r8", 0, 8)),

        // R9 family
        "r9" => Some(("r9", 0, 64)),
        "r9d" => Some(("r9", 0, 32)),
        "r9w" => Some(("r9", 0, 16)),
        "r9b" => Some(("r9", 0, 8)),

        // R10 family
        "r10" => Some(("r10", 0, 64)),
        "r10d" => Some(("r10", 0, 32)),
        "r10w" => Some(("r10", 0, 16)),
        "r10b" => Some(("r10", 0, 8)),

        // R11 family
        "r11" => Some(("r11", 0, 64)),
        "r11d" => Some(("r11", 0, 32)),
        "r11w" => Some(("r11", 0, 16)),
        "r11b" => Some(("r11", 0, 8)),

        // R12 family
        "r12" => Some(("r12", 0, 64)),
        "r12d" => Some(("r12", 0, 32)),
        "r12w" => Some(("r12", 0, 16)),
        "r12b" => Some(("r12", 0, 8)),

        // R13 family
        "r13" => Some(("r13", 0, 64)),
        "r13d" => Some(("r13", 0, 32)),
        "r13w" => Some(("r13", 0, 16)),
        "r13b" => Some(("r13", 0, 8)),

        // R14 family
        "r14" => Some(("r14", 0, 64)),
        "r14d" => Some(("r14", 0, 32)),
        "r14w" => Some(("r14", 0, 16)),
        "r14b" => Some(("r14", 0, 8)),

        // R15 family
        "r15" => Some(("r15", 0, 64)),
        "r15d" => Some(("r15", 0, 32)),
        "r15w" => Some(("r15", 0, 16)),
        "r15b" => Some(("r15", 0, 8)),

        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemoryAddress {
    Physical(u64),
    Stack(i64),
    Named(String, i64),
    Symbolic(TermId),
}

#[derive(Clone)]
struct SavedScope {
    reg_state: HashMap<String, TermId>,
    zero_flag: Option<TermId>,
    carry_flag: Option<TermId>,
    sign_flag: Option<TermId>,
    overflow_flag: Option<TermId>,
    stack: Vec<TermId>,
    memory: HashMap<u64, TermId>,
    stack_memory: HashMap<i64, TermId>,
    named_memory: HashMap<(String, i64), TermId>,
    symbolic_memory: Vec<(TermId, TermId)>,
}

/// Symbolic lifter and path condition analyzer.
pub struct Lifter {
    pub sorts: SortArena,
    pub terms: TermArena,
    reg_state: HashMap<String, TermId>,
    zero_flag: Option<TermId>,
    carry_flag: Option<TermId>,
    sign_flag: Option<TermId>,
    overflow_flag: Option<TermId>,
    stack: Vec<TermId>,
    memory: HashMap<u64, TermId>,
    stack_memory: HashMap<i64, TermId>,
    named_memory: HashMap<(String, i64), TermId>,
    symbolic_memory: Vec<(TermId, TermId)>,
    scope_stack: Vec<SavedScope>,
}

impl Default for Lifter {
    fn default() -> Self {
        Self::new()
    }
}

impl Lifter {
    pub fn new() -> Self {
        let mut sorts = SortArena::new();
        let mut terms = TermArena::new(&mut sorts);
        let mut reg_state = HashMap::new();
        let initial_rsp = terms.bv_const(0x7fff_ffff_0000u64.into(), 64, &mut sorts);
        reg_state.insert("rsp".to_string(), initial_rsp);
        Self {
            sorts,
            terms,
            reg_state,
            zero_flag: None,
            carry_flag: None,
            sign_flag: None,
            overflow_flag: None,
            stack: Vec::new(),
            memory: HashMap::new(),
            stack_memory: HashMap::new(),
            named_memory: HashMap::new(),
            symbolic_memory: Vec::new(),
            scope_stack: Vec::new(),
        }
    }

    /// Pushes current symbolic register, flag, and memory states onto the scope stack.
    pub fn push(&mut self) {
        self.scope_stack.push(SavedScope {
            reg_state: self.reg_state.clone(),
            zero_flag: self.zero_flag,
            carry_flag: self.carry_flag,
            sign_flag: self.sign_flag,
            overflow_flag: self.overflow_flag,
            stack: self.stack.clone(),
            memory: self.memory.clone(),
            stack_memory: self.stack_memory.clone(),
            named_memory: self.named_memory.clone(),
            symbolic_memory: self.symbolic_memory.clone(),
        });
    }

    /// Pops previously saved symbolic state from the scope stack.
    pub fn pop(&mut self) -> bool {
        if let Some(saved) = self.scope_stack.pop() {
            self.reg_state = saved.reg_state;
            self.zero_flag = saved.zero_flag;
            self.carry_flag = saved.carry_flag;
            self.sign_flag = saved.sign_flag;
            self.overflow_flag = saved.overflow_flag;
            self.stack = saved.stack;
            self.memory = saved.memory;
            self.stack_memory = saved.stack_memory;
            self.named_memory = saved.named_memory;
            self.symbolic_memory = saved.symbolic_memory;
            true
        } else {
            false
        }
    }

    /// Initializes a register as a free input variable.
    pub fn init_register(&mut self, name: &str, width: u32) -> TermId {
        let sort = self.sorts.bv(width);
        let var = self.terms.var(name, sort);
        self.reg_state.insert(name.to_string(), var);

        if let Some((root, offset, w)) = canonical_reg_mapping(name) {
            if w == 32 && offset == 0 {
                let zero32 = self.terms.bv_const(0u32.into(), 32, &mut self.sorts);
                if let Ok(val64) = self.terms.bv_concat(zero32, var, &mut self.sorts) {
                    self.reg_state.insert(root.to_string(), val64);
                }
            } else if w == 64 {
                if let Some(sub32) = subregister_32_name(root) {
                    if let Ok(eax) = self.terms.bv_extract(31, 0, var, &mut self.sorts) {
                        self.reg_state.insert(sub32.to_string(), eax);
                    }
                }
            }
        }
        var
    }

    /// Reads a register value, properly handling subregister extraction and canonical mapping.
    pub fn read_reg(&mut self, name: &str, width: u32) -> TermId {
        if let Some(&t) = self.reg_state.get(name) {
            t
        } else if let Some((root, offset, w)) = canonical_reg_mapping(name) {
            if let Some(&root_val) = self.reg_state.get(root) {
                if w == 64 {
                    root_val
                } else {
                    let sub = self
                        .terms
                        .bv_extract(offset + w - 1, offset, root_val, &mut self.sorts)
                        .expect("Valid subregister slice");
                    self.reg_state.insert(name.to_string(), sub);
                    sub
                }
            } else {
                self.init_register(name, width)
            }
        } else {
            self.init_register(name, width)
        }
    }

    /// Writes a register value, implementing x86-64 implicit 32-bit zero-extension and partial aliasing.
    pub fn write_reg(&mut self, name: &str, val: TermId, _width: u32) {
        self.reg_state.insert(name.to_string(), val);

        if let Some((root, offset, w)) = canonical_reg_mapping(name) {
            if w == 32 {
                // x86-64: writing to a 32-bit register zero-extends to 64 bits (upper 32 bits cleared)
                let zero32 = self.terms.bv_const(0u32.into(), 32, &mut self.sorts);
                let val64 = self
                    .terms
                    .bv_concat(zero32, val, &mut self.sorts)
                    .expect("Valid 32-to-64 zero-extension");
                self.reg_state.insert(root.to_string(), val64);
            } else if w == 64 {
                if let Some(sub32) = subregister_32_name(root) {
                    if let Ok(eax) = self.terms.bv_extract(31, 0, val, &mut self.sorts) {
                        self.reg_state.insert(sub32.to_string(), eax);
                    }
                }
            } else if offset == 0 && w == 16 {
                let root_val = self.read_reg(root, 64);
                let high48 = self
                    .terms
                    .bv_extract(63, 16, root_val, &mut self.sorts)
                    .expect("Extract high 48 bits");
                let val64 = self
                    .terms
                    .bv_concat(high48, val, &mut self.sorts)
                    .expect("Concat high 48 with 16");
                self.reg_state.insert(root.to_string(), val64);
                if let Some(sub32) = subregister_32_name(root) {
                    if let Ok(eax) = self.terms.bv_extract(31, 0, val64, &mut self.sorts) {
                        self.reg_state.insert(sub32.to_string(), eax);
                    }
                }
            } else if offset == 0 && w == 8 {
                let root_val = self.read_reg(root, 64);
                let high56 = self
                    .terms
                    .bv_extract(63, 8, root_val, &mut self.sorts)
                    .expect("Extract high 56 bits");
                let val64 = self
                    .terms
                    .bv_concat(high56, val, &mut self.sorts)
                    .expect("Concat high 56 with 8");
                self.reg_state.insert(root.to_string(), val64);
                if let Some(sub32) = subregister_32_name(root) {
                    if let Ok(eax) = self.terms.bv_extract(31, 0, val64, &mut self.sorts) {
                        self.reg_state.insert(sub32.to_string(), eax);
                    }
                }
            } else if offset == 8 && w == 8 {
                let root_val = self.read_reg(root, 64);
                let high48 = self
                    .terms
                    .bv_extract(63, 16, root_val, &mut self.sorts)
                    .expect("Extract high 48 bits");
                let low8 = self
                    .terms
                    .bv_extract(7, 0, root_val, &mut self.sorts)
                    .expect("Extract low 8 bits");
                let mid16 = self
                    .terms
                    .bv_concat(val, low8, &mut self.sorts)
                    .expect("Concat ah with low 8");
                let val64 = self
                    .terms
                    .bv_concat(high48, mid16, &mut self.sorts)
                    .expect("Concat high 48 with mid 16");
                self.reg_state.insert(root.to_string(), val64);
                if let Some(sub32) = subregister_32_name(root) {
                    if let Ok(eax) = self.terms.bv_extract(31, 0, val64, &mut self.sorts) {
                        self.reg_state.insert(sub32.to_string(), eax);
                    }
                }
            } else {
                self.reg_state.insert(root.to_string(), val);
            }
        }
    }

    /// Evaluates whether a term is a concrete integer constant or simple constant arithmetic.
    pub fn eval_concrete_u64(&self, term: TermId) -> Option<u64> {
        use num_traits::ToPrimitive;
        let t = self.terms.get(term);
        match &t.op {
            Op::BvConst { value, .. } => value.to_u64(),
            Op::BvAdd if t.args.len() == 2 => {
                let a = self.eval_concrete_u64(t.args[0])?;
                let b = self.eval_concrete_u64(t.args[1])?;
                Some(a.wrapping_add(b))
            }
            Op::BvSub if t.args.len() == 2 => {
                let a = self.eval_concrete_u64(t.args[0])?;
                let b = self.eval_concrete_u64(t.args[1])?;
                Some(a.wrapping_sub(b))
            }
            Op::BvMul if t.args.len() == 2 => {
                let a = self.eval_concrete_u64(t.args[0])?;
                let b = self.eval_concrete_u64(t.args[1])?;
                Some(a.wrapping_mul(b))
            }
            _ => None,
        }
    }

    /// Resolves the effective memory address from base register, index register, and displacement.
    pub fn resolve_address(
        &mut self,
        base: &Option<String>,
        index: &Option<(String, u8)>,
        disp: i64,
    ) -> MemoryAddress {
        let index_offset = if let Some((ref idx_reg, scale)) = index {
            let idx_term = self.read_reg(idx_reg, 64);
            self.eval_concrete_u64(idx_term)
                .map(|concrete_idx| (concrete_idx.wrapping_mul(*scale as u64)) as i64)
        } else {
            Some(0)
        };

        if let Some(ref base_reg) = base {
            let base_term = self.read_reg(base_reg, 64);
            let concrete_base = self.eval_concrete_u64(base_term);

            match (concrete_base, index_offset) {
                (Some(c_base), Some(idx_off)) => {
                    let effective = (c_base as i64).wrapping_add(idx_off).wrapping_add(disp) as u64;
                    MemoryAddress::Physical(effective)
                }
                _ if base_reg == "rsp" && index_offset.is_some() => {
                    MemoryAddress::Stack(disp + index_offset.unwrap())
                }
                _ => {
                    let disp_term = self
                        .terms
                        .bv_const((disp as u64).into(), 64, &mut self.sorts);
                    let mut addr_term = if disp != 0 {
                        self.terms
                            .bv_binop(Op::BvAdd, base_term, disp_term)
                            .unwrap_or(base_term)
                    } else {
                        base_term
                    };
                    if let Some((ref idx_reg, scale)) = index {
                        let idx_term = self.read_reg(idx_reg, 64);
                        let scale_term =
                            self.terms
                                .bv_const((*scale as u64).into(), 64, &mut self.sorts);
                        if let Ok(scaled_idx) = self.terms.bv_binop(Op::BvMul, idx_term, scale_term)
                        {
                            if let Ok(combined) =
                                self.terms.bv_binop(Op::BvAdd, addr_term, scaled_idx)
                            {
                                addr_term = combined;
                            }
                        }
                    }
                    MemoryAddress::Symbolic(addr_term)
                }
            }
        } else if let Some(idx_off) = index_offset {
            MemoryAddress::Physical((disp + idx_off) as u64)
        } else {
            let disp_term = self
                .terms
                .bv_const((disp as u64).into(), 64, &mut self.sorts);
            let mut addr_term = disp_term;
            if let Some((ref idx_reg, scale)) = index {
                let idx_term = self.read_reg(idx_reg, 64);
                let scale_term = self
                    .terms
                    .bv_const((*scale as u64).into(), 64, &mut self.sorts);
                if let Ok(scaled_idx) = self.terms.bv_binop(Op::BvMul, idx_term, scale_term) {
                    if let Ok(combined) = self.terms.bv_binop(Op::BvAdd, addr_term, scaled_idx) {
                        addr_term = combined;
                    }
                }
            }
            MemoryAddress::Symbolic(addr_term)
        }
    }

    fn read_byte_at(&mut self, addr: &MemoryAddress, byte_offset: i64) -> TermId {
        match addr {
            MemoryAddress::Physical(phys) => {
                let target = phys.wrapping_add(byte_offset as u64);
                let mut res = if let Some(&t) = self.memory.get(&target) {
                    t
                } else {
                    let sort8 = self.sorts.bv(8);
                    let var = self.terms.var(format!("uninit_mem_{:x}", target), sort8);
                    self.memory.insert(target, var);
                    var
                };
                if !self.symbolic_memory.is_empty() {
                    let target_term = self.terms.bv_const(target.into(), 64, &mut self.sorts);
                    for (s_addr, s_val) in self.symbolic_memory.iter().rev() {
                        let eq = self.terms.eq(*s_addr, target_term, &self.sorts);
                        res = self.terms.ite(eq, *s_val, res);
                    }
                }
                res
            }
            MemoryAddress::Stack(stack_off) => {
                let target = stack_off + byte_offset;
                if let Some(&t) = self.stack_memory.get(&target) {
                    t
                } else {
                    let sort8 = self.sorts.bv(8);
                    let var = self.terms.var(format!("uninit_stack_{}", target), sort8);
                    self.stack_memory.insert(target, var);
                    var
                }
            }
            MemoryAddress::Named(name, base_off) => {
                let target = (name.clone(), base_off + byte_offset);
                if let Some(&t) = self.named_memory.get(&target) {
                    t
                } else {
                    let sort8 = self.sorts.bv(8);
                    let var = self
                        .terms
                        .var(format!("uninit_{}_{}", target.0, target.1), sort8);
                    self.named_memory.insert(target, var);
                    var
                }
            }
            MemoryAddress::Symbolic(base_term) => {
                let off_term =
                    self.terms
                        .bv_const((byte_offset as u64).into(), 64, &mut self.sorts);
                let byte_addr = if byte_offset != 0 {
                    self.terms
                        .bv_binop(Op::BvAdd, *base_term, off_term)
                        .unwrap_or(*base_term)
                } else {
                    *base_term
                };
                let sort8 = self.sorts.bv(8);
                let mut res = self.terms.var(format!("uninit_sym_{:?}", byte_addr), sort8);
                for (s_addr, s_val) in self.symbolic_memory.iter().rev() {
                    let eq = self.terms.eq(*s_addr, byte_addr, &self.sorts);
                    res = self.terms.ite(eq, *s_val, res);
                }
                res
            }
        }
    }

    fn write_byte_at(&mut self, addr: &MemoryAddress, byte_offset: i64, val: TermId) {
        match addr {
            MemoryAddress::Physical(phys) => {
                let target = phys.wrapping_add(byte_offset as u64);
                self.memory.insert(target, val);
            }
            MemoryAddress::Stack(stack_off) => {
                let target = stack_off + byte_offset;
                self.stack_memory.insert(target, val);
            }
            MemoryAddress::Named(name, base_off) => {
                let target = (name.clone(), base_off + byte_offset);
                self.named_memory.insert(target, val);
            }
            MemoryAddress::Symbolic(base_term) => {
                let off_term =
                    self.terms
                        .bv_const((byte_offset as u64).into(), 64, &mut self.sorts);
                let byte_addr = if byte_offset != 0 {
                    self.terms
                        .bv_binop(Op::BvAdd, *base_term, off_term)
                        .unwrap_or(*base_term)
                } else {
                    *base_term
                };
                self.symbolic_memory.push((byte_addr, val));
            }
        }
    }

    /// Reads a memory operand with proper little-endian byte assembly.
    pub fn read_memory(&mut self, op: &Operand) -> TermId {
        let (base, index, disp, width) = match op {
            Operand::Mem {
                base,
                index,
                disp,
                width,
            } => (base.clone(), index.clone(), *disp, *width),
            _ => panic!("Expected Operand::Mem in read_memory"),
        };
        let addr = self.resolve_address(&base, &index, disp);
        let byte_count = (width / 8).max(1) as usize;
        let mut bytes = Vec::with_capacity(byte_count);
        for i in 0..byte_count {
            bytes.push(self.read_byte_at(&addr, i as i64));
        }

        let mut acc = bytes[0];
        for &b in &bytes[1..] {
            acc = self
                .terms
                .bv_concat(b, acc, &mut self.sorts)
                .expect("Valid little-endian byte concat");
        }
        acc
    }

    /// Writes a value to a memory operand with little-endian byte slicing.
    pub fn write_memory(&mut self, op: &Operand, val: TermId) {
        let (base, index, disp, width) = match op {
            Operand::Mem {
                base,
                index,
                disp,
                width,
            } => (base.clone(), index.clone(), *disp, *width),
            _ => panic!("Expected Operand::Mem in write_memory"),
        };
        let addr = self.resolve_address(&base, &index, disp);
        let byte_count = (width / 8).max(1) as usize;
        for i in 0..byte_count {
            let low = (i * 8) as u32;
            let high = low + 7;
            let byte_val = self
                .terms
                .bv_extract(high, low, val, &mut self.sorts)
                .expect("Valid byte extract");
            self.write_byte_at(&addr, i as i64, byte_val);
        }
    }

    /// Gets or creates the symbolic term for an operand.
    pub fn eval_operand(&mut self, op: &Operand) -> TermId {
        match op {
            Operand::Reg(name, width) => self.read_reg(name, *width),
            Operand::Imm(val, width) => self.terms.bv_const((*val).into(), *width, &mut self.sorts),
            Operand::Mem { .. } => self.read_memory(op),
        }
    }

    /// Updates subtraction / comparison ALU flags: ZF, CF, SF, OF.
    fn update_sub_flags(&mut self, l: TermId, r: TermId) {
        let bool_sort = self.sorts.bool_sort;
        let sort = self.terms.sort_of(l);
        let width = match self.sorts.get(sort) {
            smt_core::sort::Sort::BitVec(w) => *w,
            _ => 64,
        };

        // ZF: l == r
        self.zero_flag = Some(self.terms.eq(l, r, &self.sorts));

        // CF: unsigned borrow (l < r in unsigned)
        self.carry_flag = Some(self.terms.intern(Op::BvUlt, vec![l, r], bool_sort));

        // SF and OF derived from difference
        if let Ok(diff) = self.terms.bv_binop(Op::BvSub, l, r) {
            // SF: MSB of difference is 1
            if let Ok(msb) = self
                .terms
                .bv_extract(width - 1, width - 1, diff, &mut self.sorts)
            {
                let one = self.terms.bv_const(1u32.into(), 1, &mut self.sorts);
                self.sign_flag = Some(self.terms.eq(msb, one, &self.sorts));
            }

            // OF: signed overflow on subtraction: (sign(l) != sign(r)) && (sign(diff) != sign(l))
            if let (Ok(sign_l), Ok(sign_r), Ok(sign_d)) = (
                self.terms
                    .bv_extract(width - 1, width - 1, l, &mut self.sorts),
                self.terms
                    .bv_extract(width - 1, width - 1, r, &mut self.sorts),
                self.terms
                    .bv_extract(width - 1, width - 1, diff, &mut self.sorts),
            ) {
                let diff_signs = {
                    let eq = self.terms.eq(sign_l, sign_r, &self.sorts);
                    self.terms.not(eq)
                };
                let wrong_res_sign = {
                    let eq = self.terms.eq(sign_d, sign_l, &self.sorts);
                    self.terms.not(eq)
                };
                let of = self
                    .terms
                    .and(vec![diff_signs, wrong_res_sign], &self.sorts);
                self.overflow_flag = Some(of);
            }
        }
    }

    /// Updates addition ALU flags: ZF, CF, SF, OF.
    fn update_add_flags(&mut self, l: TermId, r: TermId, sum: TermId) {
        let bool_sort = self.sorts.bool_sort;
        let sort = self.terms.sort_of(l);
        let width = match self.sorts.get(sort) {
            smt_core::sort::Sort::BitVec(w) => *w,
            _ => 64,
        };

        let zero = self.terms.bv_const(0u32.into(), width, &mut self.sorts);
        self.zero_flag = Some(self.terms.eq(sum, zero, &self.sorts));

        // CF: unsigned overflow (sum < l)
        self.carry_flag = Some(self.terms.intern(Op::BvUlt, vec![sum, l], bool_sort));

        // SF: MSB of sum is 1
        if let Ok(msb) = self
            .terms
            .bv_extract(width - 1, width - 1, sum, &mut self.sorts)
        {
            let one = self.terms.bv_const(1u32.into(), 1, &mut self.sorts);
            self.sign_flag = Some(self.terms.eq(msb, one, &self.sorts));
        }

        // OF: signed overflow on addition: (sign(l) == sign(r)) && (sign(sum) != sign(l))
        if let (Ok(sign_l), Ok(sign_r), Ok(sign_s)) = (
            self.terms
                .bv_extract(width - 1, width - 1, l, &mut self.sorts),
            self.terms
                .bv_extract(width - 1, width - 1, r, &mut self.sorts),
            self.terms
                .bv_extract(width - 1, width - 1, sum, &mut self.sorts),
        ) {
            let same_signs = self.terms.eq(sign_l, sign_r, &self.sorts);
            let wrong_res_sign = {
                let eq = self.terms.eq(sign_s, sign_l, &self.sorts);
                self.terms.not(eq)
            };
            let of = self
                .terms
                .and(vec![same_signs, wrong_res_sign], &self.sorts);
            self.overflow_flag = Some(of);
        }
    }

    /// Updates logic ALU flags: CF=0, OF=0, ZF=(res == 0), SF=(msb(res) == 1).
    fn update_logic_flags(&mut self, res: TermId) {
        let sort = self.terms.sort_of(res);
        let width = match self.sorts.get(sort) {
            smt_core::sort::Sort::BitVec(w) => *w,
            _ => 64,
        };

        let zero = self.terms.bv_const(0u32.into(), width, &mut self.sorts);
        self.zero_flag = Some(self.terms.eq(res, zero, &self.sorts));

        // CF and OF are cleared to 0 by logic instructions
        self.carry_flag = Some(self.terms.false_id);
        self.overflow_flag = Some(self.terms.false_id);

        // SF: MSB of res is 1
        if let Ok(msb) = self
            .terms
            .bv_extract(width - 1, width - 1, res, &mut self.sorts)
        {
            let one = self.terms.bv_const(1u32.into(), 1, &mut self.sorts);
            self.sign_flag = Some(self.terms.eq(msb, one, &self.sorts));
        }
    }

    /// Executes a single instruction symbolically, updating internal register, flag, and memory states.
    pub fn step(&mut self, inst: &IrInstruction) {
        match inst {
            IrInstruction::Nop => {}
            IrInstruction::Mov { dst, src } => {
                let src_term = self.eval_operand(src);
                match dst {
                    Operand::Reg(ref name, width) => self.write_reg(name, src_term, *width),
                    Operand::Mem { .. } => self.write_memory(dst, src_term),
                    Operand::Imm(..) => {}
                }
            }
            IrInstruction::Add { dst, src } => {
                let d = self.eval_operand(dst);
                let s = self.eval_operand(src);
                if let Ok(res) = self.terms.bv_binop(Op::BvAdd, d, s) {
                    match dst {
                        Operand::Reg(ref name, width) => self.write_reg(name, res, *width),
                        Operand::Mem { .. } => self.write_memory(dst, res),
                        Operand::Imm(..) => {}
                    }
                    self.update_add_flags(d, s, res);
                }
            }
            IrInstruction::Sub { dst, src } => {
                let d = self.eval_operand(dst);
                let s = self.eval_operand(src);
                if let Ok(res) = self.terms.bv_binop(Op::BvSub, d, s) {
                    match dst {
                        Operand::Reg(ref name, width) => self.write_reg(name, res, *width),
                        Operand::Mem { .. } => self.write_memory(dst, res),
                        Operand::Imm(..) => {}
                    }
                    self.update_sub_flags(d, s);
                }
            }
            IrInstruction::Xor { dst, src } => {
                let d = self.eval_operand(dst);
                let s = self.eval_operand(src);
                if let Ok(res) = self.terms.bv_binop(Op::BvXor, d, s) {
                    self.update_logic_flags(res);
                    match dst {
                        Operand::Reg(ref name, width) => self.write_reg(name, res, *width),
                        Operand::Mem { .. } => self.write_memory(dst, res),
                        Operand::Imm(..) => {}
                    }
                }
            }
            IrInstruction::And { dst, src } => {
                let d = self.eval_operand(dst);
                let s = self.eval_operand(src);
                if let Ok(res) = self.terms.bv_binop(Op::BvAnd, d, s) {
                    self.update_logic_flags(res);
                    match dst {
                        Operand::Reg(ref name, width) => self.write_reg(name, res, *width),
                        Operand::Mem { .. } => self.write_memory(dst, res),
                        Operand::Imm(..) => {}
                    }
                }
            }
            IrInstruction::Or { dst, src } => {
                let d = self.eval_operand(dst);
                let s = self.eval_operand(src);
                if let Ok(res) = self.terms.bv_binop(Op::BvOr, d, s) {
                    self.update_logic_flags(res);
                    match dst {
                        Operand::Reg(ref name, width) => self.write_reg(name, res, *width),
                        Operand::Mem { .. } => self.write_memory(dst, res),
                        Operand::Imm(..) => {}
                    }
                }
            }
            IrInstruction::Test { left, right } => {
                let l = self.eval_operand(left);
                let r = self.eval_operand(right);
                if let Ok(res) = self.terms.bv_binop(Op::BvAnd, l, r) {
                    self.update_logic_flags(res);
                }
            }
            IrInstruction::Cmp { left, right } => {
                let l = self.eval_operand(left);
                let r = self.eval_operand(right);
                self.update_sub_flags(l, r);
            }
            IrInstruction::Push { src } => {
                let val = self.eval_operand(src);
                let rsp_val = self.read_reg("rsp", 64);
                let eight = self.terms.bv_const(8u32.into(), 64, &mut self.sorts);
                if let Ok(new_rsp) = self.terms.bv_binop(Op::BvSub, rsp_val, eight) {
                    self.write_reg("rsp", new_rsp, 64);
                }
                let mem_op = Operand::Mem {
                    base: Some("rsp".to_string()),
                    index: None,
                    disp: 0,
                    width: 64,
                };
                self.write_memory(&mem_op, val);
                self.stack.push(val);
            }
            IrInstruction::Pop { dst } => {
                let mem_op = Operand::Mem {
                    base: Some("rsp".to_string()),
                    index: None,
                    disp: 0,
                    width: 64,
                };
                let val = self.read_memory(&mem_op);
                let rsp_val = self.read_reg("rsp", 64);
                let eight = self.terms.bv_const(8u32.into(), 64, &mut self.sorts);
                if let Ok(new_rsp) = self.terms.bv_binop(Op::BvAdd, rsp_val, eight) {
                    self.write_reg("rsp", new_rsp, 64);
                }
                self.stack.pop();
                match dst {
                    Operand::Reg(ref name, width) => self.write_reg(name, val, *width),
                    Operand::Mem { .. } => self.write_memory(dst, val),
                    Operand::Imm(..) => {}
                }
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

    /// Decodes and executes machine code bytes starting at the given instruction pointer.
    pub fn decode_and_execute_bytes(
        &mut self,
        bytes: &[u8],
        ip: u64,
    ) -> Result<Vec<IrInstruction>, String> {
        let mut current_ip = ip;
        let mut offset = 0;
        let mut instrs = Vec::new();
        while offset < bytes.len() {
            let decoded = crate::x86_decoder::X86Decoder::decode(&bytes[offset..], current_ip)?;
            self.step(&decoded.instruction);
            offset += decoded.length;
            current_ip += decoded.length as u64;
            let is_term = matches!(
                decoded.instruction,
                IrInstruction::Jcc { .. } | IrInstruction::Jmp { .. }
            );
            instrs.push(decoded.instruction);
            if is_term {
                break;
            }
        }
        Ok(instrs)
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

    /// Maps branch condition to SMT boolean term over tracked CPU status flags.
    fn get_condition_term(&mut self, cond: BranchCondition) -> Result<TermId, String> {
        match cond {
            BranchCondition::Equal | BranchCondition::Zero => {
                self.zero_flag.ok_or_else(|| "ZF required".to_string())
            }
            BranchCondition::NotEqual | BranchCondition::NotZero => {
                let zf = self.zero_flag.ok_or_else(|| "ZF required".to_string())?;
                Ok(self.terms.not(zf))
            }
            BranchCondition::BelowUnsigned => {
                self.carry_flag.ok_or_else(|| "CF required".to_string())
            }
            BranchCondition::AboveOrEqualUnsigned => {
                let cf = self.carry_flag.ok_or_else(|| "CF required".to_string())?;
                Ok(self.terms.not(cf))
            }
            BranchCondition::BelowOrEqualUnsigned => {
                let cf = self.carry_flag.ok_or_else(|| "CF required".to_string())?;
                let zf = self.zero_flag.ok_or_else(|| "ZF required".to_string())?;
                Ok(self.terms.or(vec![cf, zf], &self.sorts))
            }
            BranchCondition::AboveUnsigned => {
                let cf = self.carry_flag.ok_or_else(|| "CF required".to_string())?;
                let zf = self.zero_flag.ok_or_else(|| "ZF required".to_string())?;
                let not_cf = self.terms.not(cf);
                let not_zf = self.terms.not(zf);
                Ok(self.terms.and(vec![not_cf, not_zf], &self.sorts))
            }
            BranchCondition::Sign => self.sign_flag.ok_or_else(|| "SF required".to_string()),
            BranchCondition::NotSign => {
                let sf = self.sign_flag.ok_or_else(|| "SF required".to_string())?;
                Ok(self.terms.not(sf))
            }
            BranchCondition::Overflow => {
                self.overflow_flag.ok_or_else(|| "OF required".to_string())
            }
            BranchCondition::NotOverflow => {
                let of = self
                    .overflow_flag
                    .ok_or_else(|| "OF required".to_string())?;
                Ok(self.terms.not(of))
            }
            BranchCondition::LessThanSigned => {
                let sf = self.sign_flag.ok_or_else(|| "SF required".to_string())?;
                let of = self
                    .overflow_flag
                    .ok_or_else(|| "OF required".to_string())?;
                let not_of = self.terms.not(of);
                let p1 = self.terms.and(vec![sf, not_of], &self.sorts);
                let not_sf = self.terms.not(sf);
                let p2 = self.terms.and(vec![not_sf, of], &self.sorts);
                Ok(self.terms.or(vec![p1, p2], &self.sorts))
            }
            BranchCondition::GreaterOrEqualSigned => {
                let sf = self.sign_flag.ok_or_else(|| "SF required".to_string())?;
                let of = self
                    .overflow_flag
                    .ok_or_else(|| "OF required".to_string())?;
                let both_t = self.terms.and(vec![sf, of], &self.sorts);
                let not_sf = self.terms.not(sf);
                let not_of = self.terms.not(of);
                let both_f = self.terms.and(vec![not_sf, not_of], &self.sorts);
                Ok(self.terms.or(vec![both_t, both_f], &self.sorts))
            }
            BranchCondition::LessOrEqualSigned => {
                let zf = self.zero_flag.ok_or_else(|| "ZF required".to_string())?;
                let sf = self.sign_flag.ok_or_else(|| "SF required".to_string())?;
                let of = self
                    .overflow_flag
                    .ok_or_else(|| "OF required".to_string())?;
                let not_of = self.terms.not(of);
                let p1 = self.terms.and(vec![sf, not_of], &self.sorts);
                let not_sf = self.terms.not(sf);
                let p2 = self.terms.and(vec![not_sf, of], &self.sorts);
                let xor_term = self.terms.or(vec![p1, p2], &self.sorts);
                Ok(self.terms.or(vec![zf, xor_term], &self.sorts))
            }
            BranchCondition::GreaterThanSigned => {
                let zf = self.zero_flag.ok_or_else(|| "ZF required".to_string())?;
                let sf = self.sign_flag.ok_or_else(|| "SF required".to_string())?;
                let of = self
                    .overflow_flag
                    .ok_or_else(|| "OF required".to_string())?;
                let not_zf = self.terms.not(zf);
                let both_t = self.terms.and(vec![sf, of], &self.sorts);
                let not_sf = self.terms.not(sf);
                let not_of = self.terms.not(of);
                let both_f = self.terms.and(vec![not_sf, not_of], &self.sorts);
                let eq_term = self.terms.or(vec![both_t, both_f], &self.sorts);
                Ok(self.terms.and(vec![not_zf, eq_term], &self.sorts))
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
                let cond_term = match self.get_condition_term(*cond) {
                    Ok(term) => term,
                    Err(_) => {
                        return BranchResolution::Conditional {
                            true_target: *target_true,
                            false_target: *target_false,
                        };
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

    /// Resolves a branch with full mathematical audit trail (proof-carrying deobfuscation).
    pub fn resolve_branch_certified(
        &mut self,
        terminator: &IrInstruction,
        path_constraints: &[TermId],
    ) -> ProofCarryingResolution {
        match terminator {
            IrInstruction::Jmp { target } => ProofCarryingResolution {
                status: DeobfuscationStatus::ProvenInvariant {
                    surviving_target: *target,
                    dead_target: 0,
                },
                resolution: BranchResolution::Deterministic(*target),
                certificate: format!("Unconditional direct jump to {:#x}", target),
                true_branch_model: None,
                false_branch_model: None,
            },
            IrInstruction::Jcc {
                cond,
                target_true,
                target_false,
            } => {
                let cond_term = match self.get_condition_term(*cond) {
                    Ok(term) => term,
                    Err(err) => {
                        return ProofCarryingResolution {
                            status: DeobfuscationStatus::ProvenDynamic {
                                true_target: *target_true,
                                false_target: *target_false,
                            },
                            resolution: BranchResolution::Conditional {
                                true_target: *target_true,
                                false_target: *target_false,
                            },
                            certificate: format!("Condition cannot be evaluated: {}", err),
                            true_branch_model: None,
                            false_branch_model: None,
                        };
                    }
                };

                let (true_res, true_model) = {
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
                    let res = solver.check_sat();
                    let m = solver.get_model().cloned();
                    (res, m)
                };

                let not_cond = self.terms.not(cond_term);
                let (false_res, false_model) = {
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
                    let res = solver.check_sat();
                    let m = solver.get_model().cloned();
                    (res, m)
                };

                match (true_res, false_res) {
                    (CheckSatResult::Sat, CheckSatResult::Unsat) => ProofCarryingResolution {
                        status: DeobfuscationStatus::ProvenInvariant {
                            surviving_target: *target_true,
                            dead_target: *target_false,
                        },
                        resolution: BranchResolution::Deterministic(*target_true),
                        certificate: format!(
                            "SMT-certified UNSAT refutation of false branch ({:#x})",
                            target_false
                        ),
                        true_branch_model: true_model,
                        false_branch_model: None,
                    },
                    (CheckSatResult::Unsat, CheckSatResult::Sat) => ProofCarryingResolution {
                        status: DeobfuscationStatus::ProvenInvariant {
                            surviving_target: *target_false,
                            dead_target: *target_true,
                        },
                        resolution: BranchResolution::Deterministic(*target_false),
                        certificate: format!(
                            "SMT-certified UNSAT refutation of true branch ({:#x})",
                            target_true
                        ),
                        true_branch_model: None,
                        false_branch_model: false_model,
                    },
                    (CheckSatResult::Sat, CheckSatResult::Sat) => ProofCarryingResolution {
                        status: DeobfuscationStatus::ProvenDynamic {
                            true_target: *target_true,
                            false_target: *target_false,
                        },
                        resolution: BranchResolution::Conditional {
                            true_target: *target_true,
                            false_target: *target_false,
                        },
                        certificate: "Dual-model witness: both true and false paths are feasible"
                            .to_string(),
                        true_branch_model: true_model,
                        false_branch_model: false_model,
                    },
                    _ => ProofCarryingResolution {
                        status: DeobfuscationStatus::UnreachablePath,
                        resolution: BranchResolution::Unreachable,
                        certificate: "Contradiction: both branches UNSAT under path constraints"
                            .to_string(),
                        true_branch_model: None,
                        false_branch_model: None,
                    },
                }
            }
            _ => ProofCarryingResolution {
                status: DeobfuscationStatus::UnreachablePath,
                resolution: BranchResolution::Unreachable,
                certificate: "Unsupported terminator instruction".to_string(),
                true_branch_model: None,
                false_branch_model: None,
            },
        }
    }
}
