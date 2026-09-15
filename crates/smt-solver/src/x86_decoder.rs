//! Standalone x86-64 machine code byte decoder for binary lifting and CFG extraction.
//!
//! Decodes real machine code byte streams (ELF/PE .text sections, Tigress/OLLVM functions)
//! into `IrInstruction` sequences with full ModR/M, REX prefix, and branch target resolution.

use crate::lifter::{BranchCondition, IrInstruction, Operand};

/// Register names for x86-64 at various bit-widths.
pub const REGS_64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

pub const REGS_32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];

pub const REGS_16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];

pub const REGS_8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];

pub const REGS_8_LEGACY: [&str; 8] = ["al", "cl", "dl", "bl", "ah", "ch", "dh", "bh"];

/// Structured, typed error hierarchy for x86-64 machine code decoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecoderError {
    EmptyBuffer,
    TruncatedInstruction(&'static str),
    UnsupportedOpcode { opcode: u8, is_escape_0f: bool },
    UnsupportedGroupOpcode { opcode: u8, group_op: u8 },
    MissingModRm { opcode: u8 },
    InvalidOperandMode { opcode: u8, mode: u8 },
    MalformedInstruction(String),
}

impl std::fmt::Display for DecoderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecoderError::EmptyBuffer => write!(f, "Unexpected EOF: empty instruction buffer"),
            DecoderError::TruncatedInstruction(context) => {
                write!(f, "Truncated instruction: {}", context)
            }
            DecoderError::UnsupportedOpcode {
                opcode,
                is_escape_0f,
            } => {
                if *is_escape_0f {
                    write!(f, "Unsupported 0x0F opcode 0x{:02x}", opcode)
                } else {
                    write!(f, "Unsupported x86-64 opcode 0x{:02x}", opcode)
                }
            }
            DecoderError::UnsupportedGroupOpcode { opcode, group_op } => {
                write!(f, "Unsupported 0x{:02x} /{} op", opcode, group_op)
            }
            DecoderError::MissingModRm { opcode } => {
                write!(f, "Missing ModR/M byte for 0x{:02x}", opcode)
            }
            DecoderError::InvalidOperandMode { opcode, mode } => {
                write!(f, "Unsupported operand mode {} for 0x{:02x}", mode, opcode)
            }
            DecoderError::MalformedInstruction(msg) => write!(f, "Malformed instruction: {}", msg),
        }
    }
}

impl std::error::Error for DecoderError {}

/// Result of decoding a single machine code instruction.
#[derive(Debug, Clone)]
pub struct DecodedInstruction {
    pub instruction: IrInstruction,
    pub length: usize,
}

struct ModRmContext<'a> {
    bytes: &'a [u8],
    mode: u8,
    rm_raw: u8,
    rex_x: usize,
    rex_b: usize,
    width: u32,
    has_rex: bool,
    imm_len: usize,
    inst_start_ip: u64,
}

/// Standalone x86-64 machine code decoder.
pub struct X86Decoder;

impl X86Decoder {
    /// Decodes a single instruction starting at `bytes[0]` with instruction pointer `ip`.
    ///
    /// # Example
    /// ```rust
    /// use smt_solver::x86_decoder::X86Decoder;
    /// let bytes = [0x31, 0xc0]; // xor eax, eax
    /// let insn = X86Decoder::decode(&bytes, 0x401000).unwrap();
    /// assert_eq!(insn.length, 2);
    /// ```
    pub fn decode(bytes: &[u8], ip: u64) -> Result<DecodedInstruction, DecoderError> {
        if bytes.is_empty() {
            return Err(DecoderError::EmptyBuffer);
        }

        let mut offset = 0;
        let mut rex_w = false;
        let mut rex_r = 0usize;
        let mut rex_x = 0usize;
        let mut rex_b = 0usize;
        let mut has_rex = false;

        // Check for REX prefix (0x40 - 0x4F) in 64-bit mode
        if bytes[offset] >= 0x40 && bytes[offset] <= 0x4f {
            let rex = bytes[offset];
            rex_w = (rex & 0x08) != 0;
            rex_r = if (rex & 0x04) != 0 { 8 } else { 0 };
            rex_x = if (rex & 0x02) != 0 { 8 } else { 0 };
            rex_b = if (rex & 0x01) != 0 { 8 } else { 0 };
            has_rex = true;
            offset += 1;
            if offset >= bytes.len() {
                return Err(DecoderError::TruncatedInstruction("after REX prefix"));
            }
        }

        let width = if rex_w { 64 } else { 32 };
        let get_reg = |idx: usize, w: u32| -> Operand {
            match w {
                64 => Operand::Reg(REGS_64[idx % 16].to_string(), 64),
                32 => Operand::Reg(REGS_32[idx % 16].to_string(), 32),
                16 => Operand::Reg(REGS_16[idx % 16].to_string(), 16),
                8 => {
                    if has_rex {
                        Operand::Reg(REGS_8[idx % 16].to_string(), 8)
                    } else if idx < 8 {
                        Operand::Reg(REGS_8_LEGACY[idx].to_string(), 8)
                    } else {
                        Operand::Reg(REGS_8[idx % 16].to_string(), 8)
                    }
                }
                _ => Operand::Reg(REGS_32[idx % 16].to_string(), 32),
            }
        };

        let opcode = bytes[offset];
        offset += 1;

        match opcode {
            // RET
            0xc3 => Ok(DecodedInstruction {
                instruction: IrInstruction::Jmp { target: 0 },
                length: offset,
            }),

            // NOP (0x90)
            0x90 => Ok(DecodedInstruction {
                instruction: IrInstruction::Nop,
                length: offset,
            }),

            // PUSH r64 (0x50 - 0x57)
            0x50..=0x57 => {
                let reg_idx = (opcode - 0x50) as usize + rex_b;
                let reg = get_reg(reg_idx, 64);
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Push { src: reg },
                    length: offset,
                })
            }

            // POP r64 (0x58 - 0x5F)
            0x58..=0x5f => {
                let reg_idx = (opcode - 0x58) as usize + rex_b;
                let reg = get_reg(reg_idx, 64);
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Pop { dst: reg },
                    length: offset,
                })
            }

            // MOV r32/r64, imm32/imm64 (0xB8..0xBF)
            0xb8..=0xbf => {
                let reg_idx = (opcode - 0xb8) as usize + rex_b;
                let imm = if width == 64 {
                    if offset + 8 > bytes.len() {
                        return Err(DecoderError::TruncatedInstruction("MOV imm64"));
                    }
                    let val = u64::from_le_bytes([
                        bytes[offset],
                        bytes[offset + 1],
                        bytes[offset + 2],
                        bytes[offset + 3],
                        bytes[offset + 4],
                        bytes[offset + 5],
                        bytes[offset + 6],
                        bytes[offset + 7],
                    ]);
                    offset += 8;
                    val
                } else {
                    if offset + 4 > bytes.len() {
                        return Err(DecoderError::TruncatedInstruction("MOV imm32"));
                    }
                    let val = u32::from_le_bytes([
                        bytes[offset],
                        bytes[offset + 1],
                        bytes[offset + 2],
                        bytes[offset + 3],
                    ]) as u64;
                    offset += 4;
                    val
                };

                Ok(DecodedInstruction {
                    instruction: IrInstruction::Mov {
                        dst: get_reg(reg_idx, width),
                        src: Operand::Imm(imm, width),
                    },
                    length: offset,
                })
            }

            // JMP rel8 (0xEB)
            0xeb => {
                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("JMP rel8"));
                }
                let rel8 = bytes[offset] as i8 as i64;
                offset += 1;
                let target = (ip as i64 + offset as i64 + rel8) as u64;
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Jmp { target },
                    length: offset,
                })
            }

            // JMP rel32 (0xE9)
            0xe9 => {
                if offset + 4 > bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("JMP rel32"));
                }
                let rel32 = i32::from_le_bytes([
                    bytes[offset],
                    bytes[offset + 1],
                    bytes[offset + 2],
                    bytes[offset + 3],
                ]) as i64;
                offset += 4;
                let target = (ip as i64 + offset as i64 + rel32) as u64;
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Jmp { target },
                    length: offset,
                })
            }

            // Jcc rel8 (0x70 - 0x7F)
            0x70..=0x7f => {
                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("Jcc rel8"));
                }
                let rel8 = bytes[offset] as i8 as i64;
                offset += 1;
                let target_true = (ip as i64 + offset as i64 + rel8) as u64;
                let target_false = ip + offset as u64;

                let cond = match opcode & 0x0f {
                    0x00 => BranchCondition::Overflow,
                    0x01 => BranchCondition::NotOverflow,
                    0x02 => BranchCondition::BelowUnsigned,
                    0x03 => BranchCondition::AboveOrEqualUnsigned,
                    0x04 => BranchCondition::Equal,
                    0x05 => BranchCondition::NotEqual,
                    0x06 => BranchCondition::BelowOrEqualUnsigned,
                    0x07 => BranchCondition::AboveUnsigned,
                    0x08 => BranchCondition::Sign,
                    0x09 => BranchCondition::NotSign,
                    0x0c => BranchCondition::LessThanSigned,
                    0x0d => BranchCondition::GreaterOrEqualSigned,
                    0x0e => BranchCondition::LessOrEqualSigned,
                    0x0f => BranchCondition::GreaterThanSigned,
                    _ => BranchCondition::Equal,
                };

                Ok(DecodedInstruction {
                    instruction: IrInstruction::Jcc {
                        cond,
                        target_true,
                        target_false,
                    },
                    length: offset,
                })
            }

            // 2-byte escape (0x0F)
            0x0f => {
                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("0x0F escape"));
                }
                let op2 = bytes[offset];
                offset += 1;
                match op2 {
                    // Jcc rel32 (0x0F 0x80..0x8F)
                    0x80..=0x8f => {
                        if offset + 4 > bytes.len() {
                            return Err(DecoderError::TruncatedInstruction("Jcc rel32"));
                        }
                        let rel32 = i32::from_le_bytes([
                            bytes[offset],
                            bytes[offset + 1],
                            bytes[offset + 2],
                            bytes[offset + 3],
                        ]) as i64;
                        offset += 4;
                        let target_true = (ip as i64 + offset as i64 + rel32) as u64;
                        let target_false = ip + offset as u64;

                        let cond = match op2 & 0x0f {
                            0x00 => BranchCondition::Overflow,
                            0x01 => BranchCondition::NotOverflow,
                            0x02 => BranchCondition::BelowUnsigned,
                            0x03 => BranchCondition::AboveOrEqualUnsigned,
                            0x04 => BranchCondition::Equal,
                            0x05 => BranchCondition::NotEqual,
                            0x06 => BranchCondition::BelowOrEqualUnsigned,
                            0x07 => BranchCondition::AboveUnsigned,
                            0x08 => BranchCondition::Sign,
                            0x09 => BranchCondition::NotSign,
                            0x0c => BranchCondition::LessThanSigned,
                            0x0d => BranchCondition::GreaterOrEqualSigned,
                            0x0e => BranchCondition::LessOrEqualSigned,
                            0x0f => BranchCondition::GreaterThanSigned,
                            _ => BranchCondition::Equal,
                        };

                        Ok(DecodedInstruction {
                            instruction: IrInstruction::Jcc {
                                cond,
                                target_true,
                                target_false,
                            },
                            length: offset,
                        })
                    }
                    _ => Err(DecoderError::UnsupportedOpcode {
                        opcode: op2,
                        is_escape_0f: true,
                    }),
                }
            }

            // Arithmetic and Logic with ModR/M
            0x01 | 0x03 | 0x09 | 0x0b | 0x21 | 0x23 | 0x29 | 0x2b | 0x31 | 0x33 | 0x39 | 0x3b
            | 0x85 | 0x89 | 0x8b => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode });
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let reg_field = ((modrm >> 3) & 7) as usize + rex_r;
                let rm_raw = modrm & 7;

                let r_reg = get_reg(reg_field, width);
                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width,
                    has_rex,
                    imm_len: 0,
                    inst_start_ip: ip,
                };
                let rm_op = Self::decode_rm(&ctx, &mut offset)?;

                let inst = match opcode {
                    0x01 => IrInstruction::Add {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x03 => IrInstruction::Add {
                        dst: r_reg,
                        src: rm_op,
                    },
                    0x09 => IrInstruction::Or {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x0b => IrInstruction::Or {
                        dst: r_reg,
                        src: rm_op,
                    },
                    0x21 => IrInstruction::And {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x23 => IrInstruction::And {
                        dst: r_reg,
                        src: rm_op,
                    },
                    0x29 => IrInstruction::Sub {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x2b => IrInstruction::Sub {
                        dst: r_reg,
                        src: rm_op,
                    },
                    0x31 => IrInstruction::Xor {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x33 => IrInstruction::Xor {
                        dst: r_reg,
                        src: rm_op,
                    },
                    0x39 => IrInstruction::Cmp {
                        left: rm_op,
                        right: r_reg,
                    },
                    0x3b => IrInstruction::Cmp {
                        left: r_reg,
                        right: rm_op,
                    },
                    0x85 => IrInstruction::Test {
                        left: rm_op,
                        right: r_reg,
                    },
                    0x89 => IrInstruction::Mov {
                        dst: rm_op,
                        src: r_reg,
                    },
                    0x8b => IrInstruction::Mov {
                        dst: r_reg,
                        src: rm_op,
                    },
                    _ => unreachable!(),
                };

                Ok(DecodedInstruction {
                    instruction: inst,
                    length: offset,
                })
            }

            // Group 1 immediate arithmetic (0x83 /reg rm, imm8)
            0x83 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0x83 });
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_raw = modrm & 7;

                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width,
                    has_rex,
                    imm_len: 1,
                    inst_start_ip: ip,
                };
                let target = Self::decode_rm(&ctx, &mut offset)?;

                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm8 byte for 0x83"));
                }
                let imm8 = bytes[offset] as i8 as i64 as u64;
                offset += 1;
                let imm_op = Operand::Imm(imm8, width);

                let inst = match op_reg {
                    0 => IrInstruction::Add {
                        dst: target,
                        src: imm_op,
                    },
                    1 => IrInstruction::Or {
                        dst: target,
                        src: imm_op,
                    },
                    4 => IrInstruction::And {
                        dst: target,
                        src: imm_op,
                    },
                    5 => IrInstruction::Sub {
                        dst: target,
                        src: imm_op,
                    },
                    6 => IrInstruction::Xor {
                        dst: target,
                        src: imm_op,
                    },
                    7 => IrInstruction::Cmp {
                        left: target,
                        right: imm_op,
                    },
                    _ => {
                        return Err(DecoderError::UnsupportedGroupOpcode {
                            opcode: 0x83,
                            group_op: op_reg,
                        })
                    }
                };

                Ok(DecodedInstruction {
                    instruction: inst,
                    length: offset,
                })
            }

            // Group 1 immediate arithmetic (0x81 /reg rm, imm32)
            0x81 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0x81 });
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_raw = modrm & 7;

                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width,
                    has_rex,
                    imm_len: 4,
                    inst_start_ip: ip,
                };
                let target = Self::decode_rm(&ctx, &mut offset)?;

                if offset + 4 > bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm32 for 0x81"));
                }
                let imm32 = i32::from_le_bytes([
                    bytes[offset],
                    bytes[offset + 1],
                    bytes[offset + 2],
                    bytes[offset + 3],
                ]) as i64 as u64;
                offset += 4;
                let imm_op = Operand::Imm(imm32, width);

                let inst = match op_reg {
                    0 => IrInstruction::Add {
                        dst: target,
                        src: imm_op,
                    },
                    1 => IrInstruction::Or {
                        dst: target,
                        src: imm_op,
                    },
                    4 => IrInstruction::And {
                        dst: target,
                        src: imm_op,
                    },
                    5 => IrInstruction::Sub {
                        dst: target,
                        src: imm_op,
                    },
                    6 => IrInstruction::Xor {
                        dst: target,
                        src: imm_op,
                    },
                    7 => IrInstruction::Cmp {
                        left: target,
                        right: imm_op,
                    },
                    _ => {
                        return Err(DecoderError::UnsupportedGroupOpcode {
                            opcode: 0x81,
                            group_op: op_reg,
                        })
                    }
                };

                Ok(DecodedInstruction {
                    instruction: inst,
                    length: offset,
                })
            }

            // MOV r/m, imm32 (0xC7 /0)
            0xc7 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0xC7 });
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_raw = modrm & 7;

                if op_reg != 0 {
                    return Err(DecoderError::UnsupportedGroupOpcode {
                        opcode: 0xC7,
                        group_op: op_reg,
                    });
                }

                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width,
                    has_rex,
                    imm_len: 4,
                    inst_start_ip: ip,
                };
                let target = Self::decode_rm(&ctx, &mut offset)?;

                if offset + 4 > bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm32 for 0xC7"));
                }
                let imm32 = if width == 64 {
                    i32::from_le_bytes([
                        bytes[offset],
                        bytes[offset + 1],
                        bytes[offset + 2],
                        bytes[offset + 3],
                    ]) as i64 as u64
                } else {
                    u32::from_le_bytes([
                        bytes[offset],
                        bytes[offset + 1],
                        bytes[offset + 2],
                        bytes[offset + 3],
                    ]) as u64
                };
                offset += 4;

                Ok(DecodedInstruction {
                    instruction: IrInstruction::Mov {
                        dst: target,
                        src: Operand::Imm(imm32, width),
                    },
                    length: offset,
                })
            }

            // TEST r/m8, reg8 (0x84)
            0x84 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0x84 });
                }
                let modrm = bytes[offset];
                offset += 1;
                let mode = (modrm >> 6) & 3;
                let reg_field = ((modrm >> 3) & 7) as usize + rex_r;
                let rm_raw = modrm & 7;
                let r_reg = get_reg(reg_field, 8);
                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width: 8,
                    has_rex,
                    imm_len: 0,
                    inst_start_ip: ip,
                };
                let rm_op = Self::decode_rm(&ctx, &mut offset)?;
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Test {
                        left: rm_op,
                        right: r_reg,
                    },
                    length: offset,
                })
            }

            // TEST AL, imm8 (0xA8)
            0xa8 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm8 for 0xA8"));
                }
                let imm8 = bytes[offset] as u64;
                offset += 1;
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Test {
                        left: Operand::Reg("al".to_string(), 8),
                        right: Operand::Imm(imm8, 8),
                    },
                    length: offset,
                })
            }

            // TEST AX/EAX/RAX, imm16/32 (0xA9)
            0xa9 => {
                let imm_len = if width == 16 { 2 } else { 4 };
                if offset + imm_len > bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm for 0xA9"));
                }
                let imm = if imm_len == 2 {
                    u16::from_le_bytes([bytes[offset], bytes[offset + 1]]) as u64
                } else {
                    u32::from_le_bytes([
                        bytes[offset],
                        bytes[offset + 1],
                        bytes[offset + 2],
                        bytes[offset + 3],
                    ]) as u64
                };
                offset += imm_len;
                let reg = get_reg(0, width);
                Ok(DecodedInstruction {
                    instruction: IrInstruction::Test {
                        left: reg,
                        right: Operand::Imm(imm, width),
                    },
                    length: offset,
                })
            }

            // Group 3 TEST r/m8, imm8 (0xF6 /0)
            0xf6 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0xF6 });
                }
                let modrm = bytes[offset];
                offset += 1;
                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_raw = modrm & 7;

                if op_reg != 0 {
                    return Err(DecoderError::UnsupportedGroupOpcode {
                        opcode: 0xF6,
                        group_op: op_reg,
                    });
                }

                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width: 8,
                    has_rex,
                    imm_len: 1,
                    inst_start_ip: ip,
                };
                let rm_op = Self::decode_rm(&ctx, &mut offset)?;

                if offset >= bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm8 for 0xF6 /0"));
                }
                let imm8 = bytes[offset] as u64;
                offset += 1;

                Ok(DecodedInstruction {
                    instruction: IrInstruction::Test {
                        left: rm_op,
                        right: Operand::Imm(imm8, 8),
                    },
                    length: offset,
                })
            }

            // Group 3 TEST r/m, imm32 (0xF7 /0)
            0xf7 => {
                if offset >= bytes.len() {
                    return Err(DecoderError::MissingModRm { opcode: 0xF7 });
                }
                let modrm = bytes[offset];
                offset += 1;
                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_raw = modrm & 7;

                if op_reg != 0 {
                    return Err(DecoderError::UnsupportedGroupOpcode {
                        opcode: 0xF7,
                        group_op: op_reg,
                    });
                }

                let ctx = ModRmContext {
                    bytes,
                    mode,
                    rm_raw,
                    rex_x,
                    rex_b,
                    width,
                    has_rex,
                    imm_len: 4,
                    inst_start_ip: ip,
                };
                let rm_op = Self::decode_rm(&ctx, &mut offset)?;

                if offset + 4 > bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("imm32 for 0xF7 /0"));
                }
                let imm32 = u32::from_le_bytes([
                    bytes[offset],
                    bytes[offset + 1],
                    bytes[offset + 2],
                    bytes[offset + 3],
                ]) as u64;
                offset += 4;

                Ok(DecodedInstruction {
                    instruction: IrInstruction::Test {
                        left: rm_op,
                        right: Operand::Imm(imm32, width),
                    },
                    length: offset,
                })
            }

            _ => Err(DecoderError::UnsupportedOpcode {
                opcode,
                is_escape_0f: false,
            }),
        }
    }

    fn decode_rm(ctx: &ModRmContext<'_>, offset: &mut usize) -> Result<Operand, DecoderError> {
        let get_reg = |idx: usize, w: u32| -> Operand {
            match w {
                64 => Operand::Reg(REGS_64[idx % 16].to_string(), 64),
                32 => Operand::Reg(REGS_32[idx % 16].to_string(), 32),
                16 => Operand::Reg(REGS_16[idx % 16].to_string(), 16),
                8 => {
                    if ctx.has_rex {
                        Operand::Reg(REGS_8[idx % 16].to_string(), 8)
                    } else if idx < 8 {
                        Operand::Reg(REGS_8_LEGACY[idx].to_string(), 8)
                    } else {
                        Operand::Reg(REGS_8[idx % 16].to_string(), 8)
                    }
                }
                _ => Operand::Reg(REGS_32[idx % 16].to_string(), 32),
            }
        };

        if ctx.mode == 3 {
            let reg_idx = (ctx.rm_raw as usize) + ctx.rex_b;
            return Ok(get_reg(reg_idx, ctx.width));
        }

        let mut base_reg: Option<String> = None;
        let mut index_reg: Option<(String, u8)> = None;
        let mut disp: i64 = 0;

        if (ctx.rm_raw & 7) == 4 {
            if *offset >= ctx.bytes.len() {
                return Err(DecoderError::TruncatedInstruction("SIB byte"));
            }
            let sib = ctx.bytes[*offset];
            *offset += 1;

            let scale = 1u8 << ((sib >> 6) & 3);
            let index_idx = (((sib >> 3) & 7) as usize) + ctx.rex_x;
            let base_idx = ((sib & 7) as usize) + ctx.rex_b;

            if index_idx != 4 {
                index_reg = Some((REGS_64[index_idx % 16].to_string(), scale));
            }

            if (sib & 7) == 5 && ctx.mode == 0 {
                if *offset + 4 > ctx.bytes.len() {
                    return Err(DecoderError::TruncatedInstruction("disp32 in SIB"));
                }
                disp = i32::from_le_bytes([
                    ctx.bytes[*offset],
                    ctx.bytes[*offset + 1],
                    ctx.bytes[*offset + 2],
                    ctx.bytes[*offset + 3],
                ]) as i64;
                *offset += 4;
            } else {
                base_reg = Some(REGS_64[base_idx % 16].to_string());
            }
        } else if ctx.mode == 0 && (ctx.rm_raw & 7) == 5 {
            if *offset + 4 > ctx.bytes.len() {
                return Err(DecoderError::TruncatedInstruction("RIP-relative disp32"));
            }
            let rel32 = i32::from_le_bytes([
                ctx.bytes[*offset],
                ctx.bytes[*offset + 1],
                ctx.bytes[*offset + 2],
                ctx.bytes[*offset + 3],
            ]) as i64;
            *offset += 4;
            let next_ip = ctx.inst_start_ip + (*offset + ctx.imm_len) as u64;
            let target = (next_ip as i64 + rel32) as u64;
            return Ok(Operand::Mem {
                base: None,
                index: None,
                disp: target as i64,
                width: ctx.width,
            });
        } else {
            let base_idx = (ctx.rm_raw as usize) + ctx.rex_b;
            base_reg = Some(REGS_64[base_idx % 16].to_string());
        }

        if ctx.mode == 1 {
            if *offset >= ctx.bytes.len() {
                return Err(DecoderError::TruncatedInstruction("disp8"));
            }
            disp = ctx.bytes[*offset] as i8 as i64;
            *offset += 1;
        } else if ctx.mode == 2 {
            if *offset + 4 > ctx.bytes.len() {
                return Err(DecoderError::TruncatedInstruction("disp32"));
            }
            disp = i32::from_le_bytes([
                ctx.bytes[*offset],
                ctx.bytes[*offset + 1],
                ctx.bytes[*offset + 2],
                ctx.bytes[*offset + 3],
            ]) as i64;
            *offset += 4;
        }

        Ok(Operand::Mem {
            base: base_reg,
            index: index_reg,
            disp,
            width: ctx.width,
        })
    }

    /// Decodes a contiguous sequence of machine code bytes into a BasicBlock until a terminator is met.
    pub fn decode_block(
        bytes: &[u8],
        base_ip: u64,
    ) -> Result<crate::lifter::BasicBlock, DecoderError> {
        let mut bb = crate::lifter::BasicBlock::new(base_ip);
        let mut curr_offset = 0;

        while curr_offset < bytes.len() {
            let curr_ip = base_ip + curr_offset as u64;
            let decoded = Self::decode(&bytes[curr_offset..], curr_ip)?;
            curr_offset += decoded.length;

            let is_term = matches!(
                decoded.instruction,
                IrInstruction::Jcc { .. } | IrInstruction::Jmp { .. }
            );
            bb.push(decoded.instruction);
            if is_term {
                break;
            }
        }

        Ok(bb)
    }
}
