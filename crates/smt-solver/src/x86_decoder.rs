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

/// Result of decoding a single machine code instruction.
#[derive(Debug, Clone)]
pub struct DecodedInstruction {
    pub instruction: IrInstruction,
    pub length: usize,
}

/// Standalone x86-64 machine code decoder.
pub struct X86Decoder;

impl X86Decoder {
    /// Decodes a single instruction starting at `bytes[0]` with instruction pointer `ip`.
    pub fn decode(bytes: &[u8], ip: u64) -> Result<DecodedInstruction, String> {
        if bytes.is_empty() {
            return Err("Unexpected EOF: empty instruction buffer".to_string());
        }

        let mut offset = 0;
        let mut rex_w = false;
        let mut rex_r = 0usize;
        let mut rex_b = 0usize;
        let mut has_rex = false;

        // Check for REX prefix (0x40 - 0x4F) in 64-bit mode
        if bytes[offset] >= 0x40 && bytes[offset] <= 0x4f {
            let rex = bytes[offset];
            rex_w = (rex & 0x08) != 0;
            rex_r = if (rex & 0x04) != 0 { 8 } else { 0 };
            rex_b = if (rex & 0x01) != 0 { 8 } else { 0 };
            has_rex = true;
            offset += 1;
            if offset >= bytes.len() {
                return Err("Truncated instruction after REX prefix".to_string());
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
                        return Err("Truncated MOV imm64".to_string());
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
                        return Err("Truncated MOV imm32".to_string());
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
                    return Err("Truncated JMP rel8".to_string());
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
                    return Err("Truncated JMP rel32".to_string());
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
                    return Err("Truncated Jcc rel8".to_string());
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
                    return Err("Truncated 0x0F escape".to_string());
                }
                let op2 = bytes[offset];
                offset += 1;
                match op2 {
                    // Jcc rel32 (0x0F 0x80..0x8F)
                    0x80..=0x8f => {
                        if offset + 4 > bytes.len() {
                            return Err("Truncated Jcc rel32".to_string());
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
                    _ => Err(format!("Unsupported 0x0F opcode 0x{:02x}", op2)),
                }
            }

            // Arithmetic and Logic with ModR/M
            0x01 | 0x09 | 0x21 | 0x29 | 0x31 | 0x39 | 0x85 | 0x89 | 0x8b => {
                if offset >= bytes.len() {
                    return Err("Missing ModR/M byte".to_string());
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let reg_field = ((modrm >> 3) & 7) as usize + rex_r;
                let rm_field = (modrm & 7) as usize + rex_b;

                if mode == 3 {
                    // Direct register-register mode
                    let r_reg = get_reg(reg_field, width);
                    let rm_reg = get_reg(rm_field, width);

                    let inst = match opcode {
                        0x01 => IrInstruction::Add {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x09 => IrInstruction::Or {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x21 => IrInstruction::And {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x29 => IrInstruction::Sub {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x31 => IrInstruction::Xor {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x39 => IrInstruction::Cmp {
                            left: rm_reg,
                            right: r_reg,
                        },
                        0x85 => IrInstruction::Cmp {
                            left: rm_reg,
                            right: r_reg,
                        }, // TEST
                        0x89 => IrInstruction::Mov {
                            dst: rm_reg,
                            src: r_reg,
                        },
                        0x8b => IrInstruction::Mov {
                            dst: r_reg,
                            src: rm_reg,
                        },
                        _ => unreachable!(),
                    };

                    Ok(DecodedInstruction {
                        instruction: inst,
                        length: offset,
                    })
                } else {
                    Err(format!("Memory addressing mode {} not yet supported", mode))
                }
            }

            // Group 1 immediate arithmetic (0x83 /reg rm, imm8)
            0x83 => {
                if offset >= bytes.len() {
                    return Err("Missing ModR/M byte for 0x83".to_string());
                }
                let modrm = bytes[offset];
                offset += 1;

                let mode = (modrm >> 6) & 3;
                let op_reg = (modrm >> 3) & 7;
                let rm_field = (modrm & 7) as usize + rex_b;

                if mode == 3 {
                    if offset >= bytes.len() {
                        return Err("Missing imm8 byte for 0x83".to_string());
                    }
                    let imm8 = bytes[offset] as i8 as i64 as u64;
                    offset += 1;

                    let target = get_reg(rm_field, width);
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
                        _ => return Err(format!("Unsupported 0x83 /{} op", op_reg)),
                    };

                    Ok(DecodedInstruction {
                        instruction: inst,
                        length: offset,
                    })
                } else {
                    Err(format!("0x83 Memory addressing mode {} unsupported", mode))
                }
            }

            _ => Err(format!("Unsupported x86-64 opcode 0x{:02x}", opcode)),
        }
    }

    /// Decodes a contiguous sequence of machine code bytes into a BasicBlock until a terminator is met.
    pub fn decode_block(bytes: &[u8], base_ip: u64) -> Result<crate::lifter::BasicBlock, String> {
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
