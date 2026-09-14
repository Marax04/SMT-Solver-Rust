//! Independent differential oracle tests comparing `X86Decoder` with `iced-x86`.
//!
//! Validates length, mnemonic classification, register operands, memory addressing,
//! and branch target computation against an industrial-grade disassembly oracle.

use iced_x86::{Decoder, DecoderOptions};
use smt_solver::lifter::{BranchCondition, IrInstruction, Operand};
use smt_solver::x86_decoder::X86Decoder;

fn check_instruction(bytes: &[u8], ip: u64, expected_ir_mnemonic: fn(&IrInstruction) -> bool) {
    // 1. Decode with internal X86Decoder
    let custom_res = X86Decoder::decode(bytes, ip);
    assert!(
        custom_res.is_ok(),
        "X86Decoder failed on bytes {:02x?}: {:?}",
        bytes,
        custom_res.err()
    );
    let custom = custom_res.unwrap();

    // 2. Decode with iced-x86 oracle
    let mut oracle_decoder = Decoder::with_ip(64, bytes, ip, DecoderOptions::NONE);
    assert!(
        oracle_decoder.can_decode(),
        "iced-x86 cannot decode bytes: {:02x?}",
        bytes
    );
    let oracle = oracle_decoder.decode();

    // 3. Differential assertions
    assert_eq!(
        custom.length,
        oracle.len(),
        "Length mismatch for bytes {:02x?}: custom={}, oracle={}",
        bytes,
        custom.length,
        oracle.len()
    );

    assert!(
        expected_ir_mnemonic(&custom.instruction),
        "Custom instruction does not match expected IR type: {:?}",
        custom.instruction
    );

    // 4. Branch target validation if applicable
    if let IrInstruction::Jcc { target_true, .. } = custom.instruction {
        assert_eq!(
            target_true,
            oracle.near_branch_target(),
            "Branch target mismatch for bytes {:02x?}: custom=0x{:x}, oracle=0x{:x}",
            bytes,
            target_true,
            oracle.near_branch_target()
        );
    } else if let IrInstruction::Jmp { target } = custom.instruction {
        if target != 0 {
            // Non-RET jump
            assert_eq!(
                target,
                oracle.near_branch_target(),
                "Jump target mismatch for bytes {:02x?}: custom=0x{:x}, oracle=0x{:x}",
                bytes,
                target,
                oracle.near_branch_target()
            );
        }
    }
}

#[test]
fn test_oracle_nop_and_ret() {
    check_instruction(&[0x90], 0x1000, |i| matches!(i, IrInstruction::Nop));
    check_instruction(&[0xc3], 0x1000, |i| {
        matches!(i, IrInstruction::Jmp { target: 0 })
    });
}

#[test]
fn test_oracle_push_pop_all_gp_registers() {
    // PUSH/POP rax..rdi (0x50..0x5F)
    for reg_idx in 0..8 {
        let push_byte = 0x50 + reg_idx;
        let pop_byte = 0x58 + reg_idx;
        check_instruction(&[push_byte], 0x1000, |i| {
            matches!(i, IrInstruction::Push { .. })
        });
        check_instruction(&[pop_byte], 0x1000, |i| {
            matches!(i, IrInstruction::Pop { .. })
        });
    }

    // PUSH/POP r8..r15 (REX.B + 0x50..0x5F)
    for reg_idx in 0..8 {
        let push_bytes = [0x41, 0x50 + reg_idx];
        let pop_bytes = [0x41, 0x58 + reg_idx];
        check_instruction(&push_bytes, 0x1000, |i| {
            matches!(i, IrInstruction::Push { .. })
        });
        check_instruction(&pop_bytes, 0x1000, |i| {
            matches!(i, IrInstruction::Pop { .. })
        });
    }
}

#[test]
fn test_oracle_mov_immediate() {
    // mov eax, 0x12345678 (b8 78 56 34 12)
    check_instruction(
        &[0xb8, 0x78, 0x56, 0x34, 0x12],
        0x1000,
        |i| matches!(i, IrInstruction::Mov { dst: Operand::Reg(r, 32), src: Operand::Imm(0x12345678, 32) } if r == "eax"),
    );

    // movabs rax, 0x1122334455667788 (48 b8 88 77 66 55 44 33 22 11)
    check_instruction(
        &[0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
        0x1000,
        |i| matches!(i, IrInstruction::Mov { dst: Operand::Reg(r, 64), src: Operand::Imm(0x1122334455667788, 64) } if r == "rax"),
    );
}

#[test]
fn test_oracle_alu_reg_reg() {
    // add eax, ebx (01 d8)
    check_instruction(&[0x01, 0xd8], 0x1000, |i| {
        matches!(i, IrInstruction::Add { .. })
    });
    // add rax, rbx (48 01 d8)
    check_instruction(&[0x48, 0x01, 0xd8], 0x1000, |i| {
        matches!(i, IrInstruction::Add { .. })
    });
    // sub rax, rbx (48 29 d8)
    check_instruction(&[0x48, 0x29, 0xd8], 0x1000, |i| {
        matches!(i, IrInstruction::Sub { .. })
    });
    // xor r8d, r9d (45 31 c8)
    check_instruction(&[0x45, 0x31, 0xc8], 0x1000, |i| {
        matches!(i, IrInstruction::Xor { .. })
    });
    // and r14, r15 (4d 21 fe)
    check_instruction(&[0x4d, 0x21, 0xfe], 0x1000, |i| {
        matches!(i, IrInstruction::And { .. })
    });
    // or rsi, rdi (48 09 fe)
    check_instruction(&[0x48, 0x09, 0xfe], 0x1000, |i| {
        matches!(i, IrInstruction::Or { .. })
    });
    // cmp edx, ecx (39 ca)
    check_instruction(&[0x39, 0xca], 0x1000, |i| {
        matches!(i, IrInstruction::Cmp { .. })
    });
    // test edx, ecx (85 ca)
    check_instruction(&[0x85, 0xca], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
    // test dl, cl (84 ca)
    check_instruction(&[0x84, 0xca], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
    // test al, 0x0f (a8 0f)
    check_instruction(&[0xa8, 0x0f], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
    // test eax, 0x12345678 (a9 78 56 34 12)
    check_instruction(&[0xa9, 0x78, 0x56, 0x34, 0x12], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
    // test cl, 1 (f6 c1 01)
    check_instruction(&[0xf6, 0xc1, 0x01], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
    // test eax, 0x12345678 (f7 c0 78 56 34 12)
    check_instruction(&[0xf7, 0xc0, 0x78, 0x56, 0x34, 0x12], 0x1000, |i| {
        matches!(i, IrInstruction::Test { .. })
    });
}

#[test]
fn test_oracle_alu_immediate_83_and_81() {
    // add eax, 42 (83 c0 2a)
    check_instruction(&[0x83, 0xc0, 0x2a], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Add {
                src: Operand::Imm(42, 32),
                ..
            }
        )
    });
    // sub rbx, 10 (48 83 eb 0a)
    check_instruction(&[0x48, 0x83, 0xeb, 0x0a], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Sub {
                src: Operand::Imm(10, 64),
                ..
            }
        )
    });
    // xor rcx, -1 (48 83 f1 ff)
    check_instruction(&[0x48, 0x83, 0xf1, 0xff], 0x1000, |i| {
        matches!(i, IrInstruction::Xor { .. })
    });

    // add eax, 0x12345678 (81 c0 78 56 34 12)
    check_instruction(&[0x81, 0xc0, 0x78, 0x56, 0x34, 0x12], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Add {
                src: Operand::Imm(0x12345678, 32),
                ..
            }
        )
    });
    // cmp rbx, 0x12345678 (48 81 fb 78 56 34 12)
    check_instruction(&[0x48, 0x81, 0xfb, 0x78, 0x56, 0x34, 0x12], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Cmp {
                right: Operand::Imm(0x12345678, 64),
                ..
            }
        )
    });
}

#[test]
fn test_oracle_memory_addressing() {
    // mov eax, [rbp - 4] (8b 45 fc)
    check_instruction(&[0x8b, 0x45, 0xfc], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Mov {
                dst: Operand::Reg(..),
                src: Operand::Mem { base: Some(b), index: None, disp: -4, width: 32 },
            } if b == "rbp"
        )
    });

    // mov [rsp + 8], rax (48 89 44 24 08)
    check_instruction(&[0x48, 0x89, 0x44, 0x24, 0x08], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Mov {
                dst: Operand::Mem { base: Some(b), index: None, disp: 8, width: 64 },
                src: Operand::Reg(..),
            } if b == "rsp"
        )
    });

    // mov [rsp], rax (48 89 04 24)
    check_instruction(&[0x48, 0x89, 0x04, 0x24], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Mov {
                dst: Operand::Mem { base: Some(b), index: None, disp: 0, width: 64 },
                src: Operand::Reg(..),
            } if b == "rsp"
        )
    });

    // add eax, [rcx + rdx*4 + 0x20] (03 44 91 20)
    check_instruction(&[0x03, 0x44, 0x91, 0x20], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Add {
                dst: Operand::Reg(..),
                src: Operand::Mem { base: Some(b), index: Some((idx, 4)), disp: 0x20, width: 32 },
            } if b == "rcx" && idx == "rdx"
        )
    });

    // mov dword ptr [rsp + 16], 0x42 (c7 44 24 10 42 00 00 00)
    check_instruction(
        &[0xc7, 0x44, 0x24, 0x10, 0x42, 0x00, 0x00, 0x00],
        0x1000,
        |i| {
            matches!(
                i,
                IrInstruction::Mov {
                    dst: Operand::Mem { base: Some(b), index: None, disp: 16, width: 32 },
                    src: Operand::Imm(0x42, 32),
                } if b == "rsp"
            )
        },
    );
}

#[test]
fn test_oracle_rip_relative_addressing() {
    // mov eax, [rip + 0x100] (8b 05 00 01 00 00 at ip=0x1000)
    // next_ip = 0x1000 + 6 = 0x1006. target = 0x1006 + 0x100 = 0x1106.
    check_instruction(&[0x8b, 0x05, 0x00, 0x01, 0x00, 0x00], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Mov {
                dst: Operand::Reg(r, 32),
                src: Operand::Mem { base: None, index: None, disp: 0x1106, width: 32 },
            } if r == "eax"
        )
    });
}

#[test]
fn test_oracle_jumps_and_branches() {
    // jmp rel8 (eb 10 at 0x1000 -> target 0x1012)
    check_instruction(&[0xeb, 0x10], 0x1000, |i| {
        matches!(i, IrInstruction::Jmp { target: 0x1012 })
    });

    // jmp rel32 (e9 00 10 00 00 at 0x1000 -> target 0x2005)
    check_instruction(&[0xe9, 0x00, 0x10, 0x00, 0x00], 0x1000, |i| {
        matches!(i, IrInstruction::Jmp { target: 0x2005 })
    });

    // jne rel8 (75 08 at 0x1000 -> target 0x100a)
    check_instruction(&[0x75, 0x08], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Jcc {
                cond: BranchCondition::NotEqual,
                target_true: 0x100a,
                ..
            }
        )
    });

    // je rel8 (74 14 at 0x1000 -> target 0x1016)
    check_instruction(&[0x74, 0x14], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Jcc {
                cond: BranchCondition::Equal,
                target_true: 0x1016,
                ..
            }
        )
    });

    // jg rel32 (0f 8f 50 00 00 00 at 0x1000 -> target 0x1056)
    check_instruction(&[0x0f, 0x8f, 0x50, 0x00, 0x00, 0x00], 0x1000, |i| {
        matches!(
            i,
            IrInstruction::Jcc {
                cond: BranchCondition::GreaterThanSigned,
                target_true: 0x1056,
                ..
            }
        )
    });
}
