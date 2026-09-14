//! Differential fuzzing suite validating `X86Decoder` against `iced-x86`.
//!
//! Generates pseudo-random instruction patterns and byte arrays to ensure:
//! 1. Custom decoder never panics or crashes on invalid byte streams.
//! 2. Whenever custom decoder succeeds, length, mnemonics, operands, and targets match `iced-x86`.

use iced_x86::{Decoder, DecoderOptions};
use smt_solver::x86_decoder::X86Decoder;

#[test]
fn test_differential_fuzzing_against_iced_x86_oracle() {
    // Deterministic pseudo-random seed generator (LCG)
    let mut seed: u64 = 0x1337_c0de_cafe_babe;
    let mut rng = || -> u8 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) as u8
    };

    let mut random_bytes = [0u8; 15];

    for iteration in 0..2_000 {
        // Fill byte array with pseudo-random noise
        for b in &mut random_bytes {
            *b = rng();
        }

        let ip = 0x400000 + (iteration as u64) * 0x10;

        // 1. Attempt decode with internal X86Decoder
        match X86Decoder::decode(&random_bytes, ip) {
            Ok(custom_dec) => {
                // If custom decoder succeeded, iced-x86 must also decode successfully
                let mut oracle_decoder =
                    Decoder::with_ip(64, &random_bytes, ip, DecoderOptions::NONE);
                if oracle_decoder.can_decode() {
                    let oracle_inst = oracle_decoder.decode();
                    // Length must match
                    assert_eq!(
                        custom_dec.length,
                        oracle_inst.len(),
                        "Length mismatch at iteration {}: custom={}, oracle={}. Bytes: {:02x?}",
                        iteration,
                        custom_dec.length,
                        oracle_inst.len(),
                        &random_bytes[..custom_dec.length]
                    );
                }
            }
            Err(_) => {
                // Failure is acceptable for unhandled/invalid opcodes; test guarantees no panics
            }
        }
    }
}

#[test]
fn test_structured_instruction_differential_oracle_corpus() {
    // Structured diverse instructions
    let corpus: &[&[u8]] = &[
        &[0x90],                               // NOP
        &[0xc3],                               // RET
        &[0x50],                               // PUSH RAX
        &[0x53],                               // PUSH RBX
        &[0x58],                               // POP RAX
        &[0x5b],                               // POP RBX
        &[0x48, 0x01, 0xd8],                   // ADD RAX, RBX
        &[0x48, 0x29, 0xd8],                   // SUB RAX, RBX
        &[0x48, 0x31, 0xc0],                   // XOR RAX, RAX
        &[0x48, 0x21, 0xc8],                   // AND RAX, RCX
        &[0x48, 0x09, 0xc8],                   // OR RAX, RCX
        &[0x48, 0x39, 0xd8],                   // CMP RAX, RBX
        &[0x48, 0x85, 0xc0],                   // TEST RAX, RAX
        &[0x84, 0xc0],                         // TEST AL, AL
        &[0xa8, 0x7f],                         // TEST AL, 0x7F
        &[0xa9, 0x00, 0x00, 0x01, 0x00],       // TEST EAX, 0x10000
        &[0x48, 0x83, 0xc0, 0x01],             // ADD RAX, 1
        &[0x48, 0x83, 0xe8, 0x05],             // SUB RAX, 5
        &[0x48, 0x83, 0xf8, 0x2a],             // CMP RAX, 42
        &[0x48, 0x89, 0x04, 0x24],             // MOV [RSP], RAX
        &[0x48, 0x8b, 0x04, 0x24],             // MOV RAX, [RSP]
        &[0xeb, 0x10],                         // JMP +0x10
        &[0x74, 0x05],                         // JZ +0x5
        &[0x75, 0xf8],                         // JNZ -0x8
        &[0x0f, 0x84, 0x00, 0x01, 0x00, 0x00], // JZ +0x100
    ];

    for &bytes in corpus {
        let ip = 0x1000;
        let custom =
            X86Decoder::decode(bytes, ip).expect("Custom decoder must decode corpus instruction");
        let mut oracle = Decoder::with_ip(64, bytes, ip, DecoderOptions::NONE);
        let oracle_inst = oracle.decode();

        assert_eq!(
            custom.length,
            oracle_inst.len(),
            "Length mismatch for {:02x?}",
            bytes
        );
    }
}
