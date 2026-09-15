#![no_main]

use libfuzzer_sys::fuzz_target;
use smt_solver::decoder::X86Decoder;

fuzz_target!(|data: &[u8]| {
    // Fuzz the x86 machine code decoder across arbitrary byte streams.
    // The decoder must never panic, crash, or enter unbounded recursion on adversarial inputs.
    let mut offset = 0;
    let limit = data.len().min(64); // Decode up to 64 bytes per iteration
    while offset < limit {
        match X86Decoder::decode(&data[offset..], 0x401000 + offset as u64) {
            Ok(insn) => {
                if insn.length == 0 {
                    break;
                }
                offset += insn.length;
            }
            Err(_) => {
                // Controlled, typed error
                offset += 1;
            }
        }
    }
});
