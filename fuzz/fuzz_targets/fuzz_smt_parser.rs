#![no_main]

use libfuzzer_sys::fuzz_target;
use smt_parser::Parser;

fuzz_target!(|data: &[u8]| {
    // Fuzz the SMT-LIB 2.6 grammar parser across arbitrary UTF-8/binary streams.
    // The parser must never panic on malformed sexprs, deeply nested parentheses, or hostile identifiers.
    if let Ok(s) = std::str::from_utf8(data) {
        let mut parser = Parser::new(s);
        let _ = parser.parse_script();
    }
});
