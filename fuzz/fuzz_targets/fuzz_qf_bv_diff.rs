#![no_main]

use libfuzzer_sys::fuzz_target;
use smt_core::term::TermPool;
use smt_core::sort::Sort;

fuzz_target!(|data: &[u8]| {
    if data.len() < 8 {
        return;
    }
    // Fuzz bitvector simplification and evaluation consistency
    let mut pool = TermPool::new();
    let x_val = u64::from_le_bytes(data[0..8].try_into().unwrap());
    let x_term = pool.bv_const(x_val, 64);
    let zero = pool.bv_const(0, 64);
    let xor_self = pool.bvxor(x_term, x_term);

    // Algebraic identity: x ^ x must simplify to 0
    assert_eq!(xor_self, zero, "x ^ x identity violated");
});
