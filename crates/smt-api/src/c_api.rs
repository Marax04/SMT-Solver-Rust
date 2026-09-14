//! C-ABI Foreign Function Interface (FFI) for drop-in integration with C/Python/angr tools.

use num_bigint::BigUint;
use num_traits::ToPrimitive;
use smt_core::term::{Op, TermId};
use smt_core::value::Value;
use smt_solver::engine::{CheckSatResult, Solver};
use std::ffi::CStr;
use std::os::raw::c_char;

/// Creates a new solver instance.
#[no_mangle]
pub extern "C" fn smt_solver_new() -> *mut Solver {
    Box::into_raw(Box::new(Solver::new()))
}

/// Frees a solver instance.
#[no_mangle]
pub extern "C" fn smt_solver_free(solver: *mut Solver) {
    if !solver.is_null() {
        unsafe {
            drop(Box::from_raw(solver));
        }
    }
}

/// Declares a Bit-Vector constant variable.
#[no_mangle]
pub extern "C" fn smt_declare_bv_var(solver: *mut Solver, name: *const c_char, width: u32) -> u32 {
    if solver.is_null() || name.is_null() {
        return 0;
    }
    let s = unsafe { &mut *solver };
    let c_str = unsafe { CStr::from_ptr(name) };
    let name_str = c_str.to_str().unwrap_or("var");
    let sort = s.sorts.bv(width);
    let term = s.declare_const(name_str, sort);
    term.0
}

/// Creates a bit-vector literal from a 64-bit integer.
#[no_mangle]
pub extern "C" fn smt_mk_bv_const(solver: *mut Solver, val: u64, width: u32) -> u32 {
    if solver.is_null() {
        return 0;
    }
    let s = unsafe { &mut *solver };
    let term = s.terms.bv_const(BigUint::from(val), width, &mut s.sorts);
    term.0
}

/// Constructs a bit-vector addition term: `(bvadd a b)`.
#[no_mangle]
pub extern "C" fn smt_mk_bv_add(solver: *mut Solver, a: u32, b: u32) -> u32 {
    if solver.is_null() {
        return 0;
    }
    let s = unsafe { &mut *solver };
    s.terms.bv_binop(Op::BvAdd, TermId(a), TermId(b)).map(|t| t.0).unwrap_or(0)
}

/// Constructs a bit-vector xor term: `(bvxor a b)`.
#[no_mangle]
pub extern "C" fn smt_mk_bv_xor(solver: *mut Solver, a: u32, b: u32) -> u32 {
    if solver.is_null() {
        return 0;
    }
    let s = unsafe { &mut *solver };
    s.terms.bv_binop(Op::BvXor, TermId(a), TermId(b)).map(|t| t.0).unwrap_or(0)
}

/// Constructs an equality term: `(= a b)`.
#[no_mangle]
pub extern "C" fn smt_mk_eq(solver: *mut Solver, a: u32, b: u32) -> u32 {
    if solver.is_null() {
        return 0;
    }
    let s = unsafe { &mut *solver };
    let t = s.terms.eq(TermId(a), TermId(b), &s.sorts);
    t.0
}

/// Asserts a formula constraint into the solver.
#[no_mangle]
pub extern "C" fn smt_assert(solver: *mut Solver, term: u32) {
    if !solver.is_null() {
        let s = unsafe { &mut *solver };
        s.assert_formula(TermId(term));
    }
}

/// Checks satisfiability: returns 1 for SAT, 0 for UNSAT, -1 for UNKNOWN.
#[no_mangle]
pub extern "C" fn smt_check_sat(solver: *mut Solver) -> i32 {
    if solver.is_null() {
        return -1;
    }
    let s = unsafe { &mut *solver };
    match s.check_sat() {
        CheckSatResult::Sat => 1,
        CheckSatResult::Unsat => 0,
        CheckSatResult::Unknown => -1,
    }
}

/// Retrieves the evaluated 64-bit value of a variable from the model.
#[no_mangle]
pub extern "C" fn smt_get_model_bv_u64(solver: *mut Solver, name: *const c_char) -> u64 {
    if solver.is_null() || name.is_null() {
        return 0;
    }
    let s = unsafe { &*solver };
    let c_str = unsafe { CStr::from_ptr(name) };
    let name_str = c_str.to_str().unwrap_or("");
    if let Some(model) = s.get_model() {
        if let Some(Value::BitVec { value, .. }) = model.get(name_str) {
            return value.to_u64().unwrap_or(0);
        }
    }
    0
}
