//! SMT-LIB 2.6 Command AST representation.

use smt_core::sort::SortId;
use smt_core::term::TermId;

/// An executed SMT-LIB top-level command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// `(set-logic <symbol>)`
    SetLogic(String),
    /// `(set-info <keyword> <value>)`
    SetInfo(String, String),
    /// `(set-option <keyword> <value>)`
    SetOption(String, String),
    /// `(declare-sort <symbol> <numeral>)`
    DeclareSort(String, u32),
    /// `(declare-const <symbol> <sort>)`
    DeclareConst(String, SortId),
    /// `(declare-fun <symbol> (<sort>*) <sort>)`
    DeclareFun(String, Vec<SortId>, SortId),
    /// `(define-fun <symbol> ((<symbol> <sort>)*) <sort> <term>)`
    DefineFun(String, Vec<(String, SortId)>, SortId, TermId),
    /// `(assert <term>)`
    Assert(TermId),
    /// `(check-sat)`
    CheckSat,
    /// `(check-sat-assuming (<prop-literal>*))`
    CheckSatAssuming(Vec<TermId>),
    /// `(get-model)`
    GetModel,
    /// `(get-unsat-core)`
    GetUnsatCore,
    /// `(get-value (<term>*))`
    GetValue(Vec<TermId>),
    /// `(push <numeral>)`
    Push(u32),
    /// `(pop <numeral>)`
    Pop(u32),
    /// `(reset)`
    Reset,
    /// `(exit)`
    Exit,
}
