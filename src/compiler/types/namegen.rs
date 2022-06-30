use crate::compiler::gensym::gensym;
use crate::compiler::types::ast::{TypeVar, Var};

pub fn fresh_name(seq: &Vec<u8>) -> String {
    std::str::from_utf8(&gensym(seq.to_vec())).expect("failed to make fresh var").to_string()
}

pub fn fresh_var() -> Var {
    Var(fresh_name(&"var".as_bytes().to_vec()))
}

pub fn fresh_tvar() -> TypeVar {
    TypeVar(fresh_name(&"tvar".as_bytes().to_vec()))
}
