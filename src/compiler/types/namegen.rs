use crate::compiler::gensym::gensym;
use crate::compiler::srcloc::Srcloc;
use crate::compiler::types::ast::{TypeVar, Var};

pub fn fresh_name(seq: &[u8]) -> String {
    std::str::from_utf8(&gensym(seq.to_vec()))
        .expect("failed to make fresh var")
        .to_string()
}

pub fn fresh_var(l: Srcloc) -> Var {
    Var(fresh_name("var".as_bytes()), l)
}

pub fn fresh_tvar(l: Srcloc) -> TypeVar {
    TypeVar(fresh_name("tvar".as_bytes()), l)
}
