use crate::compiler::gensym;

pub fn fresh_name(seq: &Vec<u8>) -> String {
    str::from_utf8(gensym(seq.to_vec())).expect("failed to make fresh var")
}

pub fn fresh_var() -> Var {
    Var(fresh_name("var"))
}

pub fn fresh_tvar() -> TVar {
    TVar(fresh_name("tvar"))
}
