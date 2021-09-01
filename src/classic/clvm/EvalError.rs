use std::rc::Rc;
use crate::classic::clvm::CLVMObject::{CLVMObject};

pub struct EvalError {
    line: u32,
    col: u32,
    desc: String,
    sexp: Option<Rc<CLVMObject>>
}

impl EvalError {
    pub fn new_str(s: String) -> EvalError {
        return EvalError { line: 0, col: 0, desc: s, sexp: None };
    }

    pub fn new(s: String, sexp: Rc<CLVMObject>) -> EvalError {
        return EvalError { line: 0, col: 0, desc: s, sexp: Some(sexp.clone()) };
    }
}
