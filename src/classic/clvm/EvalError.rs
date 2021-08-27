use crate::classic::clvm::CLVMObject::{CLVMObject};

pub struct EvalError {
    line: u32,
    col: u32,
    desc: String,
    sexp: Option<Box<CLVMObject>>
}

impl EvalError {
    pub fn new_str(s : String) -> EvalError {
        return EvalError { line: 0, col: 0, desc: s, sexp: None };
    }
}
