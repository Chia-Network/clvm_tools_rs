use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[derive(Debug, Clone, PartialEq)]
pub enum RunFailure {
    RunErr(Srcloc, String),
    RunExn(Srcloc, Rc<SExp>),
}

impl RunFailure {
    pub fn to_string(&self) -> String {
        match self {
            RunFailure::RunExn(l, s) => {
                format!("{}: throw(x) {}", l.to_string(), s.to_string())
            }
            RunFailure::RunErr(l, s) => {
                format!("{}: {}", l.to_string(), s)
            }
        }
    }
}
