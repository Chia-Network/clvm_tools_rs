use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[derive(Debug, Clone, PartialEq)]
pub enum RunFailure {
    RunErr(Srcloc, String),
    RunExn(Srcloc, Rc<SExp>),
}

fn collapse<A>(r: Result<A, A>) -> A {
    match r {
        Ok(a) => a,
        Err(a) => a,
    }
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

fn run_to_string<A>(cvt: &dyn Fn(&A) -> String, r: Result<A, RunFailure>) -> String {
    collapse(r.map(|a| cvt(&a)).map_err(|o| o.to_string()))
}
