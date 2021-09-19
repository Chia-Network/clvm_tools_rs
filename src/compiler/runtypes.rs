use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

pub enum RunFailure {
    RunErr(Srcloc, String),
    RunExn(Srcloc, Rc<SExp>)
}

fn collapse<A>(r: Result<A,A>) -> A {
    match r {
        Ok(a) => a,
        Err(a) => a
    }
}

fn run_to_string<A>(cvt: &dyn Fn(&A) -> String, r: Result<A, RunFailure>) -> String {
    collapse(r.map(|a| cvt(&a)).map_err(|o| match o {
        RunFailure::RunErr(l, s) => format!("{}: throw(x) {}", l.to_string(), s),
        RunFailure::RunExn(l, s) => format!("{}: {}", l.to_string(), s.to_string())
    }))
}
