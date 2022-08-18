use std::fmt::Display;
use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunFailure {
    RunErr(Srcloc, String),
    RunExn(Srcloc, Rc<SExp>),
}

impl Display for RunFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            RunFailure::RunExn(l, s) => {
                l.fmt(formatter)?;
                formatter.write_str(": throw(x) ")?;
                s.fmt(formatter)?;
            }
            RunFailure::RunErr(l, s) => {
                l.fmt(formatter)?;
                formatter.write_str(": ")?;
                s.fmt(formatter)?;
            }
        }
        Ok(())
    }
}
