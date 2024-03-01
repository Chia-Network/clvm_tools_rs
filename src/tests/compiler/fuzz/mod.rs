use std::rc::Rc;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

mod modules_with_constant_exports;

#[derive(Debug)]
struct GenError { message: String }
impl From<&str> for GenError {
    fn from(m: &str) -> GenError { GenError { message: m.to_string() } }
}

fn compose_sexp(loc: Srcloc, s: &str) -> Rc<SExp> {
    parse_sexp(loc, s.bytes()).expect("should parse")[0].clone()
}
