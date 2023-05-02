use std::rc::Rc;

use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[test]
fn test_runfailure_err() {
    let loc = Srcloc::start("test.clsp");
    let errstr = "Error".to_string();
    let want_err = format!("{loc}: {errstr}");
    assert_eq!(RunFailure::RunErr(loc, errstr).to_string(), want_err);
}

#[test]
fn test_runfailure_exn() {
    let loc = Srcloc::start("test.clsp");
    let err = Rc::new(SExp::Atom(loc.clone(), b"test".to_vec()));
    let want_err = format!("{loc}: throw(x) {err}");
    assert_eq!(RunFailure::RunExn(loc, err).to_string(), want_err);
}
