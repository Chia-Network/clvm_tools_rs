use std::rc::Rc;

use clvm_rust::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;
use crate::compiler::usecheck::check_parameters_used_compileform;

fn check_argument_use(input_program: String) -> Vec<String> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts: Rc<dyn CompilerOpts> =
        Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));
    let pre_forms =
        parse_sexp(Srcloc::start(&opts.filename()), &input_program).
        map_err(|e| CompileErr(e.0, e.1)).expect("should parse");
    let g = frontend(opts.clone(), pre_forms).expect("should pass frontend");
    let set = check_parameters_used_compileform(opts, Rc::new(g)).
        expect("should be able to determine unused vars");
    let mut result = Vec::new();
    for x in set.iter() {
        result.push(Bytes::new(Some(BytesFromType::Raw(x.clone()))).decode());
    }
    result.sort();
    result
}

fn empty_vec() -> Vec<String> { vec![] }

#[test]
fn check_unused_base_case_0() {
    assert_eq!(
        check_argument_use("(mod () (x))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_base_case_1() {
    assert_eq!(
        check_argument_use("(mod (_) (x))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_base_case_2() {
    assert_eq!(
        check_argument_use("(mod (A) (x))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_base_case_3() {
    assert_eq!(
        check_argument_use("(mod (a) (x))".to_string()),
        vec!["a".to_string()]
    );
}

#[test]
fn check_unused_base_case_4() {
    assert_eq!(
        check_argument_use("(mod (a) (x a))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_fun_1() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (g) (+ g 1)) (F a))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_fun_2() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (g) (+ 2 3)) (F a))".to_string()),
        vec!["a".to_string()]
    );
}

#[test]
fn check_unused_fun_if_1() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (g h) (if g (+ h 1) ())) (F () a))".to_string()),
        vec!["a".to_string()]
    );
}

#[test]
fn check_unused_fun_if_2() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (g h) (if g (+ h 1) ())) (F 1 a))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_fun_rec_1() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (X) (if X (F (- X 1)) ())) (F a))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_fun_rec_2() {
    assert_eq!(
        check_argument_use("(mod (a) (defun F (R) (if R (F (- R 1)) R)) (F a))".to_string()),
        empty_vec()
    );
}

#[test]
fn check_unused_fun_rec_3() {
    assert_eq!(
        check_argument_use("(mod (a b) (defun F (X Y) (if X (F (- X 1) Y) X)) (F a b))".to_string()),
        vec!["b".to_string()]
    );
}

#[test]
fn check_unused_fun_rec_4() {
    assert_eq!(
        check_argument_use("(mod (a b) (defun G (s t) t) (defun F (a b) (if b (F a (- b 1)) (G a b))) (F a b))".to_string()),
        vec!["a".to_string()]
    );
}
