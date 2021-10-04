use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::clvm::run;
use crate::compiler::compiler::{
    DefaultCompilerOpts,
    compile_file
};
use crate::compiler::comptypes::{
    CompileErr
};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::Srcloc;

fn compile_string(content: &String) -> Result<String, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));

    compile_file(
        &mut allocator,
        runner,
        opts,
        &content
    ).map(|x| x.to_string())
}

fn run_string(content: &String, args: &String) -> Result<Rc<SExp>, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let srcloc = Srcloc::start(&"*test*".to_string());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));
    let sexp_args = parse_sexp(srcloc.clone(), &args).map_err(|e| {
        CompileErr(e.0, e.1)
    })?[0].clone();

    compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &content
    ).and_then(|x| {
        run(
            &mut allocator,
            runner,
            Rc::new(HashMap::new()),
            Rc::new(x),
            sexp_args
        ).map_err(|e| match e {
            RunFailure::RunErr(l,s) => CompileErr(l, s),
            RunFailure::RunExn(l,s) => CompileErr(l, s.to_string())
        })
    })
}

#[test]
fn compile_test_1() {
    let result =
        compile_string(
            &"(mod () (defmacro testmacro (A) (qq (+ 1 (unquote A)))) (testmacro 3))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 16 (1 . 1) (1 . 3)) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_2() {
    let result =
        compile_string(
            &"(mod () (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @))) (if () (+ 1 3) (+ 5 8)))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 2 (3 (1) (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 5) (1 . 8)) 1)) 1) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_3() {
    let result =
        compile_string(
            &"(mod (A) (include *standard-cl-21*) A)".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 . 5) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_4() {
    let result =
        compile_string(
            &"(mod () (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @))) (if () (+ 1 3) (+ 5 8)))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 2 (3 (1) (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 5) (1 . 8)) 1)) 1) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_5() {
    let result =
        compile_string(
            &"(mod (X) (include *standard-cl-21*) (defmacro testmacro (x) (qq (+ 1 (unquote x)))) (if X (testmacro 3) (testmacro 4)))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 2 (3 5 (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 1) (1 . 4)) 1)) 1) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_6() {
    let result =
        compile_string(
            &"(mod () (list 1 2 3))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 4 (1 . 1) (4 (1 . 2) (4 (1 . 3) (1)))) (4 (1) 1))".to_string());
}

#[test]
fn run_test_1() {
    let result =
        run_string(
            &"(mod () (defun f (a b) (+ (* a a) b)) (f 3 1))".to_string(),
            &"()".to_string()
        ).unwrap();
    assert_eq!(result.to_string(), "10".to_string());
}

#[test]
fn run_test_2() {
    let result =
        run_string(
            &"(mod (c) (defun f (a b) (+ (* a a) b)) (f 3 c))".to_string(),
            &"(4)".to_string()
        ).unwrap();
    assert_eq!(result.to_string(), "13".to_string());
}

#[test]
fn run_test_3() {
    let result =
        run_string(
            &"(mod (arg_one) (defun factorial (input) (if (= input 1) 1 (* (factorial (- input 1)) input))) (factorial arg_one))".to_string(),
            &"(5)".to_string()
        ).unwrap();
    assert_eq!(result.to_string(), "120".to_string());
}

#[test]
fn run_test_4() {
    let result =
        run_string(
            &"(mod () (defun makelist (a) (if a (c (q . 4) (c (f a) (c (makelist (r a)) (q . ())))) (q . ()))) (makelist (q . (1 2 3))))".to_string(),
            &"()".to_string()
        ).unwrap();
    assert_eq!(result.to_string(), "(4 1 (4 2 (4 3 ())))".to_string());
}
