use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::compiler::compiler::compile_file;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::evaluate::Evaluator;
use crate::compiler::frontend::{from_clvm, frontend};
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

fn shrink_expr_from_string(s: String) -> Result<String, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    let loc = Srcloc::start(&"*program*".to_string());
    parse_sexp(loc.clone(), &s)
        .map_err(|e| {
            return CompileErr(e.0.clone(), e.1.clone());
        })
        .and_then(|parsed_program| {
            return frontend(opts.clone(), parsed_program);
        })
        .and_then(|program| {
            let e = Evaluator::new(opts.clone(), runner, program.helpers);
            return e.shrink_bodyform(
                &mut allocator,
                program.args.clone(),
                &HashMap::new(),
                program.exp.clone(),
                false,
            );
        })
        .map(|result| result.to_sexp().to_string())
}

#[test]
fn test_basic_shrink_arithmetic() {
    assert_eq!(
        shrink_expr_from_string("(+ 3 (- 10 7))".to_string()).unwrap(),
        "(q . 6)".to_string()
    );
}

#[test]
fn test_basic_expand_macro() {
    assert_eq!(
        shrink_expr_from_string("(if 3 1 0)".to_string()).unwrap(),
        "(q . 1)"
    );
}

#[test]
fn test_basic_expand_macro_2() {
    assert_eq!(
        shrink_expr_from_string("(list 1 2 3)".to_string()).unwrap(),
        "(q 1 2 3)"
    );
}

#[test]
fn test_basic_expand_macro_3() {
    assert_eq!(
        shrink_expr_from_string("(mod (A) (list 1 A))".to_string()).unwrap(),
        "(c (q . 1) (c A (q)))"
    );
}

fn convert_clvm_to_chialisp(s: String) -> Result<Rc<SExp>, CompileErr> {
    let loc = Srcloc::start(&"*program*".to_string());
    parse_sexp(loc.clone(), &s)
        .map_err(|e| {
            return CompileErr(e.0.clone(), e.1.clone());
        })
        .map(|parsed_program| from_clvm(parsed_program[0].clone()))
}

#[test]
fn test_simple_conversion_from_clvm_to_chialisp() {
    let converted = convert_clvm_to_chialisp("(+ (q . 3) 2)".to_string()).unwrap();
    assert_eq!(converted.to_string(), "(+ (q . 3) (@ 2))");
}

#[test]
fn test_basic_expand_macro_4() {
    assert_eq!(
        shrink_expr_from_string(
            "(mod () (defun torp (S A B) (if S (+ A B) (* A B))) (torp 0 2 3))".to_string()
        )
        .unwrap(),
        "(q . 6)"
    );
}

#[test]
fn test_expand_with_recursive_1() {
    assert_eq!(
        shrink_expr_from_string("(mod () (defun factorial (input_$_11) (if (= input_$_11 1) 1 (* (factorial (- input_$_11 1)) input_$_11))) (factorial 3))".to_string()).unwrap(),
        "(q . 6)"
    );
}

fn compile_with_fe_opt(s: String) -> Result<String, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut opts: Rc<dyn CompilerOpts> =
        Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    opts = opts.set_frontend_opt(true);
    compile_file(&mut allocator, runner, opts, &s, &mut HashMap::new()).map(|r| r.to_string())
}

#[test]
fn test_simple_fe_opt_compile_1() {
    assert_eq!(
        compile_with_fe_opt("(mod () 99)".to_string()).unwrap(),
        "(2 (1 1 . 99) (4 (1) 1))".to_string()
    );
}
