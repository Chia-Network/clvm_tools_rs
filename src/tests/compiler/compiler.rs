use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::compiler::{
    DefaultCompilerOpts,
    compile_file
};
use crate::compiler::comptypes::{
    CompileErr
};

fn compile_string(content: &String) -> Result<String, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));

    compile_file(
        &mut allocator,
        runner,
        opts,
        &content
    )
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
