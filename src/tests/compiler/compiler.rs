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
    let opts = Rc::new(DefaultCompilerOpts::new());

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
