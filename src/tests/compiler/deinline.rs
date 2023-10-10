use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::clvm::run;
use crate::compiler::codegen::codegen;
use crate::compiler::compiler::{DefaultCompilerOpts, do_desugar};
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::frontend::frontend;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{SExp, parse_sexp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::test_deinline::ProgramWithConstants;
use crate::tests::compiler::TEST_TIMEOUT;

#[test]
fn test_deinliner() {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let test_prog_name = "resources/tests/deinline/test-basic-deinline.clsp";
    let loaded_code = fs::read_to_string(test_prog_name).expect("should be present");
    let opts = Rc::new(DefaultCompilerOpts::new(test_prog_name)).set_search_paths(&["resources/tests/bridge-includes".to_string()]);
    let parsed_code = parse_sexp(Srcloc::start(test_prog_name), loaded_code.as_bytes().iter().copied()).expect("should parse");
    let orig_program = frontend(opts.clone(), &parsed_code).expect("should be a valid program");
    let deinlined_program = ProgramWithConstants::make_testable(orig_program).expect("should be suitable");
    let desugared = do_desugar(&deinlined_program.program).expect("should desugar");
    let mut symbols = HashMap::new();
    let generated = codegen(&mut allocator, runner.clone(), opts, &desugared, &mut symbols).expect("should generate");

    let run_outcome = run(
        &mut allocator,
        runner,
        Rc::new(HashMap::new()),
        Rc::new(generated),
        deinlined_program.constants,
        Some(TEST_TIMEOUT),
    ).map_err(|e| match e {
        RunFailure::RunErr(l, s) => CompileErr(l, s),
        RunFailure::RunExn(l, s) => CompileErr(l, s.to_string()),
    }).expect("should run ok");
    assert_eq!(run_outcome, Rc::new(SExp::Nil(desugared.loc.clone())));
}
