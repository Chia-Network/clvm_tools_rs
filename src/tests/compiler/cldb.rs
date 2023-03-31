use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::cldb::{CldbNoOverride, CldbRun, CldbRunEnv};
use crate::compiler::clvm::start_step;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::prims;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;

#[test]
fn test_run_clvm_in_cldb() {
    let program_name = "fact.clsp";
    let program_code = "(mod (X) (include *standard-cl-21*) (defun fact (X) (if (> X 1) (* X (fact (- X 1))) 1)) (fact X))";
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(program_name));
    let mut symbols = HashMap::new();
    let args = parse_sexp(Srcloc::start("*args*"), "(5)".bytes()).expect("should parse")[0].clone();

    let program = compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &program_code,
        &mut symbols,
    )
    .expect("should compile");

    let mut prim_map = HashMap::new();
    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }
    let program_lines: Vec<String> = program_code.lines().map(|x| x.to_string()).collect();

    let step = start_step(Rc::new(program), args);
    let cldbenv = CldbRunEnv::new(
        Some(program_name.to_string()),
        program_lines,
        Box::new(CldbNoOverride::new_symbols(symbols)),
    );
    let mut cldbrun = CldbRun::new(runner, Rc::new(prim_map), Box::new(cldbenv), step);
    let mut output: BTreeMap<String, String> = BTreeMap::new();

    loop {
        if cldbrun.is_ended() {
            assert_eq!(output.get("Final"), Some(&"120".to_string()));
            return;
        }

        if let Some(result) = cldbrun.step(&mut allocator) {
            output = result;
        }
    }
}
