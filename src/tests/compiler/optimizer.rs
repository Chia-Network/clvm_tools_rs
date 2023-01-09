use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::sexp::sexp_as_bin;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs};
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

struct CompileRunResult {
    pub compiled: Rc<SExp>,
    pub compiled_hex: String,
    pub run_result: Rc<SExp>,
    pub run_cost: u64
}

struct OptRunResult {
    unopt: CompileRunResult,
    opt: CompileRunResult
}

fn run_with_cost(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    sexp: Rc<SExp>,
    env: Rc<SExp>
) -> Result<CompileRunResult, RunFailure> {
    let as_classic_program = convert_to_clvm_rs(allocator, sexp.clone())?;
    let as_classic_env = convert_to_clvm_rs(allocator, env.clone())?;
    let compiled_hex = sexp_as_bin(allocator, as_classic_program).hex();
    runner.run_program(
        allocator,
        as_classic_program,
        as_classic_env,
        None
    ).map_err(|e| {
        RunFailure::RunErr(sexp.loc(), format!("{} in {} {}", e.1, sexp, env))
    }).and_then(|reduction| {
        Ok(CompileRunResult {
            compiled: sexp.clone(),
            compiled_hex,
            run_result: convert_from_clvm_rs(allocator, sexp.loc(), reduction.1)?,
            run_cost: reduction.0
        })
    })
}

fn run_string_get_program_and_output(
    content: &str, args: &str, fe_opt: bool
) -> Result<CompileRunResult, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));
    let srcloc = Srcloc::start(&"*test*".to_string());
    opts = opts
        .set_frontend_opt(fe_opt)
        .set_search_paths(&vec!["resources/tests".to_string()]);
    let sexp_args =
        parse_sexp(srcloc.clone(), args.bytes()).map_err(|e| CompileErr(e.0, e.1))?[0].clone();

    compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &content,
        &mut HashMap::new(),
    )
        .and_then(|program| {
            run_with_cost(
                &mut allocator,
                runner,
                Rc::new(program),
                sexp_args
            )
                .map_err(|e| match e {
                    RunFailure::RunErr(l, s) => CompileErr(l, s),
                    RunFailure::RunExn(l, s) => CompileErr(l, s.to_string()),
                })
        })
}

fn do_compile_and_run_opt_size_test(
    prog: &str, env: &str
) -> Result<OptRunResult, CompileErr> {
    let unopt_run = run_string_get_program_and_output(prog, env, false)?;
    let opt_run = run_string_get_program_and_output(prog, env, true)?;

    // Ensure the runs had the same output.
    assert_eq!(unopt_run.run_result, opt_run.run_result);

    Ok(OptRunResult {
        unopt: unopt_run,
        opt: opt_run
    })
}

#[test]
fn smoke_test_optimizer() {
    let res = do_compile_and_run_opt_size_test(
        indoc!{"
        (mod ()
         (include *standard-cl-22*)
         (defun-inline F (X Y) (+ X Y))
         (let ((A 2) (B 4)) (F A B))
          )
        "},
        "()"
    ).expect("should compile and run");
    assert!(res.opt.compiled_hex.len() < res.unopt.compiled_hex.len());
    assert!(res.opt.run_cost < res.unopt.run_cost);
    assert_eq!(res.opt.compiled.to_string(), "(2 (1 1 . 6) (4 (1) 1))");
}
