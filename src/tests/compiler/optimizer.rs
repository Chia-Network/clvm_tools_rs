use std::collections::HashMap;
use std::fs;
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
    // pub compiled: Rc<SExp>,
    pub compiled_hex: String,
    pub run_result: Rc<SExp>,
    pub run_cost: u64,
}

struct OptRunResult {
    unopt: CompileRunResult,
    opt: CompileRunResult,
}

fn run_with_cost(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    sexp: Rc<SExp>,
    env: Rc<SExp>,
) -> Result<CompileRunResult, RunFailure> {
    let as_classic_program = convert_to_clvm_rs(allocator, sexp.clone())?;
    let as_classic_env = convert_to_clvm_rs(allocator, env.clone())?;
    let compiled_hex = sexp_as_bin(allocator, as_classic_program).hex();
    runner
        .run_program(allocator, as_classic_program, as_classic_env, None)
        .map_err(|e| RunFailure::RunErr(sexp.loc(), format!("{} in {} {}", e.1, sexp, env)))
        .and_then(|reduction| {
            Ok(CompileRunResult {
                // compiled: sexp.clone(),
                compiled_hex,
                run_result: convert_from_clvm_rs(allocator, sexp.loc(), reduction.1)?,
                run_cost: reduction.0,
            })
        })
}

fn run_string_get_program_and_output_with_includes(
    content: &str,
    args: &str,
    include_dirs: &[String],
    fe_opt: bool,
) -> Result<CompileRunResult, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));
    let srcloc = Srcloc::start(&"*test*".to_string());
    opts = opts.set_frontend_opt(fe_opt).set_search_paths(include_dirs);
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
        run_with_cost(&mut allocator, runner, Rc::new(program), sexp_args).map_err(|e| match e {
            RunFailure::RunErr(l, s) => CompileErr(l, s),
            RunFailure::RunExn(l, s) => CompileErr(l, s.to_string()),
        })
    })
}

fn do_compile_and_run_opt_size_test_with_includes(
    prog: &str,
    env: &str,
    includes: &[String],
) -> Result<OptRunResult, CompileErr> {
    let unopt_run = run_string_get_program_and_output_with_includes(prog, env, includes, false)?;
    let opt_run = run_string_get_program_and_output_with_includes(prog, env, includes, true)?;

    // Ensure the runs had the same output.
    assert_eq!(unopt_run.run_result, opt_run.run_result);

    Ok(OptRunResult {
        unopt: unopt_run,
        opt: opt_run,
    })
}

fn do_compile_and_run_opt_size_test(prog: &str, env: &str) -> Result<OptRunResult, CompileErr> {
    do_compile_and_run_opt_size_test_with_includes(prog, env, &["resources/tests".to_string()])
}

#[test]
fn test_optimizer_tables_big_constants() {
    let res = do_compile_and_run_opt_size_test(
        indoc! {"
        (mod (A)
         (include *standard-cl-22*)
         (defconstant X \"hi there this is a test\")
         (c X (c X A))
         )
        "},
        "(test)",
    )
    .expect("should compile and run");
    assert!(res.opt.compiled_hex.len() < res.unopt.compiled_hex.len());
}

#[test]
fn smoke_test_optimizer() {
    let res = do_compile_and_run_opt_size_test(
        indoc! {"
        (mod ()
         (include *standard-cl-22*)
         (defun-inline F (X Y) (+ X Y))
         (let ((A 2) (B 4)) (F A B))
          )
        "},
        "()",
    )
    .expect("should compile and run");
    assert!(res.opt.compiled_hex.len() < res.unopt.compiled_hex.len());
    assert!(res.opt.run_cost < res.unopt.run_cost);
}

#[test]
fn test_optimizer_shrinks_inlines() {
    let res = do_compile_and_run_opt_size_test(
        indoc! {"
        (mod (A)
          (include *standard-cl-22*)
          (defun-inline F (N) (* 3 (+ 1 N)))
          (let* ((FN (F A)))
            (let ((FA (+ FN 1)) (FB (- FN 1)) (FC (* FN 2)))
              (+ FA FB FC)
              )
            )
          )
        "},
        "(3)",
    )
    .expect("should compile and run");
    assert!(res.opt.compiled_hex.len() < res.unopt.compiled_hex.len());
}

#[test]
fn test_optimizer_shrinks_repeated_lets() {
    let res = do_compile_and_run_opt_size_test(
        indoc! {"
    (mod (X)
     (include *standard-cl-22*)
     (defconstant Z 1000000)
     (let
      ((X1 (+ X Z)))
      (+ X1 X1 X1 X1 X1 X1)
     )
    )"},
        "(3)",
    )
    .expect("should compile and run");
    assert!(res.opt.compiled_hex.len() < res.unopt.compiled_hex.len());
}

#[test]
fn test_optimizer_shrinks_q_test_1() {
    let program = fs::read_to_string("resources/tests/optimization/merkle_tree_a2c.clsp")
        .expect("test file should exist");
    let res = do_compile_and_run_opt_size_test_with_includes(
        &program,
        "(0x79539b34c33bc90bdaa6f9a28d3993a1e34025e5f2061fc57f8ff3edb9fb3b85 0x47194347579b7aa1ede51c52ddfd4200d8b560828051608ce599c763fd99291a (() 0xfb3b5605bc59e423b7df9c3bcfa7f559d6cdfcb9a49645dd801b3b24d6e9c439 0xe925a16b925dc355611f46c900ff0c182a3ed29a32d76394ea85b14d760d91c6))",
        &["resources/tests/bridge-includes".to_string()]
    ).expect("should compile and run");
    assert!(res.opt.compiled_hex.len() <= res.unopt.compiled_hex.len());
}

#[test]
fn test_optimizer_shrinks_q_test_2() {
    let program = fs::read_to_string("resources/tests/optimization/validation_taproot.clsp")
        .expect("test file should exist");
    let res = do_compile_and_run_opt_size_test_with_includes(
        &program,
        indoc!{"(
           ;; Curried
           (
             0x7faa3253bfddd1e0decb0906b2dc6247bbc4cf608f58345d173adb63e8b47c9f
             0x0303030303030303030303030303030303030303030303030303030303030303 .
             0xeff07522495060c066f66f32acc2a77e3a3e737aca8baea4d1a64ea4cdc13da9
           )
           0xa04d9f57764f54a43e4030befb4d80026e870519aaa66334aef8304f5d0393c2
           0xb521509a3e089e25b66b3e272aa88b19851778eefebbea13e6be63a471ebf12a
           ;; Args
           () 0x78305c9b8b52ec71ebdd6db292fd106dbfdee8c061314658e13bf2436fa66a71 0x9dcf97a184f32623d11a73124ceb99a5709b083721e878a16d78f596718ba7b2 1 (((1 . 0x0000000000000000000000000000000000000000000000000000000000000000) 2 . 0x0101010101010101010101010101010101010101010101010101010101010101) . 0x15966a8a80f66c1eb2547b2dcc42b1fccdb7d6c1c787a888b9fdc19bf72ac58b)
           )"},
        &["resources/tests/bridge-includes".to_string()]
    ).expect("should compile and run");
    assert!(res.opt.compiled_hex.len() <= res.unopt.compiled_hex.len());
}
