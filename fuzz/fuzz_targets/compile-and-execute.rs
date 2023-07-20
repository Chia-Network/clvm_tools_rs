#![no_main]

use rand::prelude::*;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use lazy_static::lazy_static;
use libfuzzer_sys::fuzz_target;
use log::debug;

use clvmr::allocator::Allocator;

use clvm_tools_rs::classic::clvm_tools::binutils::disassemble;
use clvm_tools_rs::classic::clvm_tools::stages::stage_0::TRunProgram;
use clvm_tools_rs::compiler::clvm;
use clvm_tools_rs::compiler::compiler::{
    DefaultCompilerOpts,
    compile_file,
};
use clvm_tools_rs::compiler::comptypes::{CompileErr, CompilerOpts};
use clvm_tools_rs::compiler::dialect::AcceptedDialect;
use clvm_tools_rs::compiler::fuzzer::{FuzzOldProgram, FuzzProgram};
use clvm_tools_rs::compiler::runtypes::RunFailure;
use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::fuzzing::fuzzrng::FuzzPseudoRng;
use clvm_tools_rs::classic::clvm_tools::clvmc::compile_clvm_text;
use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use clvm_tools_rs::compiler::prims;

pub fn run_failure_to_compile_err(e: RunFailure) -> CompileErr {
    match e {
        RunFailure::RunErr(l, e) => CompileErr(l, e),
        RunFailure::RunExn(s, e) => CompileErr(s, format!("exception {}\n", e)),
    }
}

lazy_static! {
    pub static ref LOG_INITIALIZED: &'static str = {
        env_logger::init();
        "log initialized"
    };
}

fuzz_target!(|data: &[u8]| {
    let _ = LOG_INITIALIZED;
    let mut rng = FuzzPseudoRng::new(data);
    let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(&"*prog*".to_string()))
        .set_optimize(true)
        .set_dialect(AcceptedDialect {
            stepping: Some(23),
            strict: true,
        });
    let runner = Rc::new(DefaultProgramRunner::new());
    let prim_map = prims::prim_map();
    let mut old = false;

    // Sickos: hahaha YES
    let mut allocator = Allocator::new();

    old = !old;

    let prog: FuzzProgram =
        if old {
            let old_program: FuzzOldProgram = rng.gen();
            old_program.program
        } else {
            rng.gen()
        };

    debug!("prog: {}", prog.to_sexp().to_string());

    let args = prog.random_args(&mut rng);
    debug!("args: {}", args.to_string());

    let interpret_result = prog.interpret(args.clone());

    match &interpret_result {
        Ok(res) => {
            debug!("interpreted: {}", res);
        }
        Err(e) => {
            debug!("interpreted: {}", e);
        }
    }

    let run_result = compile_file(
        &mut allocator,
        runner.clone(),
        opts.clone(),
        &prog.to_sexp().to_string(),
        &mut HashMap::new()
    ).and_then(|compiled| {
        debug!("running: {}", compiled);
        clvm::run(
            &mut allocator,
            runner.clone(),
            prim_map.clone(),
            Rc::new(compiled),
            Rc::new(args.clone()),
            None,
            None,
        ).map_err(run_failure_to_compile_err)
    });

    match &run_result {
        Ok(res) => {
            debug!("compiled-run: {}", res);
        }
        Err(e) => {
            debug!("compiled-run: {}: {}", e.0, e.1);
        }
    }

    let prog_sexp = prog.to_sexp();
    let prog_loc = prog_sexp.loc();
    let old_result: Option<Result<Rc<SExp>, CompileErr>> =
        if old {
            let compiled = compile_clvm_text(
                &mut allocator,
                opts.clone(),
                &mut HashMap::new(),
                &prog_sexp.to_string(),
                "*old-test*",
                true,
            ).map_err(|e| {
                CompileErr(prog_loc.clone(), e.1.clone())
            });

            let new_program = compiled.clone().and_then(|runnable| {
                clvm::convert_from_clvm_rs(
                    &mut allocator, prog_loc.clone(), runnable
                ).map_err(run_failure_to_compile_err)
            });

            let new_run = new_program.clone().and_then(|new_program| {
                clvm::run(
                    &mut allocator,
                    runner.clone(),
                    prim_map.clone(),
                    new_program,
                    Rc::new(args.clone()),
                    None,
                    None,
                ).map_err(run_failure_to_compile_err)
            });

            let old_args = clvm::convert_to_clvm_rs(
                &mut allocator, Rc::new(args.clone())
            ).expect("should convert args (old)");

            let old_run = compiled.and_then(|runnable| {
                runner.run_program(
                    &mut allocator,
                    runnable,
                    old_args,
                    None
                ).map_err(|e| CompileErr(prog_loc.clone(), e.1.clone()))
            });

            if old_run.is_err() != new_run.is_err() {
                panic!("old and new run disagree on error");
            }

            if let (Ok(old), Ok(new)) = (&old_run, &new_run) {
                debug!("old-run: {}", disassemble(&mut allocator, old.1));
                let new_version_of_old_run_output =
                    clvm::convert_from_clvm_rs(
                        &mut allocator,
                        prog_loc.clone(),
                        old.1
                    ).expect("should convert old run output");
                if new_version_of_old_run_output != *new {
                    panic!("old and new run values disagree {}", prog_sexp);
                }

                let modern_to_old = clvm::convert_to_clvm_rs(
                    &mut allocator,
                    new.clone()
                ).expect("should convert new to old");

                if disassemble(&mut allocator, old.1) != disassemble(&mut allocator, modern_to_old) {
                    panic!("results disagree on old conversion of value");
                }
            }

            Some(new_run)
        } else {
            None
        };

    // XXX enable panic on interpreter differences.
    // if interpret_result.is_err() != run_result.is_err() {
    //     panic!("error results disagree on error in {}", prog_sexp);
    // }

    // If we generated an old result, check here.
    if old_result.as_ref().map(|or| {
        interpret_result.is_err() != or.is_err()
    }).unwrap_or(false) {
        panic!("old run and new run disagree on error in {}", prog_sexp);
    }

    if let (Ok(interp), Ok(compiled)) = (interpret_result, run_result) {
        let compiled_borrowed: &SExp = compiled.borrow();
        if &interp != compiled_borrowed {
            panic!("results disagree on value");
        }
    }
});
