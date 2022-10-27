extern crate clvmr as clvm_rs;

use std::env;

use clvm_tools_rs::compiler::comptypes::CompileErr;
use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::typecheck::{parse_expr_sexp, TheoryToSExp};
use clvm_tools_rs::compiler::typechia::standard_type_context;
use clvm_tools_rs::compiler::types::ast::{ContextElim, Var};
use clvm_tools_rs::compiler::types::theory::TypeTheory;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("give type theory expressions");
        return;
    }

    env_logger::init();

    let loc = Srcloc::start("*program*");
    let mut context = standard_type_context();

    let mut takename = true;
    let mut name = "".to_string();
    for arg in args.iter().take(args.len() - 1).skip(1) {
        if takename {
            name = arg.to_string();
        } else {
            match parse_sexp(loc.clone(), arg.bytes())
                .map_err(|e| CompileErr(e.0.clone(), e.1))
                .and_then(|parsed_program| parse_expr_sexp(parsed_program[0].clone()))
                .and_then(|result| context.typesynth(&result))
            {
                Ok((ty, _)) => {
                    context = context.snoc(ContextElim::CVar(Var(name.clone(), loc.clone()), ty));
                }
                Err(e) => {
                    println!("error in helper {}: {:?}", name, e);
                    return;
                }
            }
        }

        takename = !takename;
    }

    println!("starting context {}", context.to_sexp());

    parse_sexp(loc, args[args.len() - 1].bytes())
        .map_err(|e| CompileErr(e.0.clone(), e.1))
        .and_then(|parsed_program| parse_expr_sexp(parsed_program[0].clone()))
        .and_then(|result| {
            println!("parsed: {}", result.to_sexp());
            context.typesynth(&result)
        })
        .map(|(ty, ctx)| {
            println!("typed: {}", ctx.reify(&ty, None).to_sexp());
            println!("context: {}", ctx.to_sexp());
        })
        .map_err(|e| {
            println!("failed: {:?}", e);
        })
        .ok();
}
