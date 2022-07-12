extern crate clvmr as clvm_rs;

use std::env;

use clvm_tools_rs::compiler::comptypes::CompileErr;
use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::typecheck::{
    TheoryToSExp,
    parse_expr_sexp,
    standard_type_context
};
use clvm_tools_rs::compiler::types::theory::TypeTheory;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("give type theory expressions");
        return;
    }

    env_logger::init();

    let loc = Srcloc::start(&"*program*".to_string());
    let _ = parse_sexp(loc.clone(), &args[1])
        .map_err(|e| {
            return CompileErr(e.0.clone(), e.1.clone());
        })
        .and_then(|parsed_program| {
            parse_expr_sexp(parsed_program[0].clone())
        })
        .and_then(|result| {
            println!("parsed: {}", result.to_sexp().to_string());
            standard_type_context().typesynth(&result)
        })
        .map(|(ty, ctx)| {
            println!("typed: {}", ctx.reify(&ty).to_sexp().to_string());
            println!("context: {}", ctx.to_sexp().to_string());
        })
        .map_err(|e| {
            println!("failed: {:?}", e);
        });
}
