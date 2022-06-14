extern crate clvmr as clvm_rs;

use std::collections::HashMap;
use std::env;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
use clvm_tools_rs::compiler::comptypes::CompileErr;
use clvm_tools_rs::compiler::evaluate::Evaluator;
use clvm_tools_rs::compiler::frontend::frontend;
use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

fn main() {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("give a chialisp program to minify");
        return;
    }

    let loc = Srcloc::start(&"*program*".to_string());
    let _ = parse_sexp(loc.clone(), &args[1])
        .map_err(|e| {
            return CompileErr(e.0.clone(), e.1.clone());
        })
        .and_then(|parsed_program| {
            return frontend(opts.clone(), parsed_program);
        })
        .and_then(|program| {
            let e = Evaluator::new(opts.clone(), runner.clone(), program.helpers.clone());
            return e.shrink_bodyform(
                &mut allocator,
                program.args.clone(),
                &HashMap::new(),
                program.exp.clone(),
                false,
            );
        })
        .map(|result| {
            println!("shrunk: {}", result.to_sexp().to_string());
        })
        .map_err(|e| {
            println!("failed: {:?}", e);
        });
}
