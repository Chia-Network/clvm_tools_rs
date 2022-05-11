use std::collections::HashMap;
use std::env;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::comptypes::{CompilerOpts, CompileErr};
use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
use clvm_tools_rs::compiler::evaluate::{
    Evaluator,
    build_reflex_captures
};
use clvm_tools_rs::compiler::frontend::frontend;
use clvm_tools_rs::compiler::prims::prim_map;
use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

fn main() {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let prims = prim_map();
    let opts = Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("give a chialisp program to minify");
        return;
    }

    let loc = Srcloc::start(&"*program*".to_string());
    parse_sexp(loc.clone(), &args[1]).map_err(|e| {
        return CompileErr(e.0.clone(), e.1.clone());
    }).and_then(|parsed_program| {
        return frontend(opts.clone(), parsed_program);
    }).and_then(|program| {
        let mut captures = HashMap::new();
        let e = Evaluator::new(
            opts.clone(),
            runner.clone(),
            prims.clone(),
            program.helpers.clone(),
        );
        return e.shrink_bodyform(
            &mut allocator,
            program.args.clone(),
            &captures,
            program.exp.clone(),
            false
        );
    }).map(|result| {
        println!("shrunk: {}", result.to_sexp().to_string());
    }).map_err(|e| {
        println!("failed: {:?}", e);
    });
}
