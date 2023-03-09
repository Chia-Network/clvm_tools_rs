extern crate clvmr as clvm_rs;

use ::serde_json;
//use std::collections::HashMap;
use std::env;
use std::rc::Rc;

//use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
//use clvm_tools_rs::compiler::evaluate::{Evaluator, EVAL_STACK_LIMIT};
use clvm_tools_rs::compiler::frontend::frontend;
use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

//use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use clvm_tools_rs::util::ErrInto;

fn main() {
    //let mut allocator = Allocator::new();
    //let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new("*program*"));
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Give a chialisp program to convert to json AST");
        return;
    }

    let loc = Srcloc::start("*program*");
    let result = parse_sexp(loc, args[1].bytes())
        .err_into()
        .and_then(|parsed_program| frontend(opts.clone(), &parsed_program));
    match result {
        Ok(program) => match serde_json::to_string(&program) {
            Ok(output) => println!("{}", output),
            Err(e) => {
                println!("{:?}", e);
            }
        },
        Err(e) => {
            println!("{:?}", e);
        }
    }
}
