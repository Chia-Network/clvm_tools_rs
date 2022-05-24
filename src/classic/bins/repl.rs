use std::io::{self, BufRead, Write};

use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
use clvm_tools_rs::compiler::repl::Repl;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

fn main() {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    let stdin = io::stdin();
    let mut repl = Repl::new(opts.clone(), runner.clone());

    print!(">>> ");
    io::stdout().flush().unwrap();

    for l in stdin.lock().lines() {
        match l {
            Err(_) => break,
            Ok(line) => {
                let _ = repl
                    .process_line(&mut allocator, line)
                    .map(|result| {
                        if let Some(result) = result {
                            print!("{}\n>>> ", result.to_sexp().to_string());
                        } else {
                            print!("... ");
                        }
                    })
                    .map_err(|e| {
                        print!("failed: {:?}\n>>> ", e);
                    });
            }
        }
        io::stdout().flush().unwrap();
    }
}
