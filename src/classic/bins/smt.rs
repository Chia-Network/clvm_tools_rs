use std::env;

use clvm_tools_rs::compiler::sexp::parse_sexp;
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::smt::smtlib::SMTSolver;

fn main() {
    let args: Vec<String> = env::args().collect();
    let loc = Srcloc::start("*command*");
    let mut solver = match SMTSolver::new() {
        Ok(s) => s,
        Err(e) => {
            panic!("error starting smt: {:?}", e);
        }
    };

    for a in args.iter().skip(1) {
        match parse_sexp(loc.clone(), &a) {
            Ok(l) => {
                match solver.run_stmt(&l[0]) {
                    Ok(res) => {
                        println!("{}", res);
                    },
                    Err(e) => {
                        println!("error {:?}", e);
                    }
                }
            },
            Err(e) => {
                println!("error {:?}", e);
            }
        }
    }
}
