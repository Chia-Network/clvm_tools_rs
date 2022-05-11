use std::io::{self, BufRead, Write};

use std::collections::HashMap;
use std::collections::HashSet;

use std::env;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::comptypes::{CompilerOpts, CompileErr, BodyForm};
use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
use clvm_tools_rs::compiler::evaluate::{
    Evaluator,
    first_of_alist,
    second_of_alist
};
use clvm_tools_rs::compiler::frontend::frontend;
use clvm_tools_rs::compiler::prims::prim_map;
use clvm_tools_rs::compiler::sexp::{SExp, parse_sexp};
use clvm_tools_rs::compiler::srcloc::Srcloc;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

fn program_with_helper(
    names: Vec<Rc<SExp>>,
    parsed_program: Rc<SExp>
) -> Rc<SExp> {
    let mut body = Rc::new(SExp::Nil(parsed_program.loc()));

    for n in names.iter() {
        body = Rc::new(SExp::Cons(
            parsed_program.loc(),
            n.clone(),
            body
        ));
    }

    body = Rc::new(SExp::Cons(
        parsed_program.loc(),
        Rc::new(SExp::atom_from_string(parsed_program.loc(), &"x".to_string())),
        body
    ));

    Rc::new(SExp::Cons(
        parsed_program.loc(),
        Rc::new(SExp::atom_from_string(parsed_program.loc(), &"mod".to_string())),
        Rc::new(SExp::Cons(
            parsed_program.loc(),
            Rc::new(SExp::Nil(parsed_program.loc())),
            Rc::new(SExp::Cons(
                parsed_program.loc(),
                parsed_program.clone(),
                Rc::new(SExp::Cons(
                    parsed_program.loc(),
                    body,
                    Rc::new(SExp::Nil(parsed_program.loc()))
                ))
            ))
        ))
    ))
}

fn count_depth(s: &String) -> i32 {
    let mut count: i32 = 0;
    for ch in s.as_bytes().iter() {
        if *ch as char == '(' {
            count += 1;
        } else if *ch as char == ')' {
            count -= 1;
        }
    }
    count
}

fn main() {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let prims = prim_map();
    let opts = Rc::new(DefaultCompilerOpts::new(&"*program*".to_string()));
    let loc = Srcloc::start(&"*program*".to_string());
    let stdin = io::stdin();
    let mut depth: i32 = 0;
    let mut input_exp = "".to_string();

    // Setup the stdenv
    let starter_empty_program = program_with_helper(vec!(
        Rc::new(SExp::atom_from_string(loc.clone(), &"if".to_string())),
        Rc::new(SExp::atom_from_string(loc.clone(), &"list".to_string()))
    ), Rc::new(SExp::Cons(
        loc.clone(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"defconstant".to_string())),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"$interpreter-version".to_string())),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::atom_from_string(loc.clone(), &env!("CARGO_PKG_VERSION").to_string())),
                Rc::new(SExp::Nil(loc.clone()))
            ))
        ))
    )));

    let start_program_fe = frontend(opts.clone(), vec!(starter_empty_program)).unwrap();

    let mut e = Evaluator::new(
        opts.clone(),
        runner.clone(),
        prims.clone(),
        start_program_fe.helpers.clone(),
    );

    let mut toplevel_forms = HashSet::new();
    for w in vec!("defun", "defun-inline", "defconstant", "defmacro").iter() {
        toplevel_forms.insert(w.to_string());
    }

    print!(">>> ");
    io::stdout().flush().unwrap();

    for l in stdin.lock().lines() {
        match l {
            Err(_) => break,
            Ok(line) => {
                depth += count_depth(&line);
                if depth < 0 {
                    input_exp = "".to_string();
                    depth = 0;
                    println!("Too many end parenthesis");
                    continue;
                }

                input_exp = input_exp + &line;
                if depth > 0 {
                    continue;
                }

                let input_taken = input_exp;
                input_exp = "".to_string();

                parse_sexp(loc.clone(), &input_taken).map_err(|e| {
                    return CompileErr(e.0.clone(), e.1.clone());
                }).and_then(|parsed_program| {
                    match first_of_alist(
                        parsed_program[0].clone()
                    ).map(|fa| toplevel_forms.contains(&fa.to_string())) {
                        Ok(true) => {
                            let prog0 = parsed_program[0].clone();
                            let name = second_of_alist(parsed_program[0].clone())?;
                            let built_program = program_with_helper(
                                vec!(name),
                                prog0.clone()
                            );
                            let program = frontend(opts.clone(), vec!(built_program))?;
                            e.add_helper(
                                &program.helpers[program.helpers.len()-1]
                            );
                            Ok(Rc::new(BodyForm::Quoted(SExp::Nil(prog0.loc()))))
                        },
                        _ => {
                            frontend(
                                opts.clone(),
                                parsed_program
                            ).and_then(|program| {
                                let mut captures = HashMap::new();
                                return e.shrink_bodyform(
                                    &mut allocator,
                                    program.args.clone(),
                                    &captures,
                                    program.exp.clone(),
                                    false
                                );
                            })
                        }
                    }
                }).map(|result| {
                    println!("shrunk: {}", result.to_sexp().to_string());
                }).map_err(|e| {
                    println!("failed: {:?}", e);
                });
            }
        }

        if depth > 0 {
            print!("... ");
        } else {
            print!(">>> ");
        }
        io::stdout().flush().unwrap();
    }
}
