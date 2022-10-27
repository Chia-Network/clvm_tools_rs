use std::collections::HashMap;
use std::collections::HashSet;

use std::env;
use std::mem::swap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts};
use crate::compiler::evaluate::Evaluator;
use crate::compiler::frontend::{compile_helperform, frontend};
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

pub struct Repl {
    depth: i32,
    input_exp: String,

    opts: Rc<dyn CompilerOpts>,
    evaluator: Evaluator,

    loc: Srcloc,
}

fn program_with_helper(names: Vec<Rc<SExp>>, parsed_program: Rc<SExp>) -> Rc<SExp> {
    let mut body = Rc::new(SExp::Nil(parsed_program.loc()));

    for n in names.iter() {
        body = Rc::new(SExp::Cons(parsed_program.loc(), n.clone(), body));
    }

    body = Rc::new(SExp::Cons(
        parsed_program.loc(),
        Rc::new(SExp::atom_from_string(parsed_program.loc(), "x")),
        body,
    ));

    Rc::new(SExp::Cons(
        parsed_program.loc(),
        Rc::new(SExp::atom_from_string(parsed_program.loc(), "mod")),
        Rc::new(SExp::Cons(
            parsed_program.loc(),
            Rc::new(SExp::Nil(parsed_program.loc())),
            Rc::new(SExp::Cons(
                parsed_program.loc(),
                parsed_program.clone(),
                Rc::new(SExp::Cons(
                    parsed_program.loc(),
                    body,
                    Rc::new(SExp::Nil(parsed_program.loc())),
                )),
            )),
        )),
    ))
}

fn count_depth(s: &str) -> i32 {
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

impl Repl {
    pub fn new(opts: Rc<dyn CompilerOpts>, runner: Rc<dyn TRunProgram>) -> Repl {
        let loc = Srcloc::start(&opts.filename());
        let mut toplevel_forms = HashSet::new();

        for w in vec![
            "defun",
            "defun-inline",
            "defconstant",
            "defmacro",
            "deftype",
        ]
        .iter()
        {
            toplevel_forms.insert(w.to_string());
        }

        // Setup the stdenv
        let starter_empty_program = program_with_helper(
            vec![
                Rc::new(SExp::atom_from_string(loc.clone(), "if")),
                Rc::new(SExp::atom_from_string(loc.clone(), "list")),
                Rc::new(SExp::atom_from_string(loc.clone(), "c*")),
                Rc::new(SExp::atom_from_string(loc.clone(), "a*")),
                Rc::new(SExp::atom_from_string(loc.clone(), "coerce")),
                Rc::new(SExp::atom_from_string(loc.clone(), "explode")),
                Rc::new(SExp::atom_from_string(loc.clone(), "bless")),
                Rc::new(SExp::atom_from_string(loc.clone(), "lift")),
                Rc::new(SExp::atom_from_string(loc.clone(), "unlift")),
            ],
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::atom_from_string(loc.clone(), "defconstant")),
                Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), "$interpreter-version")),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::atom_from_string(
                            loc.clone(),
                            env!("CARGO_PKG_VERSION"),
                        )),
                        Rc::new(SExp::Nil(loc.clone())),
                    )),
                )),
            )),
        );
        let start_program_fe = frontend(opts.clone(), vec![starter_empty_program]).unwrap();
        let evaluator = Evaluator::new(opts.clone(), runner.clone(), start_program_fe.helpers);

        Repl {
            depth: 0,
            input_exp: "".to_string(),
            evaluator,
            opts,
            loc,
        }
    }

    pub fn process_line(
        &mut self,
        allocator: &mut Allocator,
        line: String,
    ) -> Result<Option<Rc<BodyForm>>, CompileErr> {
        self.depth += count_depth(&line);

        let mut input_taken = String::new();
        swap(&mut input_taken, &mut self.input_exp);
        let input_taken = input_taken + "\n" + &line;

        if self.depth < 0 {
            let loc = self.loc.clone();
            let result = parse_sexp(loc, input_taken.bytes())
                .map(|_v| {
                    panic!("too many parens but parsed anyway");
                })
                .map_err(|e| CompileErr(e.0.clone(), e.1));
            self.input_exp = "".to_string();
            self.depth = 0;
            return result;
        }

        if self.depth > 0 {
            self.input_exp = input_taken;
            return Ok(None);
        }

        self.input_exp = "".to_string();

        parse_sexp(self.loc.clone(), input_taken.bytes())
            .map_err(|e| CompileErr(e.0.clone(), e.1))
            .and_then(|parsed_program| {
                if parsed_program.is_empty() {
                    return Ok(None);
                }
                if let Some(hresult) =
                    compile_helperform(self.opts.clone(), parsed_program[0].clone())?
                {
                    for h in hresult.new_helpers.iter() {
                        self.evaluator.add_helper(h);
                    }
                    Ok(Some(Rc::new(BodyForm::Quoted(SExp::Nil(self.loc.clone())))))
                } else {
                    frontend(self.opts.clone(), parsed_program)
                        .and_then(|program| {
                            self.evaluator.shrink_bodyform(
                                allocator,
                                program.args.clone(),
                                &HashMap::new(),
                                program.exp,
                                false,
                            )
                        })
                        .map(Some)
                }
            })
    }
}
