use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::run;
use crate::compiler::comptypes::{
    Binding,
    BodyForm,
    CompileErr,
    CompileForm,
    CompilerOpts,
    HelperForm,
    LetFormKind
};
use crate::compiler::frontend::frontend;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

// Frontend evaluator based on my fuzzer representation and direct interpreter of
// that.
#[derive(Debug)]
pub enum ArgInputs {
    Whole(Rc<BodyForm>),
    Pair(Rc<ArgInputs>, Rc<ArgInputs>)
}

pub struct Evaluator {
    opts: Rc<CompilerOpts>,
    runner: Rc<dyn TRunProgram>,
    prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    helpers: Vec<HelperForm>,
}

fn select_helper(bindings: &Vec<HelperForm>, name: &Vec<u8>) -> Option<HelperForm> {
    for b in bindings.iter() {
        if b.name() == name {
            return Some(b.clone());
        }
    }

    return None;
}

fn update_parallel_bindings(
    bindings: &HashMap<Vec<u8>, Rc<BodyForm>>, have_bindings: &Vec<Rc<Binding>>
) -> HashMap<Vec<u8>, Rc<BodyForm>> {
    let mut new_bindings = bindings.clone();
    for b in have_bindings.iter() {
        new_bindings.insert(b.name.clone(), b.body.clone());
    }
    new_bindings
}

// Tell whether the bodyform is a simple primitive.
pub fn is_primitive(expr: &BodyForm) -> bool {
    match expr {
        BodyForm::Quoted(x) => true,
        BodyForm::Value(SExp::Nil(_)) => true,
        BodyForm::Value(SExp::Integer(_,_)) => true,
        BodyForm::Value(SExp::QuotedString(_,_,_)) => true,
        _ => false
    }
}

fn make_operator1(l: &Srcloc, op: String, arg: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        l.clone(),
        vec!(
            Rc::new(BodyForm::Value(SExp::atom_from_string(l.clone(), &op))),
            arg.clone()
        )
    )
}

fn make_operator2(l: &Srcloc, op: String, arg1: Rc<BodyForm>, arg2: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        l.clone(),
        vec!(
            Rc::new(BodyForm::Value(SExp::atom_from_string(l.clone(), &op))),
            arg1.clone(),
            arg2.clone()
        )
    )
}

// For any arginput, give a bodyform that computes it.  In most cases, the
// bodyform is extracted, in a few cases, we may need to form a cons operation.
fn get_bodyform_from_arginput(l: &Srcloc, arginput: &ArgInputs) -> Rc<BodyForm> {
    match arginput {
        ArgInputs::Whole(bf) => bf.clone(),
        ArgInputs::Pair(a,b) => {
            let a_borrowed: &ArgInputs = a.borrow();
            let b_borrowed: &ArgInputs = b.borrow();
            let bfa = get_bodyform_from_arginput(l, a);
            let bfb = get_bodyform_from_arginput(l, b);
            Rc::new(make_operator2(
                l,
                "c".to_string(),
                bfa.clone(),
                bfb.clone()
            ))
        }
    }
}

// Given an SExp argument capture structure and SExp containing the arguments
// constructed for the function, populate a HashMap with minimized expressions
// which match the requested argument destructuring.
//
// It's possible this will result in irreducible (unknown at compile time)
// argument expressions.
fn create_argument_captures(
    argument_captures: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
    formed_arguments: &ArgInputs,
    function_arg_spec: Rc<SExp>
) -> Result<(), CompileErr> {
    match (formed_arguments, function_arg_spec.borrow()) {
        (_, SExp::Nil(l)) => {
            Ok(())
        },
        (ArgInputs::Whole(bf), SExp::Cons(l,f,r)) => {
            match bf.borrow() {
                BodyForm::Quoted(SExp::Cons(la,fa,ra)) => {
                    // Argument destructuring splits a quoted sexp that can itself
                    // be destructured.
                    let fa_borrowed: &SExp = fa.borrow();
                    let ra_borrowed: &SExp = ra.borrow();
                    let f_borrowed: &SExp = f.borrow();
                    let r_borrowed: &SExp = r.borrow();
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(BodyForm::Quoted(fa_borrowed.clone()))),
                        f.clone()
                    )?;
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(BodyForm::Quoted(ra_borrowed.clone()))),
                        r.clone()
                    )
                },
                bf => {
                    // Argument destructuring splits a value that couldn't
                    // previously be reduced.  We'll punt it back unreduced by
                    // specifying how the right part is reached.
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(
                            Rc::new(make_operator1(
                                l,
                                "f".to_string(),
                                Rc::new(bf.clone())
                            ))
                        ),
                        f.clone()
                    )?;
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(
                            Rc::new(make_operator1(
                                l,
                                "r".to_string(),
                                Rc::new(bf.clone())
                            ))
                        ),
                        r.clone()
                    )
                }
            }
        },
        (ArgInputs::Pair(af,ar), SExp::Cons(l,f,r)) => {
            let af_body = get_bodyform_from_arginput(l, af);
            let ar_body = get_bodyform_from_arginput(l, ar);

            create_argument_captures(
                argument_captures,
                af,
                f.clone()
            )?;
            create_argument_captures(
                argument_captures,
                ar,
                r.clone()
            )
        },
        (ArgInputs::Whole(x), SExp::Atom(l,name)) => {
            argument_captures.insert(name.clone(), x.clone());
            Ok(())
        },
        (ArgInputs::Pair(af,ar), SExp::Atom(l,name)) => {
            argument_captures.insert(name.clone(), get_bodyform_from_arginput(l, formed_arguments));
            Ok(())
        },
        (_, _) => Err(CompileErr(function_arg_spec.loc(), format!("not yet supported argument alternative: ArgInput {:?} SExp {}", formed_arguments, function_arg_spec.to_string())))
    }
}

fn arg_inputs_primitive(arginputs: Rc<ArgInputs>) -> bool {
    match arginputs.borrow() {
        ArgInputs::Whole(bf) => is_primitive(bf),
        ArgInputs::Pair(a,b) => {
            arg_inputs_primitive(a.clone()) && arg_inputs_primitive(b.clone())
        }
    }
}

fn build_argument_captures(l: &Srcloc, arguments_to_convert: &Vec<Rc<BodyForm>>, args: Rc<SExp>) -> Result<HashMap<Vec<u8>, Rc<BodyForm>>, CompileErr> {
    let mut formed_arguments =
        ArgInputs::Whole(Rc::new(BodyForm::Quoted(SExp::Nil(l.clone()))));

    for i_reverse in 0..arguments_to_convert.len() {
        let i = arguments_to_convert.len() - i_reverse - 1;
        formed_arguments = ArgInputs::Pair(
            Rc::new(ArgInputs::Whole(arguments_to_convert[i].clone())),
            Rc::new(formed_arguments)
        );
    }

    let mut argument_captures = HashMap::new();
    create_argument_captures(
        &mut argument_captures,
        &formed_arguments,
        args.clone()
    )?;
    Ok(argument_captures)
}

fn make_prim_call(l: Srcloc, prim: Rc<SExp>, args: Rc<SExp>) -> Rc<SExp> {
    Rc::new(SExp::Cons(
        l.clone(),
        prim,
        args
    ))
}

pub fn build_reflex_captures(captures: &mut HashMap<Vec<u8>, Rc<BodyForm>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Atom(l, name) => {
            captures.insert(name.clone(), Rc::new(BodyForm::Value(SExp::Atom(l.clone(), name.clone()))));
        },
        SExp::Cons(_, a, b) => {
            build_reflex_captures(captures, a.clone());
            build_reflex_captures(captures, b.clone());
        },
        _ => { }
    }
}

fn dequote(l: Srcloc, exp: Rc<BodyForm>) -> Result<Rc<SExp>, CompileErr> {
    match exp.borrow() {
        BodyForm::Quoted(v) => Ok(Rc::new(v.clone())),
        _ => Err(CompileErr(l, format!("not a quoted result in macro expansion: {} {:?}", exp.to_sexp().to_string(), exp)))
    }
}

fn run_prim(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    call_loc: Srcloc,
    name: Vec<u8>,
    prim: Rc<SExp>,
    args: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    run(
        allocator,
        runner,
        prims,
        prim,
        args
    )
}

fn show_env(env: &HashMap<Vec<u8>, Rc<BodyForm>>) {
    let loc = Srcloc::start(&"*env*".to_string());
    for kv in env.iter() {
        println!(" - {}: {}", SExp::Atom(loc.clone(), kv.0.clone()).to_string(), kv.1.to_sexp().to_string());
    }
}

impl Evaluator {
    pub fn new(
        opts: Rc<CompilerOpts>,
        runner: Rc<dyn TRunProgram>,
        prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
        helpers: Vec<HelperForm>,
    ) -> Self {
        Evaluator {
            opts: opts,
            runner: runner,
            prims: prims,
            helpers: helpers,
        }
    }

    // A frontend language evaluator and minifier
    pub fn shrink_bodyform(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        match body.borrow() {
            BodyForm::Let(l, LetFormKind::Parallel, bindings, body) => {
                let updated_bindings = update_parallel_bindings(env, bindings);
                self.shrink_bodyform(
                    allocator,
                    prog_args.clone(),
                    &updated_bindings,
                    body.clone()
                )
            },
            BodyForm::Let(l, LetFormKind::Sequential, bindings, body) => {
                if bindings.len() == 0 {
                    self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        env,
                        body.clone()
                    )
                } else {
                    let first_binding_as_list: Vec<Rc<Binding>> =
                        bindings.iter().take(1).map(|x| x.clone()).collect();
                    let rest_of_bindings: Vec<Rc<Binding>> =
                        bindings.iter().skip(1).map(|x| x.clone()).collect();

                    let updated_bindings = update_parallel_bindings(
                        env,
                        &first_binding_as_list
                    );
                    self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        &updated_bindings,
                        Rc::new(BodyForm::Let(
                            l.clone(),
                            LetFormKind::Sequential,
                            rest_of_bindings,
                            body.clone()
                        ))
                    )
                }
            },
            BodyForm::Quoted(sexp) => Ok(body.clone()),
            BodyForm::Value(SExp::Atom(l,name)) => {
                if name == &"@".as_bytes().to_vec() {
                    Ok(Rc::new(BodyForm::Quoted(SExp::Nil(l.clone()))))
                    // XXX Err(CompileErr(l.clone(), format!("can't yet paste whole environment")))
                } else {
                    env.get(name).map(|x| {
                        self.shrink_bodyform(
                            allocator,
                            prog_args.clone(),
                            env,
                            x.clone()
                        )
                    }).unwrap_or_else(|| {
                        Ok(Rc::new(BodyForm::Value(SExp::Atom(l.clone(),name.clone()))))
                    })
                }
            },
            BodyForm::Value(v) => Ok(Rc::new(BodyForm::Quoted(v.clone()))),
            BodyForm::Call(l, parts) => {
                if parts.len() == 0 {
                    return Err(CompileErr(l.clone(), format!("Impossible empty call list")));
                }

                let head_expr = parts[0].clone();
                let mut arguments_to_convert: Vec<Rc<BodyForm>> =
                    parts.iter().skip(1).map(|x| x.clone()).collect();

                match head_expr.borrow() {
                    BodyForm::Value(SExp::Atom(call_loc, call_name)) => {
                        let helper = select_helper(&self.helpers, call_name);
                        match helper {
                            Some(HelperForm::Defconstant(l, _, _)) => {
                                Err(CompileErr(
                                    call_loc.clone(),
                                    format!("Can't call constant {}", head_expr.to_sexp().to_string())
                                ))
                            },
                            Some(HelperForm::Defmacro(l, name, args, program)) => {
                                println!("processing call {}\nhelpers", body.to_sexp().to_string());
                                for h in self.helpers.iter() {
                                    println!(" - {}", h.to_sexp().to_string());
                                }

                                println!("env");
                                show_env(env);

                                // Pass the SExp representation of the expressions into
                                // the macro after forming an argument sexp and then
                                for i in 0..arguments_to_convert.len() {
                                    let arg_repr = arguments_to_convert[i].to_sexp();
                                    let borrowed_arg: &SExp =
                                        arg_repr.borrow();
                                    arguments_to_convert[i] =
                                        Rc::new(BodyForm::Quoted(borrowed_arg.clone()));
                                }

                                let argument_captures =
                                    build_argument_captures(
                                        call_loc,
                                        &arguments_to_convert,
                                        program.args.clone()
                                    )?;

                                let macro_expansion =
                                    self.expand_macro(
                                        allocator,
                                        args.clone(),
                                        &argument_captures,
                                        program.clone()
                                    )?;

                                let input_sexp = dequote(call_loc.clone(), macro_expansion)?;
                                println!("dequoted macro output: {}", input_sexp.to_string());
                                frontend(self.opts.clone(), vec!(input_sexp)).and_then(|program| {
                                    println!("frontend read of macro: {}", program.to_sexp().to_string());
                                    self.shrink_bodyform(
                                        allocator,
                                        prog_args.clone(),
                                        &argument_captures,
                                        program.exp.clone()
                                    )
                                })
                            },
                            Some(HelperForm::Defun(l, name, inline, args, body)) => {
                                let mut argument_captures_untranslated =
                                    build_argument_captures(
                                        call_loc,
                                        &arguments_to_convert, args.clone()
                                    )?;

                                let mut argument_captures = HashMap::new();
                                // Do this to protect against misalignment
                                // between argument vec and destructuring.
                                for kv in argument_captures_untranslated.iter() {
                                    let shrunk = self.shrink_bodyform(
                                        allocator,
                                        prog_args.clone(),
                                        env,
                                        kv.1.clone()
                                    )?;

                                    argument_captures.insert(
                                        kv.0.clone(),
                                        shrunk.clone()
                                    );
                                }

                                self.shrink_bodyform(
                                    allocator,
                                    args.clone(),
                                    &argument_captures,
                                    body
                                )
                            },
                            None => {
                                let mut all_primitive = true;
                                let mut target_vec: Vec<Rc<BodyForm>> =
                                    parts.clone();

                                if call_name == &"@".as_bytes().to_vec() {
                                    return Err(CompileErr(call_loc.clone(), format!("can't yet simulate environment paths")));
                                } else if call_name == &"com".as_bytes().to_vec() {
                                    // Com takes place in the current environment.
                                    // We can only reduce com if all bindings are
                                    // primitive.
                                    println!("com {}", body.to_sexp().to_string());
                                    let updated_opts = self.opts
                                        .set_stdenv(false)
                                        .set_in_defun(true);

                                    let mut end_of_list = Rc::new(SExp::Cons(
                                        l.clone(),
                                        arguments_to_convert[0].to_sexp(),
                                        Rc::new(SExp::Nil(l.clone())),
                                    ));

                                    for h in self.helpers.iter() {
                                        end_of_list = Rc::new(SExp::Cons(
                                            l.clone(),
                                            h.to_sexp(),
                                            end_of_list
                                        ))
                                    }

                                    let use_body = SExp::Cons(
                                        l.clone(),
                                        Rc::new(SExp::Atom(
                                            l.clone(), "mod".as_bytes().to_vec()
                                        )),
                                        Rc::new(SExp::Cons(
                                            l.clone(),
                                            prog_args.clone(),
                                            end_of_list
                                        )),
                                    );

                                    println!("compile program {}", use_body.to_string());
                                    let com_result = updated_opts
                                        .compile_program(
                                            allocator,
                                            self.runner.clone(),
                                            Rc::new(use_body)
                                        ).map(|code| {
                                            Rc::new(BodyForm::Quoted(code))
                                        })?;

                                    println!("com_result = {}", com_result.to_sexp().to_string());
                                    Ok(com_result)
                                } else {
                                    let pres = self.prims.get(call_name).map(|prim| {
                                        println!("run primitive {}\nenv", body.to_sexp().to_string());
                                        show_env(env);
                                        // Reduce all arguments.
                                        let mut converted_args =
                                            SExp::Nil(call_loc.clone());

                                        for i_reverse in 0..arguments_to_convert.len() {
                                            let i =
                                                arguments_to_convert.len() - i_reverse - 1;
                                            let shrunk = self.shrink_bodyform(
                                                allocator,
                                                prog_args.clone(),
                                                env,
                                                arguments_to_convert[i].clone()
                                            )?;

                                            target_vec[i+1] = shrunk.clone();

                                            if !arg_inputs_primitive(Rc::new(ArgInputs::Whole(shrunk.clone()))) {
                                                all_primitive = false;
                                            }

                                            converted_args = SExp::Cons(
                                                call_loc.clone(),
                                                shrunk.to_sexp(),
                                                Rc::new(converted_args)
                                            );
                                        }

                                        let reformed = BodyForm::Call(
                                            call_loc.clone(),
                                            target_vec.clone()
                                        );
                                        println!("all primitive: {} -> {}", reformed.to_sexp().to_string(), all_primitive);

                                        if all_primitive {
                                            run_prim(
                                                allocator,
                                                self.runner.clone(),
                                                self.prims.clone(),
                                                call_loc.clone(),
                                                call_name.clone(),
                                                make_prim_call(
                                                    call_loc.clone(),
                                                    prim.clone(),
                                                    Rc::new(converted_args)
                                                ),
                                                Rc::new(SExp::Nil(call_loc.clone()))
                                            ).map_err(|e| {
                                                match e {
                                                    RunFailure::RunExn(l, s) => {
                                                        CompileErr(call_loc.clone(), format!("exception: {}", s.to_string()))
                                                    },
                                                    RunFailure::RunErr(l, s) => {
                                                        CompileErr(call_loc.clone(), s.clone())
                                                    }
                                                }
                                            }).map(|res| {
                                                let res_borrowed: &SExp = res.borrow();
                                                Rc::new(BodyForm::Quoted(res_borrowed.clone()))
                                            })
                                        } else {
                                            Ok(Rc::new(reformed))
                                        }
                                    }).unwrap_or_else(|| {
                                        // Build SExp arguments for external call or
                                        // return the unevaluated chunk with minimized
                                        // arguments.
                                        Err(CompileErr(
                                            call_loc.clone(),
                                            format!("Don't yet support this call type {} {:?}", body.to_sexp().to_string(), body)
                                        ))
                                    })?;
                                    println!("do prim {} => {}", body.to_sexp().to_string(), pres.to_sexp().to_string());
                                    Ok(pres)
                                }
                            }
                        }
                    },
                    _ => {
                        Err(CompileErr(
                            l.clone(),
                            format!(
                                "Don't know how to call {}",
                                head_expr.to_sexp().to_string()
                            )
                        ))
                    }
                }
            }
        }
    }

    fn expand_macro(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        program: Rc<CompileForm>
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let loc = Srcloc::start(&"*xxx".to_string());
        let mut new_helpers = Vec::new();
        let mut used_names = HashSet::new();

        for h in program.helpers.iter() {
            used_names.insert(h.name());
            new_helpers.push(h.clone());
        }
        for h in self.helpers.iter() {
            if !used_names.contains(h.name()) {
                new_helpers.push(h.clone());
            }
        }
        let e = Evaluator::new(
            self.opts.clone(),
            self.runner.clone(),
            self.prims.clone(),
            new_helpers,
        );
        e.shrink_bodyform(
            allocator,
            prog_args,
            env,
            program.exp.clone()
        )
    }

}
