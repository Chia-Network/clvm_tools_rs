use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::run;
use crate::compiler::comptypes::{
    Binding, BodyForm, CompileErr, CompileForm, CompilerOpts, HelperForm, LetFormKind,
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
    Pair(Rc<ArgInputs>, Rc<ArgInputs>),
}

pub struct Evaluator {
    opts: Rc<dyn CompilerOpts>,
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
    bindings: &HashMap<Vec<u8>, Rc<BodyForm>>,
    have_bindings: &Vec<Rc<Binding>>,
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
        BodyForm::Quoted(_) => true,
        BodyForm::Value(SExp::Nil(_)) => true,
        BodyForm::Value(SExp::Integer(_, _)) => true,
        BodyForm::Value(SExp::QuotedString(_, _, _)) => true,
        _ => false,
    }
}

fn make_operator1(l: &Srcloc, op: String, arg: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        l.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::atom_from_string(l.clone(), &op))),
            arg.clone(),
        ],
    )
}

fn make_operator2(l: &Srcloc, op: String, arg1: Rc<BodyForm>, arg2: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        l.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::atom_from_string(l.clone(), &op))),
            arg1.clone(),
            arg2.clone(),
        ],
    )
}

// For any arginput, give a bodyform that computes it.  In most cases, the
// bodyform is extracted, in a few cases, we may need to form a cons operation.
fn get_bodyform_from_arginput(l: &Srcloc, arginput: &ArgInputs) -> Rc<BodyForm> {
    match arginput {
        ArgInputs::Whole(bf) => bf.clone(),
        ArgInputs::Pair(a, b) => {
            let bfa = get_bodyform_from_arginput(l, a);
            let bfb = get_bodyform_from_arginput(l, b);
            Rc::new(make_operator2(l, "c".to_string(), bfa.clone(), bfb.clone()))
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
    function_arg_spec: Rc<SExp>,
) -> Result<(), CompileErr> {
    match (formed_arguments, function_arg_spec.borrow()) {
        (_, SExp::Nil(_)) => Ok(()),
        (ArgInputs::Whole(bf), SExp::Cons(l, f, r)) => {
            match bf.borrow() {
                BodyForm::Quoted(SExp::Cons(_, fa, ra)) => {
                    // Argument destructuring splits a quoted sexp that can itself
                    // be destructured.
                    let fa_borrowed: &SExp = fa.borrow();
                    let ra_borrowed: &SExp = ra.borrow();
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(BodyForm::Quoted(fa_borrowed.clone()))),
                        f.clone(),
                    )?;
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(BodyForm::Quoted(ra_borrowed.clone()))),
                        r.clone(),
                    )
                }
                bf => {
                    // Argument destructuring splits a value that couldn't
                    // previously be reduced.  We'll punt it back unreduced by
                    // specifying how the right part is reached.
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(make_operator1(
                            l,
                            "f".to_string(),
                            Rc::new(bf.clone()),
                        ))),
                        f.clone(),
                    )?;
                    create_argument_captures(
                        argument_captures,
                        &ArgInputs::Whole(Rc::new(make_operator1(
                            l,
                            "r".to_string(),
                            Rc::new(bf.clone()),
                        ))),
                        r.clone(),
                    )
                }
            }
        }
        (ArgInputs::Pair(af, ar), SExp::Cons(_, f, r)) => {
            create_argument_captures(argument_captures, af, f.clone())?;
            create_argument_captures(argument_captures, ar, r.clone())
        }
        (ArgInputs::Whole(x), SExp::Atom(_, name)) => {
            argument_captures.insert(name.clone(), x.clone());
            Ok(())
        }
        (ArgInputs::Pair(_, _), SExp::Atom(l, name)) => {
            argument_captures.insert(
                name.clone(),
                get_bodyform_from_arginput(l, formed_arguments),
            );
            Ok(())
        }
        (_, _) => Err(CompileErr(
            function_arg_spec.loc(),
            format!(
                "not yet supported argument alternative: ArgInput {:?} SExp {}",
                formed_arguments,
                function_arg_spec.to_string()
            ),
        )),
    }
}

fn arg_inputs_primitive(arginputs: Rc<ArgInputs>) -> bool {
    match arginputs.borrow() {
        ArgInputs::Whole(bf) => is_primitive(bf),
        ArgInputs::Pair(a, b) => arg_inputs_primitive(a.clone()) && arg_inputs_primitive(b.clone()),
    }
}

fn build_argument_captures(
    l: &Srcloc,
    arguments_to_convert: &Vec<Rc<BodyForm>>,
    args: Rc<SExp>,
) -> Result<HashMap<Vec<u8>, Rc<BodyForm>>, CompileErr> {
    let mut formed_arguments = ArgInputs::Whole(Rc::new(BodyForm::Quoted(SExp::Nil(l.clone()))));

    for i_reverse in 0..arguments_to_convert.len() {
        let i = arguments_to_convert.len() - i_reverse - 1;
        formed_arguments = ArgInputs::Pair(
            Rc::new(ArgInputs::Whole(arguments_to_convert[i].clone())),
            Rc::new(formed_arguments),
        );
    }

    let mut argument_captures = HashMap::new();
    create_argument_captures(&mut argument_captures, &formed_arguments, args.clone())?;
    Ok(argument_captures)
}

fn make_prim_call(l: Srcloc, prim: Rc<SExp>, args: Rc<SExp>) -> Rc<SExp> {
    Rc::new(SExp::Cons(l.clone(), prim, args))
}

pub fn build_reflex_captures(captures: &mut HashMap<Vec<u8>, Rc<BodyForm>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Atom(l, name) => {
            captures.insert(
                name.clone(),
                Rc::new(BodyForm::Value(SExp::Atom(l.clone(), name.clone()))),
            );
        }
        SExp::Cons(_, a, b) => {
            build_reflex_captures(captures, a.clone());
            build_reflex_captures(captures, b.clone());
        }
        _ => {}
    }
}

fn dequote(l: Srcloc, exp: Rc<BodyForm>) -> Result<Rc<SExp>, CompileErr> {
    match exp.borrow() {
        BodyForm::Quoted(v) => Ok(Rc::new(v.clone())),
        _ => Err(CompileErr(
            l,
            format!(
                "not a quoted result in macro expansion: {} {:?}",
                exp.to_sexp().to_string(),
                exp
            ),
        )),
    }
}

fn show_env(env: &HashMap<Vec<u8>, Rc<BodyForm>>) {
    let loc = Srcloc::start(&"*env*".to_string());
    for kv in env.iter() {
        println!(
            " - {}: {}",
            SExp::Atom(loc.clone(), kv.0.clone()).to_string(),
            kv.1.to_sexp().to_string()
        );
    }
}

pub fn first_of_alist(lst: Rc<SExp>) -> Result<Rc<SExp>, CompileErr> {
    match lst.borrow() {
        SExp::Cons(_, f, _) => Ok(f.clone()),
        _ => Err(CompileErr(
            lst.loc(),
            format!("No first element of {}", lst.to_string()),
        )),
    }
}

pub fn second_of_alist(lst: Rc<SExp>) -> Result<Rc<SExp>, CompileErr> {
    match lst.borrow() {
        SExp::Cons(_, _, r) => first_of_alist(r.clone()),
        _ => Err(CompileErr(
            lst.loc(),
            format!("No second element of {}", lst.to_string()),
        )),
    }
}

fn third_of_alist(lst: Rc<SExp>) -> Result<Rc<SExp>, CompileErr> {
    match lst.borrow() {
        SExp::Cons(_, _, r) => second_of_alist(r.clone()),
        _ => Err(CompileErr(
            lst.loc(),
            format!("No third element of {}", lst.to_string()),
        )),
    }
}

fn synthesize_args(
    template: Rc<SExp>,
    env: &HashMap<Vec<u8>, Rc<BodyForm>>,
) -> Result<Rc<BodyForm>, CompileErr> {
    match template.borrow() {
        SExp::Atom(_, name) => env.get(name).map(|x| Ok(x.clone())).unwrap_or_else(|| {
            Err(CompileErr(
                template.loc(),
                format!(
                    "Argument {} referenced but not in env",
                    template.to_string()
                ),
            ))
        }),
        SExp::Cons(l, f, r) => Ok(Rc::new(BodyForm::Call(
            l.clone(),
            vec![
                Rc::new(BodyForm::Value(SExp::atom_from_string(
                    template.loc(),
                    &"c".to_string(),
                ))),
                synthesize_args(f.clone(), env)?,
                synthesize_args(r.clone(), env)?,
            ],
        ))),
        SExp::Nil(l) => Ok(Rc::new(BodyForm::Quoted(SExp::Nil(l.clone())))),
        _ => Err(CompileErr(
            template.loc(),
            format!("unknown argument template {}", template.to_string()),
        )),
    }
}

fn reflex_capture(name: &Vec<u8>, capture: Rc<BodyForm>) -> bool {
    match capture.borrow() {
        BodyForm::Value(SExp::Atom(_, n)) => n == name,
        _ => false,
    }
}

impl Evaluator {
    pub fn new(
        opts: Rc<dyn CompilerOpts>,
        runner: Rc<dyn TRunProgram>,
        helpers: Vec<HelperForm>,
    ) -> Self {
        Evaluator {
            opts: opts.clone(),
            runner: runner,
            prims: opts.prim_map(),
            helpers: helpers,
        }
    }

    fn invoke_macro_expansion(
        &self,
        allocator: &mut Allocator,
        l: Srcloc,
        call_loc: Srcloc,
        program: Rc<CompileForm>,
        prog_args: Rc<SExp>,
        arguments_to_convert: &Vec<Rc<BodyForm>>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        // Pass the SExp representation of the expressions into
        // the macro after forming an argument sexp and then
        let mut macro_args = Rc::new(SExp::Nil(l.clone()));
        for i_reverse in 0..arguments_to_convert.len() {
            let i = arguments_to_convert.len() - i_reverse - 1;
            let arg_repr = arguments_to_convert[i].to_sexp();
            macro_args = Rc::new(SExp::Cons(l.clone(), arg_repr, macro_args));
        }

        let macro_expansion =
            self.expand_macro(allocator, l.clone(), program.clone(), macro_args)?;

        let input_sexp = dequote(call_loc.clone(), macro_expansion)?;

        let frontend_macro_input = Rc::new(SExp::Cons(
            l.clone(),
            Rc::new(SExp::atom_from_string(l.clone(), &"mod".to_string())),
            Rc::new(SExp::Cons(
                l.clone(),
                prog_args.clone(),
                Rc::new(SExp::Cons(
                    l.clone(),
                    input_sexp,
                    Rc::new(SExp::Nil(l.clone())),
                )),
            )),
        ));

        frontend(self.opts.clone(), vec![frontend_macro_input]).and_then(|program| {
            self.shrink_bodyform(
                allocator,
                prog_args.clone(),
                env,
                program.exp.clone(),
                false,
            )
        })
    }

    fn invoke_primitive(
        &self,
        allocator: &mut Allocator,
        l: Srcloc,
        call_name: &Vec<u8>,
        parts: &Vec<Rc<BodyForm>>,
        body: Rc<BodyForm>,
        prog_args: Rc<SExp>,
        arguments_to_convert: &Vec<Rc<BodyForm>>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut all_primitive = true;
        let mut target_vec: Vec<Rc<BodyForm>> = parts.clone();

        if call_name == &"@".as_bytes().to_vec() {
            // Synthesize the environment for this function
            Ok(Rc::new(BodyForm::Quoted(SExp::Cons(
                l.clone(),
                Rc::new(SExp::Nil(l.clone())),
                prog_args,
            ))))
        } else if call_name == &"com".as_bytes().to_vec() {
            let mut end_of_list = Rc::new(SExp::Cons(
                l.clone(),
                arguments_to_convert[0].to_sexp(),
                Rc::new(SExp::Nil(l.clone())),
            ));

            for h in self.helpers.iter() {
                end_of_list = Rc::new(SExp::Cons(l.clone(), h.to_sexp(), end_of_list))
            }

            let use_body = SExp::Cons(
                l.clone(),
                Rc::new(SExp::Atom(l.clone(), "mod".as_bytes().to_vec())),
                Rc::new(SExp::Cons(l.clone(), prog_args.clone(), end_of_list)),
            );

            let compiled = self.compile_code(allocator, false, Rc::new(use_body))?;
            let compiled_borrowed: &SExp = compiled.borrow();
            Ok(Rc::new(BodyForm::Quoted(compiled_borrowed.clone())))
        } else {
            let pres = self
                .lookup_prim(l.clone(), call_name)
                .map(|prim| {
                    // Reduce all arguments.
                    let mut converted_args = SExp::Nil(l.clone());

                    for i_reverse in 0..arguments_to_convert.len() {
                        let i = arguments_to_convert.len() - i_reverse - 1;
                        let shrunk = self.shrink_bodyform(
                            allocator,
                            prog_args.clone(),
                            env,
                            arguments_to_convert[i].clone(),
                            only_inline,
                        )?;

                        target_vec[i + 1] = shrunk.clone();

                        if !arg_inputs_primitive(Rc::new(ArgInputs::Whole(shrunk.clone()))) {
                            all_primitive = false;
                        }

                        converted_args =
                            SExp::Cons(l.clone(), shrunk.to_sexp(), Rc::new(converted_args));
                    }

                    if all_primitive {
                        match self.run_prim(
                            allocator,
                            l.clone(),
                            make_prim_call(l.clone(), prim.clone(), Rc::new(converted_args)),
                            Rc::new(SExp::Nil(l.clone())),
                        ) {
                            Ok(res) => Ok(res),
                            Err(e) => {
                                if only_inline {
                                    Ok(Rc::new(BodyForm::Call(l.clone(), target_vec.clone())))
                                } else {
                                    Err(e)
                                }
                            }
                        }
                    } else {
                        let reformed = BodyForm::Call(l.clone(), target_vec.clone());
                        Ok(Rc::new(reformed))
                    }
                })
                .unwrap_or_else(|| {
                    // Build SExp arguments for external call or
                    // return the unevaluated chunk with minimized
                    // arguments.
                    Err(CompileErr(
                        l.clone(),
                        format!(
                            "Don't yet support this call type {} {:?}",
                            body.to_sexp().to_string(),
                            body
                        ),
                    ))
                })?;
            Ok(pres)
        }
    }

    fn handle_invoke(
        &self,
        allocator: &mut Allocator,
        l: Srcloc,
        call_loc: Srcloc,
        call_name: &Vec<u8>,
        head_expr: Rc<BodyForm>,
        parts: &Vec<Rc<BodyForm>>,
        body: Rc<BodyForm>,
        prog_args: Rc<SExp>,
        arguments_to_convert: &Vec<Rc<BodyForm>>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let helper = select_helper(&self.helpers, call_name);
        match helper {
            Some(HelperForm::Defconstant(_, _, _)) => Err(CompileErr(
                call_loc.clone(),
                format!("Can't call constant {}", head_expr.to_sexp().to_string()),
            )),
            Some(HelperForm::Defmacro(l, name, args, program)) => self.invoke_macro_expansion(
                allocator,
                l.clone(),
                call_loc.clone(),
                program,
                prog_args.clone(),
                arguments_to_convert,
                env,
            ),
            Some(HelperForm::Defun(_, _, inline, args, fun_body)) => {
                if !inline && only_inline {
                    return Ok(body.clone());
                }

                let argument_captures_untranslated =
                    build_argument_captures(&call_loc, &arguments_to_convert, args.clone())?;

                let mut argument_captures = HashMap::new();
                // Do this to protect against misalignment
                // between argument vec and destructuring.
                for kv in argument_captures_untranslated.iter() {
                    let shrunk = self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        env,
                        kv.1.clone(),
                        only_inline,
                    )?;

                    argument_captures.insert(kv.0.clone(), shrunk.clone());
                }

                self.shrink_bodyform(
                    allocator,
                    args.clone(),
                    &argument_captures,
                    fun_body,
                    only_inline,
                )
            }
            None => self.invoke_primitive(
                allocator,
                l.clone(),
                call_name,
                parts,
                body,
                prog_args,
                arguments_to_convert,
                env,
                only_inline,
            ),
        }
    }

    // A frontend language evaluator and minifier
    pub fn shrink_bodyform(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        body: Rc<BodyForm>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        match body.borrow() {
            BodyForm::Let(_, LetFormKind::Parallel, bindings, body) => {
                let updated_bindings = update_parallel_bindings(env, bindings);
                self.shrink_bodyform(
                    allocator,
                    prog_args.clone(),
                    &updated_bindings,
                    body.clone(),
                    only_inline,
                )
            }
            BodyForm::Let(l, LetFormKind::Sequential, bindings, body) => {
                if bindings.len() == 0 {
                    self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        env,
                        body.clone(),
                        only_inline,
                    )
                } else {
                    let first_binding_as_list: Vec<Rc<Binding>> =
                        bindings.iter().take(1).map(|x| x.clone()).collect();
                    let rest_of_bindings: Vec<Rc<Binding>> =
                        bindings.iter().skip(1).map(|x| x.clone()).collect();

                    let updated_bindings = update_parallel_bindings(env, &first_binding_as_list);
                    self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        &updated_bindings,
                        Rc::new(BodyForm::Let(
                            l.clone(),
                            LetFormKind::Sequential,
                            rest_of_bindings,
                            body.clone(),
                        )),
                        only_inline,
                    )
                }
            }
            BodyForm::Quoted(_) => Ok(body.clone()),
            BodyForm::Value(SExp::Atom(l, name)) => {
                if name == &"@".as_bytes().to_vec() {
                    let literal_args = synthesize_args(prog_args.clone(), env)?;
                    self.shrink_bodyform(
                        allocator,
                        prog_args.clone(),
                        env,
                        literal_args,
                        only_inline,
                    )
                } else {
                    env.get(name)
                        .map(|x| {
                            if reflex_capture(name, x.clone()) {
                                Ok(x.clone())
                            } else {
                                self.shrink_bodyform(
                                    allocator,
                                    prog_args.clone(),
                                    env,
                                    x.clone(),
                                    only_inline,
                                )
                            }
                        })
                        .unwrap_or_else(|| {
                            self.get_constant(name)
                                .map(|x| {
                                    self.shrink_bodyform(
                                        allocator,
                                        prog_args.clone(),
                                        env,
                                        x.clone(),
                                        only_inline,
                                    )
                                })
                                .unwrap_or_else(|| {
                                    Ok(Rc::new(BodyForm::Value(SExp::Atom(
                                        l.clone(),
                                        name.clone(),
                                    ))))
                                })
                        })
                }
            }
            BodyForm::Value(v) => Ok(Rc::new(BodyForm::Quoted(v.clone()))),
            BodyForm::Call(l, parts) => {
                if parts.len() == 0 {
                    return Err(CompileErr(l.clone(), format!("Impossible empty call list")));
                }

                let head_expr = parts[0].clone();
                let arguments_to_convert: Vec<Rc<BodyForm>> =
                    parts.iter().skip(1).map(|x| x.clone()).collect();

                match head_expr.borrow() {
                    BodyForm::Value(SExp::Atom(call_loc, call_name)) => self.handle_invoke(
                        allocator,
                        l.clone(),
                        call_loc.clone(),
                        call_name,
                        head_expr.clone(),
                        &parts,
                        body.clone(),
                        prog_args,
                        &arguments_to_convert,
                        env,
                        only_inline,
                    ),
                    _ => Err(CompileErr(
                        l.clone(),
                        format!("Don't know how to call {}", head_expr.to_sexp().to_string()),
                    )),
                }
            }
        }
    }

    fn expand_macro(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        call_loc: Srcloc,
        program: Rc<CompileForm>,
        args: Rc<SExp>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut new_helpers = Vec::new();
        let mut used_names = HashSet::new();

        let mut end_of_list = Rc::new(SExp::Cons(
            call_loc.clone(),
            program.exp.to_sexp(),
            Rc::new(SExp::Nil(call_loc.clone())),
        ));

        for h in program.helpers.iter() {
            new_helpers.push(h.clone());
            used_names.insert(h.name());
        }

        for h in self.helpers.iter() {
            if !used_names.contains(h.name()) {
                new_helpers.push(h.clone());
            }
        }

        for h in new_helpers.iter() {
            end_of_list = Rc::new(SExp::Cons(call_loc.clone(), h.to_sexp(), end_of_list))
        }

        let use_body = Rc::new(SExp::Cons(
            call_loc.clone(),
            Rc::new(SExp::Atom(call_loc.clone(), "mod".as_bytes().to_vec())),
            Rc::new(SExp::Cons(
                call_loc.clone(),
                program.args.clone(),
                end_of_list,
            )),
        ));

        let compiled = self.compile_code(allocator, false, use_body)?;
        self.run_prim(allocator, call_loc.clone(), compiled, args)
    }

    fn lookup_prim(&self, l: Srcloc, name: &Vec<u8>) -> Option<Rc<SExp>> {
        match self.prims.get(name) {
            Some(p) => Some(p.clone()),
            None => {
                if name.len() == 1 {
                    Some(Rc::new(SExp::Atom(l, name.clone())))
                } else {
                    None
                }
            }
        }
    }

    fn run_prim(
        &self,
        allocator: &mut Allocator,
        call_loc: Srcloc,
        prim: Rc<SExp>,
        args: Rc<SExp>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        run(
            allocator,
            self.runner.clone(),
            self.prims.clone(),
            prim,
            args,
        )
        .map_err(|e| match e {
            RunFailure::RunExn(_, s) => {
                CompileErr(call_loc.clone(), format!("exception: {}", s.to_string()))
            }
            RunFailure::RunErr(_, s) => CompileErr(call_loc.clone(), s.clone()),
        })
        .map(|res| {
            let res_borrowed: &SExp = res.borrow();
            Rc::new(BodyForm::Quoted(res_borrowed.clone()))
        })
    }

    fn compile_code(
        &self,
        allocator: &mut Allocator,
        in_defun: bool,
        use_body: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        // Com takes place in the current environment.
        // We can only reduce com if all bindings are
        // primitive.
        let updated_opts = self
            .opts
            .set_stdenv(!in_defun)
            .set_in_defun(in_defun)
            .set_frontend_opt(false);

        let com_result = updated_opts.compile_program(
            allocator,
            self.runner.clone(),
            use_body,
            &mut HashMap::new(),
        )?;

        Ok(Rc::new(com_result))
    }

    pub fn add_helper(&mut self, h: &HelperForm) {
        for i in 0..self.helpers.len() {
            if self.helpers[i].name() == h.name() {
                self.helpers[i] = h.clone();
                return;
            }
        }
        self.helpers.push(h.clone());
    }

    fn get_constant(&self, name: &Vec<u8>) -> Option<Rc<BodyForm>> {
        for h in self.helpers.iter() {
            match h {
                HelperForm::Defconstant(_, n, body) => {
                    if n == name {
                        return Some(body.clone());
                    }
                }
                _ => {}
            }
        }
        None
    }
}
