use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::{run, sha256tree};
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    Binding, BodyForm, CompileErr, CompileForm, CompilerOpts, HelperForm, LetFormKind,
};
use crate::compiler::frontend::frontend;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::{number_from_u8, u8_from_number, Number};

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
    mash_conditions: bool,
    ignore_exn: bool,
}

fn select_helper(bindings: &Vec<HelperForm>, name: &Vec<u8>) -> Option<HelperForm> {
    for b in bindings.iter() {
        if b.name() == name {
            return Some(b.clone());
        }
    }

    None
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
            match (is_at_capture(f.clone(), r.clone()), bf.borrow()) {
                (Some((capture, substructure)), BodyForm::Quoted(SExp::Cons(_, _, _))) => {
                    argument_captures.insert(capture.clone(), bf.clone());
                    create_argument_captures(argument_captures, formed_arguments, substructure)
                }
                (None, BodyForm::Quoted(SExp::Cons(_, fa, ra))) => {
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
                (Some((capture, substructure)), bf) => {
                    argument_captures.insert(capture.clone(), Rc::new(bf.clone()));
                    create_argument_captures(argument_captures, formed_arguments, substructure)
                }
                (None, bf) => {
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
        (ArgInputs::Pair(af, ar), SExp::Cons(l, f, r)) => {
            if let Some((capture, substructure)) = is_at_capture(f.clone(), r.clone()) {
                let bfa = get_bodyform_from_arginput(l, af);
                let bfb = get_bodyform_from_arginput(l, ar);
                let fused_arguments =
                    Rc::new(make_operator2(l, "c".to_string(), bfa.clone(), bfb.clone()));
                argument_captures.insert(capture.clone(), fused_arguments);
                create_argument_captures(argument_captures, formed_arguments, substructure)
            } else {
                create_argument_captures(argument_captures, af, f.clone())?;
                create_argument_captures(argument_captures, ar, r.clone())
            }
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
    create_argument_captures(&mut argument_captures, &formed_arguments, args)?;
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
        SExp::Cons(l, a, b) => {
            if let Some((capture, substructure)) = is_at_capture(a.clone(), b.clone()) {
                captures.insert(
                    capture.clone(),
                    Rc::new(BodyForm::Value(SExp::Atom(l.clone(), capture.clone()))),
                );
                build_reflex_captures(captures, substructure);
            } else {
                build_reflex_captures(captures, a.clone());
                build_reflex_captures(captures, b.clone());
            }
        }
        _ => {}
    }
}

pub fn dequote(l: Srcloc, exp: Rc<BodyForm>) -> Result<Rc<SExp>, CompileErr> {
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

/*
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
*/

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
        SExp::Cons(l, f, r) => {
            if let Some((capture, _substructure)) = is_at_capture(f.clone(), r.clone()) {
                synthesize_args(Rc::new(SExp::Atom(l.clone(), capture.clone())), env)
            } else {
                Ok(Rc::new(BodyForm::Call(
                    l.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::atom_from_string(
                            template.loc(),
                            &"c".to_string(),
                        ))),
                        synthesize_args(f.clone(), env)?,
                        synthesize_args(r.clone(), env)?,
                    ],
                )))
            }
        }
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

fn match_atom_to_prim(name: Vec<u8>, p: u8, h: Rc<SExp>) -> bool {
    match h.borrow() {
        SExp::Atom(_, v) => v == &name || (v.len() == 1 && v[0] == p),
        SExp::Integer(_, v) => *v == p.to_bigint().unwrap(),
        _ => false,
    }
}

fn is_quote_atom(h: Rc<SExp>) -> bool {
    match_atom_to_prim(vec![b'q'], 1, h)
}

fn is_apply_atom(h: Rc<SExp>) -> bool {
    match_atom_to_prim(vec![b'a'], 2, h)
}

fn is_i_atom(h: Rc<SExp>) -> bool {
    match_atom_to_prim(vec![b'i'], 3, h)
}

fn is_cons_atom(h: Rc<SExp>) -> bool {
    match_atom_to_prim(vec![b'c'], 4, h)
}

fn match_cons(args: Rc<BodyForm>) -> Option<(Rc<BodyForm>, Rc<BodyForm>)> {
    if let BodyForm::Call(_, v) = args.borrow() {
        if v.len() < 3 {
            return None;
        }
        let have_cons_atom = is_cons_atom(v[0].to_sexp());
        if have_cons_atom {
            return Some((v[1].clone(), v[2].clone()));
        }
    }

    None
}

fn promote_args_to_bodyform(
    head: Rc<SExp>,
    arg: Rc<SExp>,
    whole_args: Rc<BodyForm>,
) -> Result<Vec<Rc<BodyForm>>, CompileErr> {
    if let Some(v) = arg.proper_list() {
        let head_borrowed: &SExp = head.borrow();
        let mut result = vec![Rc::new(BodyForm::Value(head_borrowed.clone()))];
        for a in v.iter() {
            result.push(promote_program_to_bodyform(
                Rc::new(a.clone()),
                whole_args.clone(),
            )?);
        }
        return Ok(result);
    }

    Err(CompileErr(
        arg.loc(),
        "improper argument list for primitive".to_string(),
    ))
}

fn choose_from_env_by_path(path_: Number, args_program: Rc<BodyForm>) -> Rc<BodyForm> {
    let mut path = path_;
    let mut op_list = Vec::new();
    let two = 2_i32.to_bigint().unwrap();

    if path == bi_zero() {
        return Rc::new(BodyForm::Quoted(SExp::Nil(args_program.loc())));
    }

    while path != bi_one() {
        op_list.push(path.clone() % two.clone() == bi_one());
        path = path.clone() / two.clone();
    }

    let mut result_form = args_program.clone();
    for op in op_list.iter() {
        if let Some((head, tail)) = match_cons(result_form.clone()) {
            if *op {
                result_form = tail.clone();
            } else {
                result_form = head.clone();
            }
        } else {
            let apply_op = if *op { 6 } else { 5 };
            result_form = Rc::new(BodyForm::Call(
                args_program.loc(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Atom(
                        args_program.loc(),
                        vec![apply_op],
                    ))),
                    result_form,
                ],
            ));
        }
    }
    result_form
}

fn promote_program_to_bodyform(
    program: Rc<SExp>,
    env: Rc<BodyForm>,
) -> Result<Rc<BodyForm>, CompileErr> {
    match program.borrow() {
        SExp::Cons(_, h, t) => {
            if is_quote_atom(h.clone()) {
                let t_borrowed: &SExp = t.borrow();
                return Ok(Rc::new(BodyForm::Quoted(t_borrowed.clone())));
            }

            // Process tails to change bare numbers to (@ n)
            let args = promote_args_to_bodyform(h.clone(), t.clone(), env.clone())?;
            Ok(Rc::new(BodyForm::Call(program.loc(), args)))
        }
        SExp::Integer(_, n) => {
            // A program that is an atom refers to a position
            // in the environment.
            Ok(choose_from_env_by_path(n.clone(), env.clone()))
        }
        SExp::QuotedString(_, _, v) => {
            // Treated as integer path.
            let integer = number_from_u8(v);
            Ok(choose_from_env_by_path(integer, env.clone()))
        }
        SExp::Atom(_, v) => {
            // Treated as integer path.
            let integer = number_from_u8(v);
            Ok(choose_from_env_by_path(integer, env.clone()))
        }
        _ => {
            let borrowed_program: &SExp = program.borrow();
            Ok(Rc::new(BodyForm::Quoted(borrowed_program.clone())))
        }
    }
}

fn match_i_op(candidate: Rc<BodyForm>) -> Option<(Rc<BodyForm>, Rc<BodyForm>, Rc<BodyForm>)> {
    if let BodyForm::Call(_, cvec) = candidate.borrow() {
        if cvec.len() != 4 {
            return None;
        }
        if let BodyForm::Value(atom) = cvec[0].borrow() {
            if is_i_atom(Rc::new(atom.clone())) {
                return Some((cvec[1].clone(), cvec[2].clone(), cvec[3].clone()));
            }
        }
    }

    None
}

fn fake_body_of_env(l: Srcloc, env: &HashMap<Vec<u8>, Rc<BodyForm>>) -> Rc<BodyForm> {
    let mut composed = Rc::new(BodyForm::Quoted(SExp::Nil(l.clone())));
    let mut sorted_env: Vec<Vec<u8>> = env.iter().map(|nv| nv.0.clone()).collect();
    sorted_env.sort();
    for nv in sorted_env.iter() {
        if let Some(v) = env.get(nv) {
            let entry = Rc::new(BodyForm::Call(
                v.loc(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Atom(v.loc(), nv.clone()))),
                    v.clone(),
                ],
            ));
            composed = Rc::new(BodyForm::Call(l.clone(), vec![entry, composed]));
        }
    }
    composed
}

fn compute_hash_of_apply(body: Rc<BodyForm>, env: Rc<BodyForm>) -> Vec<u8> {
    let composed = Rc::new(BodyForm::Call(body.loc(), vec![body.clone(), env.clone()]));
    sha256tree(composed.to_sexp())
}

fn flatten_expression_to_names_inner(collection: &mut HashSet<Vec<u8>>, expr: Rc<SExp>) {
    match expr.borrow() {
        SExp::Cons(_, a, b) => {
            flatten_expression_to_names_inner(collection, a.clone());
            flatten_expression_to_names_inner(collection, b.clone());
        }
        SExp::Atom(_, a) => {
            collection.insert(a.clone());
        }
        _ => {}
    }
}

fn flatten_expression_to_names(expr: Rc<SExp>) -> Rc<BodyForm> {
    let mut collection = HashSet::new();
    flatten_expression_to_names_inner(&mut collection, expr.clone());
    let mut transformed = Vec::new();
    for a in collection.iter() {
        transformed.push(a.clone());
    }
    transformed.sort();
    let mut call_vec: Vec<Rc<BodyForm>> = transformed
        .iter()
        .map(|x| Rc::new(BodyForm::Value(SExp::Atom(expr.loc(), x.clone()))))
        .collect();
    call_vec.insert(
        0,
        Rc::new(BodyForm::Value(SExp::Atom(expr.loc(), vec![b'+']))),
    );
    Rc::new(BodyForm::Call(expr.loc(), call_vec))
}

impl Evaluator {
    pub fn new(
        opts: Rc<dyn CompilerOpts>,
        runner: Rc<dyn TRunProgram>,
        helpers: Vec<HelperForm>,
    ) -> Self {
        Evaluator {
            opts: opts.clone(),
            runner,
            prims: opts.prim_map(),
            helpers,
            mash_conditions: false,
            ignore_exn: false,
        }
    }

    pub fn mash_conditions(&self) -> Self {
        Evaluator {
            opts: self.opts.clone(),
            runner: self.runner.clone(),
            prims: self.prims.clone(),
            helpers: self.helpers.clone(),
            mash_conditions: true,
            ignore_exn: true,
        }
    }

    fn invoke_macro_expansion(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
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

        if let Ok(input) = dequote(call_loc.clone(), macro_expansion.clone()) {
            let frontend_macro_input = Rc::new(SExp::Cons(
                l.clone(),
                Rc::new(SExp::atom_from_string(l.clone(), &"mod".to_string())),
                Rc::new(SExp::Cons(
                    l.clone(),
                    prog_args.clone(),
                    Rc::new(SExp::Cons(l.clone(), input, Rc::new(SExp::Nil(l.clone())))),
                )),
            ));

            frontend(self.opts.clone(), vec![frontend_macro_input]).and_then(|program| {
                self.shrink_bodyform_visited(
                    allocator,
                    visited,
                    prog_args.clone(),
                    env,
                    program.exp.clone(),
                    false,
                )
            })
        } else {
            promote_program_to_bodyform(
                macro_expansion.to_sexp(),
                Rc::new(BodyForm::Value(SExp::Atom(
                    macro_expansion.loc(),
                    vec![b'@'],
                ))),
            )
        }
    }

    fn invoke_primitive(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
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
                        let shrunk = self.shrink_bodyform_visited(
                            allocator,
                            visited,
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
                                if only_inline || self.ignore_exn {
                                    Ok(Rc::new(BodyForm::Call(l.clone(), target_vec.clone())))
                                } else {
                                    Err(e)
                                }
                            }
                        }
                    } else {
                        let reformed = BodyForm::Call(l.clone(), target_vec.clone());
                        self.chase_apply(allocator, visited, Rc::new(reformed))
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

    fn continue_apply(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
        env: Rc<BodyForm>,
        run_program: Rc<SExp>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let bindings = HashMap::new();
        let program = promote_program_to_bodyform(run_program.clone(), env)?;
        let apply_result = self.shrink_bodyform_visited(
            allocator,
            visited,
            Rc::new(SExp::Nil(run_program.loc())),
            &bindings,
            program,
            false,
        )?;
        self.chase_apply(allocator, visited, apply_result)
    }

    fn do_mash_condition(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
        maybe_condition: Rc<BodyForm>,
        env: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        // The inner part could be an 'i' which we know passes on
        // one of the two conditional arguments.  This was an apply so
        // we can distribute over the conditional arguments.
        if let Some((cond, iftrue, iffalse)) = match_i_op(maybe_condition.clone()) {
            let x_head = Rc::new(BodyForm::Value(SExp::Atom(cond.loc(), vec![b'x'])));
            let apply_head = Rc::new(BodyForm::Value(SExp::Atom(iftrue.loc(), vec![2])));
            let where_from = cond.loc().to_string();
            let where_from_vec = where_from.as_bytes().to_vec();

            if let Some(present) = visited.get(&where_from_vec) {
                return Ok(present.clone());
            }

            visited.insert(
                where_from_vec.clone(),
                Rc::new(BodyForm::Call(
                    maybe_condition.loc(),
                    vec![x_head.clone(), cond.clone()],
                )),
            );

            let surrogate_apply_true = self.chase_apply(
                allocator,
                visited,
                Rc::new(BodyForm::Call(
                    iftrue.loc(),
                    vec![apply_head.clone(), iftrue.clone(), env.clone()],
                )),
            );

            let surrogate_apply_false = self.chase_apply(
                allocator,
                visited,
                Rc::new(BodyForm::Call(
                    iffalse.loc(),
                    vec![apply_head, iffalse.clone(), env.clone()],
                )),
            );

            // Reproduce the equivalent hull over the used values of
            // (a (i cond surrogate_apply_true surrogate_apply_false))
            // Flatten and short circuit any farther evaluation since we just
            // want the argument names passed through from the environment.
            let res = Rc::new(BodyForm::Call(
                maybe_condition.loc(),
                vec![
                    x_head,
                    flatten_expression_to_names(cond.to_sexp()),
                    flatten_expression_to_names(surrogate_apply_true?.to_sexp()),
                    flatten_expression_to_names(surrogate_apply_false?.to_sexp()),
                ],
            ));

            return Ok(res);
        }

        Err(CompileErr(maybe_condition.loc(), "not i op".to_string()))
    }

    fn chase_apply(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let BodyForm::Call(l, vec) = body.borrow() {
            if is_apply_atom(vec[0].to_sexp()) {
                if let Ok(run_program) = dequote(l.clone(), vec[1].clone()) {
                    return self.continue_apply(allocator, visited, vec[2].clone(), run_program);
                }

                if self.mash_conditions {
                    if let Ok(mashed) =
                        self.do_mash_condition(allocator, visited, vec[1].clone(), vec[2].clone())
                    {
                        return Ok(mashed);
                    }
                }
            }
        }

        Ok(body)
    }

    fn handle_invoke(
        &self,
        allocator: &mut Allocator,
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
        l: Srcloc,
        call_loc: Srcloc,
        call_name: &Vec<u8>,
        _head_expr: Rc<BodyForm>,
        parts: &Vec<Rc<BodyForm>>,
        body: Rc<BodyForm>,
        prog_args: Rc<SExp>,
        arguments_to_convert: &Vec<Rc<BodyForm>>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let helper = select_helper(&self.helpers, call_name);
        match helper {
            Some(HelperForm::Defmacro(l, _name, _args, program)) => self.invoke_macro_expansion(
                allocator,
                visited,
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
                    let shrunk = self.shrink_bodyform_visited(
                        allocator,
                        visited,
                        prog_args.clone(),
                        env,
                        kv.1.clone(),
                        only_inline,
                    )?;

                    argument_captures.insert(kv.0.clone(), shrunk.clone());
                }

                self.shrink_bodyform_visited(
                    allocator,
                    visited,
                    args.clone(),
                    &argument_captures,
                    fun_body,
                    only_inline,
                )
            }
            _ => self
                .invoke_primitive(
                    allocator,
                    visited,
                    l.clone(),
                    call_name,
                    parts,
                    body,
                    prog_args,
                    arguments_to_convert,
                    env,
                    only_inline,
                )
                .and_then(|res| self.chase_apply(allocator, visited, res)),
        }
    }

    // A frontend language evaluator and minifier
    pub fn shrink_bodyform_visited(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        visited: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        body: Rc<BodyForm>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        match body.borrow() {
            BodyForm::Let(_, LetFormKind::Parallel, bindings, body) => {
                let updated_bindings = update_parallel_bindings(env, bindings);
                self.shrink_bodyform_visited(
                    allocator,
                    visited,
                    prog_args.clone(),
                    &updated_bindings,
                    body.clone(),
                    only_inline,
                )
            }
            BodyForm::Let(l, LetFormKind::Sequential, bindings, body) => {
                if bindings.len() == 0 {
                    self.shrink_bodyform_visited(
                        allocator,
                        visited,
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
                    self.shrink_bodyform_visited(
                        allocator,
                        visited,
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
                    self.shrink_bodyform_visited(
                        allocator,
                        visited,
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
                                self.shrink_bodyform_visited(
                                    allocator,
                                    visited,
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
                                    self.shrink_bodyform_visited(
                                        allocator,
                                        visited,
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
                        visited,
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
                    BodyForm::Value(SExp::Integer(call_loc, call_int)) => self.handle_invoke(
                        allocator,
                        visited,
                        l.clone(),
                        call_loc.clone(),
                        &u8_from_number(call_int.clone()),
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

    pub fn shrink_bodyform(
        &self,
        allocator: &mut Allocator, // Support random prims via clvm_rs
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        body: Rc<BodyForm>,
        only_inline: bool,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        self.shrink_bodyform_visited(
            allocator, // Support random prims via clvm_rs
            &mut HashMap::new(),
            prog_args,
            env,
            body,
            only_inline,
        )
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
            if let HelperForm::Defconstant(_, n, body) = h {
                if n == name {
                    return Some(body.clone());
                }
            }
        }
        None
    }
}
