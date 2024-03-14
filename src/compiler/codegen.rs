use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::mem::swap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};

use crate::compiler::clvm::{run, truthy};
use crate::compiler::compiler::{compile_from_compileform, is_at_capture};
use crate::compiler::comptypes::{
    fold_m, join_vecs_to_string, list_to_cons, Binding, BindingPattern, BodyForm, CallSpec,
    Callable, CompileErr, CompileForm, CompiledCode, CompilerOpts, CompilerOutput, ConstantKind,
    DefconstData, DefunCall, DefunData, HelperForm, InlineFunction, LetData, LetFormInlineHint, LetFormKind,
    ModulePhase, PrimaryCodegen, RawCallSpec, SyntheticType,
};
use crate::compiler::debug::{build_swap_table_mut, relabel};
use crate::compiler::evaluate::{Evaluator, EVAL_STACK_LIMIT};
use crate::compiler::frontend::{compile_bodyform, make_provides_set};
use crate::compiler::gensym::gensym;
use crate::compiler::inline::{replace_in_inline, synthesize_args};
use crate::compiler::lambda::lambda_codegen;
use crate::compiler::optimize::depgraph::{DepgraphOptions, FunctionDependencyGraph};
use crate::compiler::prims::{primapply, primcons, primquote};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, printable, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::StartOfCodegenOptimization;
use crate::compiler::{BasicCompileContext, CompileContextWrapper};
use crate::util::{toposort, u8_from_number, Number, TopoSortItem};

const MACRO_TIME_LIMIT: usize = 1000000;
pub const CONST_EVAL_LIMIT: usize = 1000000;

/* As in the python code, produce a pair whose (thanks richard)
 *
 *   - car is the compiled code and
 *   - cdr is the argument from the mod definition
 *
 *   Every let adds arguments, and since we model each function level target
 *   as a mod () in the end, we can do the same with let bindings, letting
 *   each group of bindings:
 *
 *       (mod args
 *         (let
 *           ((x (+ a 1))
 *            (y (+ b 1)))
 *
 *           (+ x y)))
 *
 *   Translate to:
 *
 *       (mod (a b)
 *         (defun let_$1 ((a b) x y) (+ x y))
 *         (let_$1 (r @) (+ a 1) (+ b 1))
 *         )
 */

fn cons_bodyform(loc: Srcloc, left: Rc<BodyForm>, right: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        loc.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::Atom(loc, "c".as_bytes().to_vec()))), // Cons
            left,
            right,
        ],
        None,
    )
}

fn empty_left_env(env: Rc<SExp>) -> Option<Rc<SExp>> {
    if let SExp::Cons(_, l, r) = env.borrow() {
        if truthy(l.clone()) {
            None
        } else {
            Some(r.clone())
        }
    } else {
        // It's an unusual env, so be conservative.
        None
    }
}

fn enable_nil_env_mode_for_stepping_23_or_greater(
    opts: Rc<dyn CompilerOpts>,
    code_generator: &mut PrimaryCodegen,
) {
    if let Some(s) = opts.dialect().stepping {
        if s >= 23 && opts.optimize() {
            if let Some(whole_env) = empty_left_env(code_generator.env.clone()) {
                code_generator.left_env = false;
                code_generator.env = whole_env;
            }
        }
    }
}

/*
 * Produce a structure that mimics the expected environment if the current inline
 * context had been a function.
 */
fn create_let_env_expression(args: Rc<SExp>) -> BodyForm {
    match args.borrow() {
        SExp::Cons(l, a, b) => cons_bodyform(
            l.clone(),
            Rc::new(create_let_env_expression(a.clone())),
            Rc::new(create_let_env_expression(b.clone())),
        ),
        _ => {
            let cloned: &SExp = args.borrow();
            BodyForm::Value(cloned.clone())
        }
    }
}

fn helper_atom(h: &HelperForm) -> SExp {
    SExp::Atom(h.loc(), h.name().clone())
}

fn build_tree(l: Srcloc, s: usize, e: usize, helper_array: &[HelperForm]) -> SExp {
    if e - s == 1 {
        helper_atom(&helper_array[s])
    } else {
        let mid = (e + s) / 2;
        let car = build_tree(l.clone(), s, mid, helper_array);
        let cdr = build_tree(l.clone(), mid, e, helper_array);
        SExp::Cons(l, Rc::new(car), Rc::new(cdr))
    }
}

fn compute_code_shape(l: Srcloc, helpers: &[HelperForm]) -> SExp {
    let alen = helpers.len();
    if alen == 0 {
        SExp::Nil(l)
    } else if alen == 1 {
        SExp::Atom(l, helpers[0].name().clone())
    } else {
        build_tree(l, 0, alen, helpers)
    }
}

fn compute_env_shape(
    module_phase: Option<&ModulePhase>,
    l: Srcloc,
    args: Rc<SExp>,
    helpers: &[HelperForm]
) -> SExp {
    match module_phase {
        Some(ModulePhase::StandalonePhase(sp)) => {
            let common_env_data = collect_env_names(sp.env.clone());
            let mut extra_env_data = Vec::new();
            for h in helpers.iter() {
                let name_atom = Rc::new(SExp::Atom(h.loc(), h.name().to_vec()));
                if !common_env_data.contains(&name_atom) {
                    extra_env_data.push(name_atom.clone());
                }
            }

            let extra_env_data_strings: Vec<String> = extra_env_data.iter().map(|e| e.to_string()).collect();
            eprintln!("extra_env_data_strings {extra_env_data_strings:?}");
            let extra_env_tree = make_env_tree(&sp.env.loc(), &extra_env_data, 0, extra_env_data.len());
            let car = sp.env.clone();
            if let SExp::Cons(l, all_env, _) = sp.env.borrow() {
                if let SExp::Cons(l, old_env, _) = all_env.borrow() {
                    return SExp::Cons(
                        l.clone(),
                        Rc::new(SExp::Cons(
                            l.clone(),
                            old_env.clone(),
                            extra_env_tree,
                        )),
                        args
                    );
                }
            }

            todo!();
        }
        Some(ModulePhase::CommonPhase) => {
            let car = compute_code_shape(l.clone(), helpers);
            SExp::Cons(
                l.clone(),
                Rc::new(SExp::Cons(
                    l.clone(),
                    Rc::new(car),
                    Rc::new(SExp::Nil(l.clone()))
                )),
                args
            )
        }
        None => {
            let car = compute_code_shape(l.clone(), helpers);
            let cdr = args;
            SExp::Cons(l, Rc::new(car), cdr)
        }
    }

}

fn create_name_lookup_(
    l: Srcloc,
    name: &[u8],
    env: Rc<SExp>,
    find: Rc<SExp>,
) -> Result<u64, CompileErr> {
    match find.borrow() {
        SExp::Atom(l, a) => {
            if *a == *name {
                Ok(1_u64)
            } else {
                Err(CompileErr(
                    l.clone(),
                    format!(
                        "{} not found (via {})",
                        decode_string(name),
                        decode_string(a)
                    ),
                ))
            }
        }
        SExp::Integer(l, i) => {
            let a = u8_from_number(i.clone());
            if a == *name {
                Ok(1_u64)
            } else {
                Err(CompileErr(
                    l.clone(),
                    format!(
                        "{} not found (via {})",
                        decode_string(name),
                        decode_string(&a)
                    ),
                ))
            }
        }
        SExp::Cons(l, head, rest) => {
            if let Some((capture, substructure)) = is_at_capture(head.clone(), rest.clone()) {
                if *capture == *name {
                    Ok(1_u64)
                } else {
                    create_name_lookup_(l.clone(), name, env, substructure)
                }
            } else {
                create_name_lookup_(l.clone(), name, env.clone(), head.clone())
                    .map(|v| Ok(2 * v))
                    .unwrap_or_else(|_| {
                        create_name_lookup_(l.clone(), name, env, rest.clone()).map(|v| 2 * v + 1)
                    })
            }
        }
        _ => Err(CompileErr(
            l,
            format!(
                "operator or function atom {} not found",
                decode_string(name),
            ),
        )),
    }
}

fn is_defun_in_codegen(compiler: &PrimaryCodegen, name: &[u8]) -> bool {
    // Check for an input defun that matches the name.
    for h in compiler.original_helpers.iter() {
        if matches!(h, HelperForm::Defun(false, _)) && h.name() == name {
            return true;
        }
    }

    false
}

fn make_list(loc: Srcloc, elements: Vec<Rc<SExp>>) -> Rc<SExp> {
    let mut res = Rc::new(SExp::Nil(loc.clone()));
    for e in elements.iter().rev() {
        res = Rc::new(primcons(loc.clone(), e.clone(), res));
    }
    res
}

//
// Write an expression that conses the left env.
//
// (list (q . 2) (c (q . 1) n) (list (q . 4) (c (q . 1)    2    ) (q . 1)))
//
// Something like:
//   (apply (quoted (expanded n)) (cons (quoted (expanded 2)) given-args))
//
// If the function is in the common env, and we're in standalone phase, filter
// 6 from the env so the env image is only the common part.
//
// (list (q . 2) (c (q . 1) n) (list (q . 4) (c (q . 1) (c 4 ())) (q . 1)))
//
fn lambda_for_defun(compiler: &PrimaryCodegen, opts: Rc<dyn CompilerOpts>, loc: Srcloc, name: &[u8], lookup: Rc<SExp>) -> Rc<SExp> {
    let one_atom = Rc::new(SExp::Atom(loc.clone(), vec![1]));
    let two_atom = Rc::new(SExp::Atom(loc.clone(), vec![2]));
    let apply_atom = two_atom.clone();
    let cons_atom = Rc::new(SExp::Atom(loc.clone(), vec![4]));
    let four_atom = cons_atom.clone();
    let env_expr =
        if let Some(ModulePhase::StandalonePhase(sp)) = compiler.module_phase.as_ref() {
            // Check whether the function is part of the common env.  If so, filter.
            if create_name_lookup_(loc.clone(), name, sp.env.clone(), sp.env.clone()).is_ok() {
                // The environment we construct replaces path 6 with ().
                Rc::new(primcons(
                    loc.clone(),
                    four_atom.clone(),
                    Rc::new(SExp::Nil(loc.clone()))
                ))
            } else {
                two_atom.clone()
            }
        } else {
            two_atom.clone()
        };

    // Lambda-ize normally by composing an env with the left env as first
    // and the args as rest.
    make_list(
        loc.clone(),
        vec![
            Rc::new(primquote(loc.clone(), apply_atom)),
            Rc::new(primcons(
                loc.clone(),
                Rc::new(primquote(loc.clone(), one_atom.clone())),
                lookup,
            )),
            make_list(
                loc.clone(),
                vec![
                    Rc::new(primquote(loc.clone(), cons_atom)),
                    Rc::new(primcons(
                        loc.clone(),
                        Rc::new(primquote(loc.clone(), one_atom.clone())),
                        env_expr,
                    )),
                    Rc::new(primquote(loc, one_atom)),
                ],
            ),
        ],
    )
}

fn create_name_lookup(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &[u8],
    as_variable: bool,
) -> Result<Rc<SExp>, CompileErr> {
    if let Some(ModulePhase::StandalonePhase(sp)) = opts.module_phase() {
        eprintln!("lookup {} with standalone env {}", sp.env, decode_string(name));
    }
    compiler
        .constants
        .get(name)
        .map(|x| Ok(x.clone()))
        .unwrap_or_else(|| {
            create_name_lookup_(l.clone(), name, compiler.env.clone(), compiler.env.clone()).map(
                |i| {
                    // Determine if it's a defun.  If so we can ensure that it's
                    // callable like a lambda by repeating the left env into it.
                    let find_program = Rc::new(SExp::Integer(l.clone(), i.to_bigint().unwrap()));
                    if as_variable && is_defun_in_codegen(compiler, name) {
                        let l = lambda_for_defun(compiler, opts.clone(), l.clone(), name, find_program);
                        eprintln!("lambda for defun {}: {l}", decode_string(name));
                        eprintln!("env was {}", compiler.env);
                        l
                    } else {
                        find_program
                    }
                },
            )
        })
}

fn get_prim(loc: Srcloc, prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>, name: &[u8]) -> Option<Rc<SExp>> {
    if let Some(p) = prims.get(name) {
        return Some(p.clone());
    }
    let myatom = SExp::Atom(loc, name.to_owned());
    for kv in prims.iter() {
        let val_borrowed: &SExp = kv.1.borrow();
        if val_borrowed == &myatom {
            return Some(Rc::new(myatom));
        }
    }
    None
}

pub fn get_callable(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    atom: Rc<SExp>,
) -> Result<Callable, CompileErr> {
    match atom.borrow() {
        SExp::Atom(l, name) => {
            let macro_def = compiler.macros.get(name);
            let inline = compiler.inlines.get(name);
            let defun = create_name_lookup(opts.clone(), compiler, l.clone(), name, false);
            let prim = get_prim(l.clone(), compiler.prims.clone(), name);
            let atom_is_com = *name == "com".as_bytes().to_vec();
            let atom_is_at =
                *name == "@".as_bytes().to_vec() || *name == "@*env*".as_bytes().to_vec();
            match (macro_def, inline, defun, prim, atom_is_com, atom_is_at) {
                (Some(macro_def), _, _, _, _, _) => {
                    let macro_def_clone: &SExp = macro_def.borrow();
                    Ok(Callable::CallMacro(l.clone(), macro_def_clone.clone()))
                }
                (_, Some(inline), _, _, _, _) => {
                    Ok(Callable::CallInline(l.clone(), inline.clone()))
                }
                (_, _, Ok(defun), _, _, _) => {
                    let defun_clone: &SExp = defun.borrow();
                    Ok(Callable::CallDefun(l.clone(), defun_clone.clone()))
                }
                (_, _, _, Some(prim), _, _) => {
                    let prim_clone: &SExp = prim.borrow();
                    Ok(Callable::CallPrim(l.clone(), prim_clone.clone()))
                }
                (_, _, _, _, true, _) => Ok(Callable::RunCompiler),
                (_, _, _, _, _, true) => Ok(Callable::EnvPath),
                _ => Err(CompileErr(
                    l.clone(),
                    format!("no such callable '{}'", decode_string(name)),
                )),
            }
        }
        SExp::Integer(_, v) => Ok(Callable::CallPrim(l.clone(), SExp::Integer(l, v.clone()))),
        _ => Err(CompileErr(atom.loc(), format!("can't call object {atom}"))),
    }
}

pub fn process_macro_call(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    args: Vec<Rc<BodyForm>>,
    code: Rc<SExp>,
) -> Result<CompiledCode, CompileErr> {
    let converted_args: Vec<Rc<SExp>> = args.iter().map(|b| b.to_sexp()).collect();
    let mut swap_table = HashMap::new();
    let args_to_macro = list_to_cons(l.clone(), &converted_args);
    build_swap_table_mut(&mut swap_table, &args_to_macro);

    let runner = context.runner();
    run(
        context.allocator(),
        runner,
        opts.prim_map(),
        code,
        Rc::new(args_to_macro),
        None,
        Some(MACRO_TIME_LIMIT),
    )
    .map_err(|e| match e {
        RunFailure::RunExn(ml, x) => CompileErr(l, format!("macro aborted at {ml} with {x}")),
        RunFailure::RunErr(rl, e) => CompileErr(l, format!("error executing macro: {rl} {e}")),
    })
    .and_then(|v| {
        let relabeled_expr = relabel(&swap_table, &v);
        compile_bodyform(opts.clone(), Rc::new(relabeled_expr))
    })
    .and_then(|body| generate_expr_code(context, opts, compiler, Rc::new(body)))
}

fn generate_args_code(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    call: &CallSpec,
    with_primcons: bool,
) -> Result<Rc<SExp>, CompileErr> {
    // Early return for the case where there are no provided arguments and no tail.
    if call.args.is_empty() && call.tail.is_none() {
        return Ok(Rc::new(SExp::Nil(call.loc.clone())));
    }

    // Ensure we start with either the specified tail or nil.
    let mut compiled_args: Rc<SExp> = if let Some(t) = call.tail.as_ref() {
        generate_expr_code(context, opts.clone(), compiler, t.clone())?.1
    } else {
        Rc::new(SExp::Nil(call.loc.clone()))
    };

    // Now that we have the tail, generate the code for each argument in reverse
    // order to cons on.
    for hd in call.args.iter().rev() {
        let generated = generate_expr_code(context, opts.clone(), compiler, hd.clone())?.1;

        // This function is now reused for purposes that make a simple list of the
        // converted arguments, or generate valid code with primitive conses.
        if with_primcons {
            compiled_args = Rc::new(primcons(generated.loc(), generated.clone(), compiled_args));
        } else {
            compiled_args = Rc::new(SExp::Cons(
                generated.loc(),
                generated.clone(),
                compiled_args,
            ));
        }
    }

    Ok(compiled_args)
}

fn process_defun_call(
    _opts: Rc<dyn CompilerOpts>,
    _compiler: &PrimaryCodegen,
    l: Srcloc,
    args: Rc<SExp>,
    lookup: Rc<SExp>,
) -> Result<CompiledCode, CompileErr> {
    let env = primcons(
        l.clone(),
        Rc::new(SExp::Integer(l.clone(), 2_u32.to_bigint().unwrap())),
        args,
    );
    Ok(CompiledCode(
        l.clone(),
        Rc::new(primapply(l, lookup, Rc::new(env))),
    ))
}

pub fn get_call_name(l: Srcloc, body: BodyForm) -> Result<Rc<SExp>, CompileErr> {
    match &body {
        BodyForm::Value(SExp::Atom(l, name)) => {
            return Ok(Rc::new(SExp::Atom(l.clone(), name.clone())));
        }
        BodyForm::Value(SExp::Integer(l, v)) => {
            return Ok(Rc::new(SExp::Integer(l.clone(), v.clone())));
        }
        _ => {}
    }

    Err(CompileErr(
        l,
        format!("not yet callable {}", body.to_sexp()),
    ))
}

fn produce_argument_check(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    a: &[u8],
    mut steps: Number,
) -> Result<CompiledCode, CompileErr> {
    if let Ok(SExp::Integer(l, mut lookup)) = create_name_lookup(opts, compiler, loc.clone(), a, true)
        .map(|x| {
            let x_ref: &SExp = x.borrow();
            x_ref.clone()
        })
    {
        let mut bit = bi_one();
        let two = 2_u32.to_bigint().unwrap();

        while bit < lookup {
            bit *= two.clone();
        }

        while steps > bi_zero() {
            steps -= bi_one();
            bit /= two.clone();
            if lookup.clone() & bit.clone() != bi_zero() {
                lookup ^= bit.clone();
            }
            lookup |= bit.clone() / two.clone();
        }

        Ok(CompiledCode(loc.clone(), Rc::new(SExp::Integer(l, lookup))))
    } else {
        Err(CompileErr(
            loc.clone(),
            format!(
                "Lookup of unbound variable {}",
                SExp::Atom(loc.clone(), a.to_vec())
            ),
        ))
    }
}

fn compile_call(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    call: &RawCallSpec,
) -> Result<CompiledCode, CompileErr> {
    let arg_string_list: Vec<Vec<u8>> = call
        .args
        .iter()
        .map(|v| v.to_sexp().to_string().as_bytes().to_vec())
        .collect();

    let error = Err(CompileErr(
        call.loc.clone(),
        format!(
            "wierdly formed compile request: {}",
            join_vecs_to_string(";".as_bytes().to_vec(), &arg_string_list)
        ),
    ));

    let compile_atom_head = |al: Srcloc, an: &Vec<u8>| {
        let tl = call.args.iter().skip(1).cloned().collect();
        get_callable(
            opts.clone(),
            compiler,
            call.loc.clone(),
            Rc::new(SExp::Atom(al.clone(), an.to_vec())),
        )
        .and_then(|calltype| {
            match calltype {
                Callable::CallMacro(l, code) => {
                    process_macro_call(context, opts.clone(), compiler, l, tl, Rc::new(code))
                }

                Callable::CallInline(l, inline) => replace_in_inline(
                    context,
                    opts.clone(),
                    compiler,
                    l.clone(),
                    &inline,
                    l,
                    &tl,
                    call.tail.clone(),
                ),

                Callable::CallDefun(l, lookup) => generate_args_code(
                    context,
                    opts.clone(),
                    compiler,
                    // A callspec is a way to collect some info about a call, mainly
                    // to reduce the number of arguments to pass through.
                    &CallSpec {
                        loc: l.clone(),
                        name: an,
                        args: &tl,
                        tail: call.tail.clone(),
                        original: call.original.clone(),
                    },
                    true,
                )
                .and_then(|args| {
                    process_defun_call(opts.clone(), compiler, l.clone(), args, Rc::new(lookup))
                }),
                Callable::CallPrim(l, p) => generate_args_code(
                    context,
                    opts,
                    compiler,
                    &CallSpec {
                        name: an,
                        loc: l.clone(),
                        args: &tl,
                        tail: None,
                        original: call.original.clone(),
                    },
                    false,
                )
                .map(|args| CompiledCode(l.clone(), Rc::new(SExp::Cons(l, Rc::new(p), args)))),

                Callable::EnvPath => {
                    if tl.len() == 1 {
                        match tl[0].borrow() {
                            BodyForm::Value(SExp::Integer(l, i)) => Ok(CompiledCode(
                                l.clone(),
                                Rc::new(SExp::Integer(l.clone(), i.clone())),
                            )),
                            BodyForm::Quoted(SExp::Integer(l, i)) => Ok(CompiledCode(
                                l.clone(),
                                Rc::new(SExp::Integer(l.clone(), i.clone())),
                            )),
                            _ => Err(CompileErr(
                                al.clone(),
                                "@ form only accepts integers at present".to_string(),
                            )),
                        }
                    } else if tl.len() == 2 {
                        match (tl[0].borrow(), tl[1].borrow()) {
                            (
                                BodyForm::Value(SExp::Atom(_al, a)),
                                BodyForm::Value(SExp::Integer(_il, i)),
                            ) => produce_argument_check(opts, compiler, call.loc.clone(), a, i.clone()),
                            (
                                BodyForm::Value(SExp::Atom(_al, a)),
                                BodyForm::Quoted(SExp::Integer(_il, i)),
                            ) => produce_argument_check(opts, compiler, call.loc.clone(), a, i.clone()),
                            _ => Err(CompileErr(
                                al.clone(),
                                "@ form with two arguments requires argument and integer"
                                    .to_string(),
                            )),
                        }
                    } else {
                        Err(CompileErr(
                            al.clone(),
                            "@ form accepts one argument".to_string(),
                        ))
                    }
                }

                Callable::RunCompiler => {
                    if call.args.len() >= 2 {
                        let updated_opts = opts
                            .set_stdenv(false)
                            .set_in_defun(true)
                            .set_frontend_opt(false)
                            .set_start_env(Some(compiler.env.clone()))
                            .set_code_generator(compiler.clone());

                        let use_body = SExp::Cons(
                            call.loc.clone(),
                            Rc::new(SExp::Atom(call.loc.clone(), "mod".as_bytes().to_vec())),
                            Rc::new(SExp::Cons(
                                call.loc.clone(),
                                Rc::new(SExp::Nil(call.loc.clone())),
                                Rc::new(SExp::Cons(
                                    call.args[1].loc(),
                                    call.args[1].to_sexp(),
                                    Rc::new(SExp::Nil(call.loc.clone())),
                                )),
                            )),
                        );

                        let mut unused_symbol_table = HashMap::new();
                        let mut context_wrapper =
                            CompileContextWrapper::from_context(context, &mut unused_symbol_table);
                        let code = updated_opts
                            .compile_program(&mut context_wrapper.context, Rc::new(use_body))?;

                        match code {
                            CompilerOutput::Program(_, code) => Ok(CompiledCode(
                                call.loc.clone(),
                                Rc::new(primquote(call.loc.clone(), Rc::new(code))),
                            )),
                            CompilerOutput::Module(_) => {
                                todo!();
                            }
                        }
                    } else {
                        error.clone()
                    }
                }
            }
        })
    };

    match call.args[0].borrow() {
        BodyForm::Value(SExp::Integer(al, an)) => {
            compile_atom_head(al.clone(), &u8_from_number(an.clone()))
        }
        BodyForm::Value(SExp::QuotedString(al, _, an)) => compile_atom_head(al.clone(), an),
        BodyForm::Value(SExp::Atom(al, an)) => compile_atom_head(al.clone(), an),
        _ => error,
    }
}

pub fn do_mod_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    program: &CompileForm,
) -> Result<CompiledCode, CompileErr> {
    // A mod form yields the compiled code.
    let without_env = opts.set_start_env(None).set_in_defun(false).set_module_phase(None);
    let mut throwaway_symbols = HashMap::new();
    let mut context_wrapper = CompileContextWrapper::from_context(context, &mut throwaway_symbols);
    let code = codegen(&mut context_wrapper.context, without_env, program)?;
    Ok(CompiledCode(
        program.loc.clone(),
        Rc::new(SExp::Cons(
            program.loc.clone(),
            Rc::new(SExp::Atom(program.loc.clone(), vec![1])),
            Rc::new(code),
        )),
    ))
}

fn is_cons(bf: &BodyForm) -> bool {
    if let BodyForm::Value(v) = bf {
        if let SExp::Atom(_, vec) = v.atomize() {
            return vec == [4] || vec == b"r";
        }
    }

    false
}

fn is_at_env(bf: &BodyForm) -> bool {
    if let BodyForm::Value(v) = bf {
        if let SExp::Atom(_, vec) = v.atomize() {
            return vec == b"@*env*";
        }
    }

    false
}

fn addresses_user_env(call: &[Rc<BodyForm>]) -> bool {
    call.len() == 2 && is_cons(call[0].borrow()) && is_at_env(call[1].borrow())
}

pub fn generate_expr_code(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    expr: Rc<BodyForm>,
) -> Result<CompiledCode, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(LetFormKind::Parallel, letdata) => {
            /* Depends on a defun having been desugared from this let and the let
            expressing rewritten. */
            generate_expr_code(context, opts, compiler, letdata.body.clone())
        }
        BodyForm::Quoted(q) => {
            let l = q.loc();
            Ok(CompiledCode(
                l.clone(),
                Rc::new(primquote(l, Rc::new(q.clone()))),
            ))
        }
        BodyForm::Value(v) => {
            match v {
                SExp::Atom(l, atom) => {
                    if *atom == "@".as_bytes().to_vec() || *atom == "@*env*".as_bytes().to_vec() {
                        Ok(CompiledCode(
                            l.clone(),
                            Rc::new(SExp::Integer(l.clone(), bi_one())),
                        ))
                    } else {
                        create_name_lookup(opts.clone(), compiler, l.clone(), atom, true)
                            .map(|f| Ok(CompiledCode(l.clone(), f)))
                            .unwrap_or_else(|_| {
                                if opts.dialect().strict && printable(atom, false) {
                                    return Err(CompileErr(
                                        l.clone(),
                                        format!(
                                            "Unbound use of {} as a variable name",
                                            decode_string(atom)
                                        ),
                                    ));
                                }

                                // Pass through atoms that don't look up on behalf of
                                // macros, as it's possible that a macro returned
                                // something that's canonically a name in number form.
                                generate_expr_code(
                                    context,
                                    opts,
                                    compiler,
                                    Rc::new(BodyForm::Quoted(SExp::Atom(l.clone(), atom.clone()))),
                                )
                            })
                    }
                }
                SExp::Integer(l, i) => {
                    if opts.dialect().strict {
                        return generate_expr_code(
                            context,
                            opts,
                            compiler,
                            Rc::new(BodyForm::Quoted(SExp::Integer(l.clone(), i.clone()))),
                        );
                    }

                    // Since macros are in this language and the runtime has
                    // a very narrow data representation, we'll need to
                    // accomodate bare numbers coming back in place of identifiers,
                    // but only in legacy non-strict mode.
                    generate_expr_code(
                        context,
                        opts,
                        compiler,
                        Rc::new(BodyForm::Value(SExp::Atom(
                            l.clone(),
                            u8_from_number(i.clone()),
                        ))),
                    )
                }
                _ => Ok(CompiledCode(
                    v.loc(),
                    Rc::new(primquote(v.loc(), Rc::new(v.clone()))),
                )),
            }
        }
        BodyForm::Call(l, list, tail) => {
            // Recognize attempts to get the input arguments.  They're paired with
            // a left env in the usual case, but it can be omitted if there are no
            // freestanding functions.  In that case, the user args are just the
            // whole env.
            if !compiler.left_env && addresses_user_env(list) {
                return generate_expr_code(context, opts, compiler, list[1].clone());
            }
            if list.is_empty() {
                Err(CompileErr(
                    l.clone(),
                    "created a call with no forms".to_string(),
                ))
            } else {
                compile_call(
                    context,
                    opts,
                    compiler,
                    // This is a partial callspec.
                    &RawCallSpec {
                        loc: l.clone(),
                        args: list,
                        tail: tail.clone(),
                        original: expr.clone(),
                    },
                )
            }
        }
        BodyForm::Mod(_, program) => do_mod_codegen(context, opts, program),
        _ => Err(CompileErr(
            expr.loc(),
            format!("don't know how to compile {}", expr.to_sexp()),
        )),
    }
}

fn combine_defun_env(old_env: Rc<SExp>, new_args: Rc<SExp>) -> Rc<SExp> {
    match old_env.borrow() {
        SExp::Cons(l, h, _) => Rc::new(SExp::Cons(l.clone(), h.clone(), new_args)),
        _ => old_env,
    }
}

// Diverts to failure if a symbol is redefined.
fn fail_if_present<T, R>(
    loc: Srcloc,
    map: &HashMap<Vec<u8>, T>,
    name: &[u8],
    result: R,
) -> Result<R, CompileErr> {
    if map.contains_key(name) {
        Err(CompileErr(
            loc.clone(),
            format!("Cannot redefine {}", SExp::Atom(loc, name.to_owned())),
        ))
    } else {
        Ok(result)
    }
}

fn codegen_(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    h: &HelperForm,
) -> Result<PrimaryCodegen, CompileErr> {
    match &h {
        HelperForm::Defun(inline, defun) => {
            if *inline {
                // Note: this just replaces a dummy function inserted earlier.
                // The real redefinition check is in dummy_functions.
                Ok(compiler.add_inline(
                    &defun.name,
                    &InlineFunction {
                        name: defun.name.clone(),
                        args: defun.args.clone(),
                        body: defun.body.clone(),
                    },
                ))
            } else {
                let updated_opts = opts
                    .set_code_generator(compiler.clone())
                    .set_in_defun(true)
                    .set_module_phase(None)
                    .set_stdenv(false)
                    .set_frontend_opt(false)
                    .set_start_env(Some(combine_defun_env(
                        compiler.env.clone(),
                        defun.args.clone(),
                    )));

                let opt = context.pre_codegen_function_optimize(opts.clone(), compiler, defun)?;

                let tocompile = SExp::Cons(
                    defun.loc.clone(),
                    Rc::new(SExp::Atom(defun.loc.clone(), "mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        defun.loc.clone(),
                        defun.args.clone(),
                        Rc::new(SExp::Cons(
                            defun.loc.clone(),
                            opt.to_sexp(),
                            Rc::new(SExp::Nil(defun.loc.clone())),
                        )),
                    )),
                );

                let mut unused_symbol_table = HashMap::new();
                let code = {
                    let mut context_wrapper =
                        CompileContextWrapper::from_context(context, &mut unused_symbol_table);
                    let code = updated_opts
                        .compile_program(&mut context_wrapper.context, Rc::new(tocompile))?;
                    match code {
                        CompilerOutput::Program(_, p) => p,
                        CompilerOutput::Module(_) => {
                            todo!();
                        }
                    }
                };

                let code =
                    context.post_codegen_function_optimize(opts.clone(), Some(h), Rc::new(code))?;
                let code =
                    fail_if_present(defun.loc.clone(), &compiler.inlines, &defun.name, code)?;
                let code = fail_if_present(defun.loc.clone(), &compiler.defuns, &defun.name, code)?;
                Ok(compiler.add_defun(
                    &defun.name,
                    defun.orig_args.clone(),
                    DefunCall {
                        required_env: defun.args.clone(),
                        code,
                    },
                    true, // Always take left env for now
                ))
            }
        }
        _ => Ok(compiler.clone()),
    }
}

fn is_defun_or_tabled_const(b: &HelperForm) -> bool {
    match b {
        HelperForm::Defun(false, _) => true,
        HelperForm::Defconstant(cdata) => cdata.tabled,
        _ => false,
    }
}

pub fn empty_compiler(prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>, l: Srcloc) -> PrimaryCodegen {
    let nil = SExp::Nil(l.clone());
    let nil_rc = Rc::new(nil.clone());

    PrimaryCodegen {
        prims: prim_map,
        constants: HashMap::new(),
        tabled_constants: HashMap::new(),
        module_constants: HashMap::new(),
        inlines: HashMap::new(),
        macros: HashMap::new(),
        defuns: HashMap::new(),
        parentfns: HashSet::new(),
        env: Rc::new(SExp::Cons(l, nil_rc.clone(), nil_rc.clone())),
        to_process: Vec::new(),
        original_helpers: Vec::new(),
        final_expr: Rc::new(BodyForm::Quoted(nil)),
        final_code: None,
        final_env: nil_rc,
        function_symbols: HashMap::new(),
        left_env: true,
        module_phase: None,
    }
}

pub fn should_inline_let(inline_hint: &Option<LetFormInlineHint>) -> bool {
    matches!(inline_hint, None | Some(LetFormInlineHint::Inline(_)))
}

#[allow(clippy::too_many_arguments)]
fn generate_let_defun(
    l: Srcloc,
    kwl: Option<Srcloc>,
    name: &[u8],
    args: Rc<SExp>,
    // Tells what the user's preference is for inlining.  It can be set to None,
    // which means use the form's default.
    // Some(LetFormInlineHint::NoPreference), meaning the system should choose the
    // best inlining strategy,
    // Some(LetFormInlineHint::Inline(_)) or Some(LetFormInlineHint::NonInline(_))
    inline_hint: &Option<LetFormInlineHint>,
    bindings: Vec<Rc<Binding>>,
    body: Rc<BodyForm>,
) -> HelperForm {
    let new_arguments: Vec<Rc<SExp>> = bindings
        .iter()
        .map(|b| match &b.pattern {
            // This is the classic let form.  It doesn't support destructuring.
            BindingPattern::Name(name) => Rc::new(SExp::Atom(l.clone(), name.clone())),
            // The assign form, which supports destructuring and signals newer
            // handling.
            BindingPattern::Complex(sexp) => sexp.clone(),
        })
        .collect();

    let inner_function_args = Rc::new(SExp::Cons(
        l.clone(),
        args,
        Rc::new(list_to_cons(l.clone(), &new_arguments)),
    ));

    HelperForm::Defun(
        // Some forms will be inlined and some as separate functions based on
        // binary size, when permitted.  Sometimes the user will signal a
        // preference.
        should_inline_let(inline_hint),
        DefunData {
            loc: l.clone(),
            nl: l,
            kw: kwl,
            name: name.to_owned(),
            orig_args: inner_function_args.clone(),
            args: inner_function_args,
            body,
            synthetic: Some(SyntheticType::NoInlinePreference),
            ty: None,
        },
    )
}

fn generate_let_args(_l: Srcloc, blist: Vec<Rc<Binding>>) -> Vec<Rc<BodyForm>> {
    blist.iter().map(|b| b.body.clone()).collect()
}

/// Assign arranges its variable names via need and split into batches that don't
/// add additional dependencies.  To illustrate:
///
/// (assign
///   (X . Y) (F A W)
///   W (G A)
///   Z (H X Y W)
///   Next (H2 X Y W)
///   (doit Y Next)
///
/// In this case, we have the following dependencies:
/// W depends on A (external)
/// X and Y depend on A (external) and W
/// Z depends on X Y and W
/// Next depends on X Y and W
/// The body depends on Y and Next.
///
/// So we sort this:
/// W (G A)
/// --- X and Y add a dependency on W ---
/// (X . Y) (F A W)
/// --- Z and Next depend on X Y and W
/// Z (H X Y W)
/// Next (H2 X Y W)
/// --- done sorting, the body has access to all bindings ---
///
/// We return TopoSortItem<Vec<u8>> (bytewise names), which is used in the
/// generic toposort function in util.
///
/// This is used by facilities that need to know the order of the assignments.
///
/// A good number of languages support reorderable assignment (haskell, elm).
pub fn toposort_assign_bindings(
    loc: &Srcloc,
    bindings: &[Rc<Binding>],
) -> Result<Vec<TopoSortItem<Vec<u8>>>, CompileErr> {
    // Topological sort of bindings.
    toposort(
        bindings,
        CompileErr(loc.clone(), "deadlock resolving binding order".to_string()),
        // Needs: What this binding relies on.
        |possible, b| {
            let mut need_set = HashSet::new();
            make_provides_set(&mut need_set, b.body.to_sexp());
            let mut need_set_thats_possible = HashSet::new();
            for need in need_set.intersection(possible) {
                need_set_thats_possible.insert(need.clone());
            }
            Ok(need_set_thats_possible)
        },
        // Has: What this binding provides.
        |b| match &b.pattern {
            BindingPattern::Name(name) => HashSet::from([name.clone()]),
            BindingPattern::Complex(sexp) => {
                let mut result_set = HashSet::new();
                make_provides_set(&mut result_set, sexp.clone());
                result_set
            }
        },
    )
}

/// Let forms are "hoisted" (promoted) from being body forms to being functions
/// in the program (either defun or defun-inline).  The arguments given are bound
/// in the downstream code, allowing the code generator to re-use functions to
/// allow the inner body forms to use the variable names defined in the assign.
/// This is isolated here from hoist_body_let_binding because it has its own
/// complexity that's separate from the original let features.
///
/// In the future, things such as lambdas will also desugar along these same
/// routes.
pub fn hoist_assign_form(letdata: &LetData) -> Result<BodyForm, CompileErr> {
    let sorted_spec = toposort_assign_bindings(&letdata.loc, &letdata.bindings)?;

    // Break up into stages of parallel let forms.
    // Track the needed bindings of this level.
    // If this becomes broader in a way that doesn't
    // match the existing provides, we need to break
    // the let binding.
    let mut current_provides = HashSet::new();
    let mut binding_lists = Vec::new();
    let mut this_round_bindings = Vec::new();
    let mut new_provides: HashSet<Vec<u8>> = HashSet::new();

    for spec in sorted_spec.iter() {
        let mut new_needs = spec.needs.difference(&current_provides).cloned();
        if new_needs.next().is_some() {
            // Roll over the set we're accumulating to the finished version.
            let mut empty_tmp: Vec<Rc<Binding>> = Vec::new();
            swap(&mut empty_tmp, &mut this_round_bindings);
            binding_lists.push(empty_tmp);
            for provided in new_provides.iter() {
                current_provides.insert(provided.clone());
            }
            new_provides.clear();
        }
        // Record what we can provide to the next round.
        for p in spec.has.iter() {
            new_provides.insert(p.clone());
        }
        this_round_bindings.push(letdata.bindings[spec.index].clone());
    }

    // Pick up the last ones that didn't add new needs.
    if !this_round_bindings.is_empty() {
        binding_lists.push(this_round_bindings);
    }

    binding_lists.reverse();

    // Spill let forms as parallel sets to get the best stack we can.
    let mut end_bindings = Vec::new();
    swap(&mut end_bindings, &mut binding_lists[0]);

    // build a stack of let forms starting with the inner most bindings.
    let mut output_let = BodyForm::Let(
        LetFormKind::Parallel,
        Box::new(LetData {
            bindings: end_bindings,
            ..letdata.clone()
        }),
    );

    // build rest of the stack.
    for binding_list in binding_lists.into_iter().skip(1) {
        output_let = BodyForm::Let(
            LetFormKind::Parallel,
            Box::new(LetData {
                bindings: binding_list,
                body: Rc::new(output_let),
                ..letdata.clone()
            }),
        )
    }

    Ok(output_let)
}

/// The main function that, when encountering something that needs to desugar to
/// a function, returns the functions that result (because things inside it may
/// also need to desugar) and rewrites the expression to incorporate that
/// function.
///
/// We add result here in case something needs extra processing, such as assign
/// form sorting, which can fail if a workable order can't be solved.
pub fn hoist_body_let_binding(
    outer_context: Option<Rc<SExp>>,
    args: Rc<SExp>,
    body: Rc<BodyForm>,
) -> Result<(Vec<HelperForm>, Rc<BodyForm>), CompileErr> {
    match body.borrow() {
        BodyForm::Let(LetFormKind::Sequential, letdata) => {
            if letdata.bindings.is_empty() {
                return Ok((vec![], letdata.body.clone()));
            }

            // If we're here, we're in the middle of hoisting.
            // Simply slice one binding and do it again.
            let new_sub_expr = if letdata.bindings.len() == 1 {
                // There is one binding, so we just need to put body below
                letdata.body.clone()
            } else {
                // Slice other bindings
                let sub_bindings = letdata.bindings.iter().skip(1).cloned().collect();
                Rc::new(BodyForm::Let(
                    LetFormKind::Sequential,
                    Box::new(LetData {
                        bindings: sub_bindings,
                        ..*letdata.clone()
                    }),
                ))
            };

            hoist_body_let_binding(
                outer_context,
                args,
                Rc::new(BodyForm::Let(
                    LetFormKind::Parallel,
                    Box::new(LetData {
                        bindings: vec![letdata.bindings[0].clone()],
                        body: new_sub_expr,
                        ..*letdata.clone()
                    }),
                )),
            )
        }
        BodyForm::Let(LetFormKind::Parallel, letdata) => {
            let mut out_defuns = Vec::new();
            let defun_name = gensym("letbinding".as_bytes().to_vec());

            let mut revised_bindings = Vec::new();
            for b in letdata.bindings.iter() {
                let (mut new_helpers, new_binding) =
                    hoist_body_let_binding(outer_context.clone(), args.clone(), b.body.clone())?;
                out_defuns.append(&mut new_helpers);
                revised_bindings.push(Rc::new(Binding {
                    loc: b.loc.clone(),
                    nl: b.nl.clone(),
                    pattern: b.pattern.clone(),
                    body: new_binding,
                }));
            }
            let generated_defun = generate_let_defun(
                letdata.loc.clone(),
                None,
                &defun_name,
                args,
                &letdata.inline_hint,
                revised_bindings.to_vec(),
                letdata.body.clone(),
            );
            out_defuns.push(generated_defun);

            let mut let_args = generate_let_args(letdata.loc.clone(), revised_bindings.to_vec());
            let pass_env = outer_context
                .map(create_let_env_expression)
                .unwrap_or_else(|| {
                    BodyForm::Call(
                        letdata.loc.clone(),
                        vec![
                            Rc::new(BodyForm::Value(SExp::Atom(
                                letdata.loc.clone(),
                                "r".as_bytes().to_vec(),
                            ))),
                            Rc::new(BodyForm::Value(SExp::Atom(
                                letdata.loc.clone(),
                                "@*env*".as_bytes().to_vec(),
                            ))),
                        ],
                        None,
                    )
                });

            let mut call_args = vec![
                Rc::new(BodyForm::Value(SExp::Atom(letdata.loc.clone(), defun_name))),
                Rc::new(pass_env),
            ];
            call_args.append(&mut let_args);

            let final_call = BodyForm::Call(letdata.loc.clone(), call_args, None);
            Ok((out_defuns, Rc::new(final_call)))
        }
        // New alternative for assign forms.
        BodyForm::Let(LetFormKind::Assign, letdata) => {
            hoist_body_let_binding(outer_context, args, Rc::new(hoist_assign_form(letdata)?))
        }
        BodyForm::Call(l, list, tail) => {
            let mut vres = Vec::new();
            let mut new_call_list = vec![list[0].clone()];
            for i in list.iter().skip(1) {
                let (mut new_helpers, new_arg) =
                    hoist_body_let_binding(outer_context.clone(), args.clone(), i.clone())?;
                new_call_list.push(new_arg);
                vres.append(&mut new_helpers);
            }

            // Ensure that we hoist a let occupying the &rest tail.
            let new_tail = if let Some(t) = tail.as_ref() {
                let (mut new_tail_helpers, new_tail) =
                    hoist_body_let_binding(outer_context, args, t.clone())?;
                vres.append(&mut new_tail_helpers);
                Some(new_tail)
            } else {
                None
            };

            Ok((
                vres,
                Rc::new(BodyForm::Call(l.clone(), new_call_list, new_tail)),
            ))
        }
        BodyForm::Lambda(letdata) => {
            let new_function_args = Rc::new(SExp::Cons(
                letdata.loc.clone(),
                letdata.capture_args.clone(),
                letdata.args.clone(),
            ));
            let new_function_name = gensym(b"lambda".to_vec());
            let (mut new_helpers_from_body, new_body) = hoist_body_let_binding(
                Some(new_function_args.clone()),
                new_function_args.clone(),
                letdata.body.clone(),
            )?;
            let new_expr = lambda_codegen(&new_function_name, letdata)?;
            let function = HelperForm::Defun(
                false,
                DefunData {
                    loc: letdata.loc.clone(),
                    name: new_function_name,
                    kw: letdata.kw.clone(),
                    nl: letdata.args.loc(),
                    orig_args: new_function_args.clone(),
                    args: new_function_args,
                    body: new_body,
                    synthetic: Some(SyntheticType::WantNonInline),
                    ty: None,
                },
            );
            new_helpers_from_body.push(function);
            Ok((new_helpers_from_body, Rc::new(new_expr)))
        }
        _ => Ok((Vec::new(), body.clone())),
    }
}

/// Turn the helpers for a program into the fully desugared set of helpers for
/// that program.  This expands and re-processes the helper set until all
/// desugarable body forms have been transformed to a state where no more
/// desugaring is needed.
pub fn process_helper_let_bindings(helpers: &[HelperForm]) -> Result<Vec<HelperForm>, CompileErr> {
    let mut result = helpers.to_owned();
    let mut i = 0;

    while i < result.len() {
        match result[i].clone() {
            HelperForm::Defun(inline, defun) => {
                let context = if inline {
                    Some(defun.args.clone())
                } else {
                    None
                };
                let helper_result =
                    hoist_body_let_binding(context, defun.args.clone(), defun.body.clone())?;
                let hoisted_helpers = helper_result.0;
                let hoisted_body = helper_result.1.clone();

                result[i] = HelperForm::Defun(
                    inline,
                    DefunData {
                        body: hoisted_body,
                        ty: defun.ty.clone(),
                        ..defun.clone()
                    },
                );

                i += 1;

                for (j, hh) in hoisted_helpers.iter().enumerate() {
                    result.insert(i + j, hh.clone());
                }
            }
            _ => {
                i += 1;
            }
        }
    }

    Ok(result)
}

fn find_satisfied_functions(
    ce: &CompileForm,
    depgraph: &FunctionDependencyGraph,
    function_set: &HashSet<Vec<u8>>,
    constant_set: &HashSet<Vec<u8>>,
    functions: &[HelperForm],
) -> Vec<HelperForm> {
    functions
        .iter()
        .filter(|f| {
            let mut function_deps = HashSet::new();

            // Don't try something we already processed.
            if !function_set.contains(f.name()) {
                return false;
            }

            depgraph.get_full_depends_on(&mut function_deps, f.name());
            let uncovered_deps: Vec<Vec<u8>> = function_deps
                .iter()
                .filter(|h| {
                    let hname: &[u8] = h;
                    !(function_set.contains(hname) || constant_set.contains(hname))
                })
                .cloned()
                .collect();
            let deps_list: Vec<String> = uncovered_deps.iter().map(|d| decode_string(d)).collect();
            uncovered_deps.is_empty()
        })
        .cloned()
        .collect()
}

fn find_easiest_constant(
    ce: &CompileForm,
    depgraph: &FunctionDependencyGraph,
    constant_set: &HashSet<Vec<u8>>,
    constants: &[HelperForm],
) -> Option<HelperForm> {
    let constants_in_set: Vec<HelperForm> = constants
        .iter()
        .filter(|c| constant_set.contains(c.name()))
        .cloned()
        .collect();

    if constants_in_set.is_empty() {
        return None;
    }

    let mut chosen_idx = 0;
    let mut best_dep_set = 0;

    for (i, h) in constants_in_set.iter().enumerate() {
        let mut deps_of_constant = HashSet::new();
        depgraph.get_full_depends_on(&mut deps_of_constant, h.name());
        let how_many_deps = deps_of_constant.len();
        if i == 0 || how_many_deps < best_dep_set {
            chosen_idx = i;
            best_dep_set = how_many_deps;
        }
    }

    Some(constants_in_set[chosen_idx].clone())
}

fn find_satisfied_constants(
    depgraph: &FunctionDependencyGraph,
    function_set: &HashSet<Vec<u8>>,
    constant_set: &HashSet<Vec<u8>>,
    constants: &[HelperForm],
) -> Vec<HelperForm> {
    let constant_set_list: Vec<String> = constant_set.iter().map(|c| decode_string(c)).collect();
    constants
        .iter()
        .filter(|c| {
            let mut constant_deps = HashSet::new();

            // We've already processed it or it isn't a module style constant.
            if !constant_set.contains(c.name()) {
                return false;
            }

            depgraph.get_full_depends_on(&mut constant_deps, c.name());
            let raw_deps_list: Vec<String> = constant_deps.iter().map(|c| decode_string(c)).collect();
            let uncovered_deps: Vec<Vec<u8>> = constant_deps
                .iter()
                .filter(|h| {
                    let hname: &[u8] = h;
                    function_set.contains(hname) || constant_set.contains(hname)
                })
                .cloned()
                .collect();
            let deps_list: Vec<String> = uncovered_deps.iter().map(|d| decode_string(d)).collect();
            uncovered_deps.is_empty()
        })
        .cloned()
        .collect()
}

// Output a viable order for constant and constant-time function generation which
// allows the constants to observe a consistent, useful viewpoint on the program
// and any functions that they depend on outside the main program.
fn decide_constant_generation_order(
    loc: &Srcloc,
    compiler: &PrimaryCodegen,
    helpers: &[HelperForm],
) -> Result<Vec<HelperForm>, CompileErr> {
    let mut exp = Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone())));

    for h in helpers.iter() {
        eprintln!("decide_constant_generation_order {}", h.to_sexp());

        let do_include = match h {
            HelperForm::Defconstant(dc) => {
                eprintln!("{:?} {}", dc.kind, decode_string(&dc.name));
                matches!(dc.kind, ConstantKind::Module(false))
            }
            HelperForm::Defun(false, _) => true,
            _ => false,
        };

        if do_include {
            exp = Rc::new(BodyForm::Call(
                loc.clone(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Integer(
                        loc.clone(),
                        4_u32.to_bigint().unwrap(),
                    ))),
                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), h.name().clone()))),
                    exp,
                ],
                None,
            ));
        }
    }

    let ce = CompileForm {
        loc: loc.clone(),
        include_forms: Vec::new(),
        args: Rc::new(SExp::Nil(loc.clone())),
        helpers: helpers.to_vec(),
        exp,
        ty: None,
    };

    let mut constants: Vec<HelperForm> = helpers
        .iter()
        .filter(|h| {
            if let HelperForm::Defconstant(dc) = h {
                return matches!(dc.kind, ConstantKind::Module(true));
            }

            false
        })
        .cloned()
        .collect();
    let mut constant_set: HashSet<Vec<u8>> = constants.iter().map(|h| h.name().to_vec()).collect();
    let mut functions: Vec<HelperForm> = helpers
        .iter()
        .filter(|h| matches!(h, HelperForm::Defun(false, dd)))
        .cloned()
        .collect();

    // We don't generate bodies for inline helpers, but they appear pre-fulfilled
    // in our function set.
    let mut function_set: HashSet<Vec<u8>> = helpers
        .iter()
        .filter(|h| matches!(h, HelperForm::Defun(_, _)))
        .map(|h| h.name().to_vec())
        .collect();

    let depgraph = FunctionDependencyGraph::new_with_options(
        &ce,
        DepgraphOptions {
            with_constants: true,
        },
    );

    let mut result = Vec::new();

    while !constant_set.is_empty() {
        let remaining_constants: Vec<String> = constant_set.iter().map(|c| decode_string(c)).collect();
        let new_satisfied_constants =
            find_satisfied_constants(&depgraph, &function_set, &constant_set, &constants);
        let new_satcon: Vec<String> = new_satisfied_constants.iter().map(|c| decode_string(c.name())).collect();

        if !new_satisfied_constants.is_empty() {
            for c in new_satisfied_constants.iter() {
                constant_set.remove(c.name());
                result.push(c.clone());
            }
            continue;
        }

        let new_satisfied_functions =
            find_satisfied_functions(&ce, &depgraph, &function_set, &constant_set, &functions);
        if !new_satisfied_functions.is_empty() {
            for f in new_satisfied_functions.iter() {
                function_set.remove(f.name());
                result.push(f.clone());
            }
            continue;
        }

        // Break blocks.  We need to unblock a constant so we'll choose the easiest
        // one generate any functions it needs which we haven't generated yet.
        if let Some(least_constant) =
            find_easiest_constant(&ce, &depgraph, &constant_set, &constants)
        {
            let mut functions_it_depends_on_hash = HashSet::new();
            depgraph.get_full_depends_on(&mut functions_it_depends_on_hash, least_constant.name());
            let mut functions_it_depends_on = functions
                .iter()
                .filter(|h| functions_it_depends_on_hash.contains(h.name()))
                .cloned()
                .collect();
            constant_set.remove(least_constant.name());
            result.append(&mut functions_it_depends_on);
            result.push(least_constant.clone());
            continue;
        }

        let mod_constant_names: Vec<String> =
            constants.iter().map(|h| decode_string(h.name())).collect();
        return Err(CompileErr(
            loc.clone(),
            format!("Deadlock generating module constants {mod_constant_names:?}"),
        ));
    }

    let result_order: Vec<String> = result.iter().map(|h| decode_string(h.name())).collect();

    Ok(result)
}

fn generate_helper_body(
    context: &mut BasicCompileContext,
    code_generator: PrimaryCodegen,
    opts: Rc<dyn CompilerOpts>,
    program: CompileForm,
    h: &HelperForm,
) -> Result<PrimaryCodegen, CompileErr> {
    match h {
        HelperForm::Defconstant(defc) => match defc.kind {
            ConstantKind::Simple => {
                let expand_program = SExp::Cons(
                    defc.loc.clone(),
                    Rc::new(SExp::Atom(defc.loc.clone(), "mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        defc.loc.clone(),
                        Rc::new(SExp::Nil(defc.loc.clone())),
                        Rc::new(SExp::Cons(
                            defc.loc.clone(),
                            Rc::new(primquote(defc.loc.clone(), defc.body.to_sexp())),
                            Rc::new(SExp::Nil(defc.loc.clone())),
                        )),
                    )),
                );
                let updated_opts = opts.set_code_generator(code_generator.clone()).set_module_phase(None);
                let mut unused_symbols = HashMap::new();
                let runner = context.runner();
                let mut context_wrapper =
                    CompileContextWrapper::from_context(context, &mut unused_symbols);
                let code = match updated_opts
                    .compile_program(&mut context_wrapper.context, Rc::new(expand_program))?
                {
                    CompilerOutput::Program(_, code) => code,
                    CompilerOutput::Module(_) => {
                        todo!();
                    }
                };

                run(
                    context_wrapper.context.allocator(),
                    runner,
                    opts.prim_map(),
                    Rc::new(code),
                    Rc::new(SExp::Nil(defc.loc.clone())),
                    None,
                    Some(CONST_EVAL_LIMIT),
                )
                    .map_err(|r| {
                        CompileErr(defc.loc.clone(), format!("Error evaluating constant: {r}"))
                    })
                    .and_then(|res| {
                        fail_if_present(
                            defc.loc.clone(),
                            &code_generator.constants,
                            &defc.name,
                            res,
                        )
                    })
                    .map(|res| {
                        if defc.tabled {
                            Ok(code_generator.add_tabled_constant(&defc.name, res))
                        } else {
                            let quoted = primquote(defc.loc.clone(), res);
                            Ok(code_generator.add_constant(&defc.name, Rc::new(quoted)))
                        }
                    })?
            }
            ConstantKind::Complex => {
                eprintln!("evaluate code for constant {}: {}", decode_string(&defc.name), defc.body.to_sexp());
                let evaluator =
                    Evaluator::new(opts.set_module_phase(None), context.runner(), program.helpers.clone());
                let constant_result = evaluator.shrink_bodyform(
                    context.allocator(),
                    Rc::new(SExp::Nil(defc.loc.clone())),
                    &HashMap::new(),
                    defc.body.clone(),
                    false,
                    Some(EVAL_STACK_LIMIT),
                )?;
                if let BodyForm::Quoted(q) = constant_result.borrow() {
                    let res = Rc::new(q.clone());
                    if defc.tabled {
                        Ok(code_generator.add_tabled_constant(&defc.name, res))
                    } else {
                        let quoted = primquote(defc.loc.clone(), res);
                        Ok(code_generator.add_constant(&defc.name, Rc::new(quoted)))
                    }
                } else {
                    return Err(CompileErr(
                        defc.loc.clone(),
                        format!(
                            "constant definition didn't reduce to constant value {}, got {}",
                            h.to_sexp(),
                            constant_result.to_sexp()
                        ),
                    ));
                }
            }
            ConstantKind::Module(_) => {
                eprintln!("do module constants {}", h.to_sexp());
                let constant_program = CompileForm {
                    helpers: program.helpers.iter().filter(|other| {
                        other.name() != h.name()
                    }).cloned().collect(),
                    exp: defc.body.clone(),
                    .. program.clone()
                };
                let updated_opts = opts.set_code_generator(code_generator.clone());
                let mut unused_symbols = HashMap::new();
                let runner = context.runner();
                let mut context_wrapper =
                    CompileContextWrapper::from_context(context, &mut unused_symbols);
                let code = compile_from_compileform(&mut context_wrapper.context, updated_opts.clone(), constant_program)?;
                eprintln!("evaluate constant code for {}: {}", decode_string(h.name()), code);

                run(
                    context_wrapper.context.allocator(),
                    runner,
                    opts.prim_map(),
                    Rc::new(code),
                    Rc::new(SExp::Nil(defc.loc.clone())),
                    None,
                    Some(CONST_EVAL_LIMIT),
                )
                    .map_err(|r| {
                        CompileErr(defc.loc.clone(), format!("Error evaluating constant: {r}"))
                    })
                    .map(|res| {
                        if defc.tabled {
                            Ok(code_generator.add_tabled_constant(&defc.name, res))
                        } else {
                            let quoted = primquote(defc.loc.clone(), res);
                            Ok(code_generator.add_constant(&defc.name, Rc::new(quoted)))
                        }
                    })?
            }
            /*
            ConstantKind::Module(false) => {
                todo!();
            }
            */
        },
        HelperForm::Defmacro(mac) => {
            let macro_program = Rc::new(SExp::Cons(
                mac.loc.clone(),
                Rc::new(SExp::Atom(mac.loc.clone(), "mod".as_bytes().to_vec())),
                mac.program.to_sexp(),
            ));

            let updated_opts = opts
                .set_code_generator(code_generator.clone())
                .set_in_defun(false)
                .set_stdenv(false)
                .set_start_env(None)
                .set_module_phase(None)
                .set_frontend_opt(false);

            let mut unused_symbols = HashMap::new();
            let mut context_wrapper =
                CompileContextWrapper::from_context(context, &mut unused_symbols);
            let code = match updated_opts
                .compile_program(&mut context_wrapper.context, macro_program)?
            {
                CompilerOutput::Program(_, p) => p,
                CompilerOutput::Module(_) => {
                    todo!();
                }
            };

            let optimized_code = context_wrapper
                .context
                .macro_optimization(opts.clone(), Rc::new(code.clone()))?;

            Ok(code_generator.add_macro(&mac.name, optimized_code))
        }
        _ => Ok(code_generator),
    }
}

fn start_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    program: CompileForm,
) -> Result<PrimaryCodegen, CompileErr> {
    // Choose code generator configuration
    let mut code_generator = match opts.code_generator() {
        None => empty_compiler(opts.prim_map(), program.loc.clone()),
        Some(c) => c,
    };

    if code_generator.module_phase.is_none() {
        code_generator.module_phase = opts.module_phase();
    }

    let mut processed_helpers = HashSet::new();

    eprintln!("start_codegen: module_phase = {:?}", code_generator.module_phase);
    if let Some(ModulePhase::CommonPhase) = code_generator.module_phase.as_ref() {
        let generation_order = decide_constant_generation_order(
            &program.loc,
            &code_generator,
            &code_generator.original_helpers)?;

        let generation_order_strings: Vec<String> = generation_order.iter().map(|h| decode_string(h.name())).collect();
        eprintln!("generation_order {generation_order_strings:?}");

        // Pre-generate nils for all module constants.
        for h in program.helpers.iter() {
            let nil_value = Rc::new(BodyForm::Value(SExp::Nil(h.loc())));
            if let HelperForm::Defconstant(dc) = h {
                if matches!(dc.kind, ConstantKind::Module(_)) {
                    let new_const = HelperForm::Defconstant(DefconstData {
                        body: nil_value,
                        .. dc.clone()
                    });
                    eprintln!("make dummy nil for {}", h.to_sexp());
                    code_generator = generate_helper_body(
                        context,
                        code_generator,
                        opts.clone(),
                        program.clone(),
                        &new_const
                    )?;
                }
            }
        }

        // Generate constants in our target order.
        for h in generation_order.iter() {
            eprintln!("generate constant {}", h.to_sexp());
            processed_helpers.insert(h.name().to_vec());
            code_generator = generate_helper_body(
                context,
                code_generator,
                opts.clone(),
                program.clone(),
                h
            )?;
        }
    };

    // Generate the bodies of classic style constants and macros.
    for h in program.helpers.iter() {
        if processed_helpers.contains(h.name()) {
            continue;
        }

        code_generator = generate_helper_body(
            context,
            code_generator,
            opts.clone(),
            program.clone(),
            h
        )?;
    }

    let only_defuns: Vec<HelperForm> = program
        .helpers
        .iter()
        .filter(|x| is_defun_or_tabled_const(x))
        .cloned()
        .collect();

    let only_defuns_list: Vec<String> = only_defuns.iter().map(|h| h.to_sexp().to_string()).collect();
    eprintln!("about to compute env shape with helpers: {only_defuns_list:?}");

    code_generator.env = match opts.start_env() {
        Some(env) => env,
        None => Rc::new(compute_env_shape(
            code_generator.module_phase.as_ref(),
            program.loc.clone(),
            program.args,
            &only_defuns,
        )),
    };

    eprintln!("phase {:?}", code_generator.module_phase.as_ref());
    eprintln!("env {}", code_generator.env);

    code_generator.to_process = program.helpers.clone();
    // Ensure that we have the synthesis of the previous codegen's helpers and
    // The ones provided with the new form if any.
    let mut combined_helpers_for_codegen = program.helpers.clone();
    combined_helpers_for_codegen.append(&mut code_generator.original_helpers);
    code_generator.original_helpers = combined_helpers_for_codegen;
    code_generator.final_expr = program.exp;

    Ok(code_generator)
}

fn final_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
) -> Result<PrimaryCodegen, CompileErr> {
    let opt_final_expr = context.pre_final_codegen_optimize(opts.clone(), compiler)?;
    let optimizer_opts = opts.clone();
    generate_expr_code(context, opts, compiler, opt_final_expr).and_then(|code| {
        let mut final_comp = compiler.clone();
        let optimized_code =
            context.post_codegen_function_optimize(optimizer_opts.clone(), None, code.1.clone())?;
        final_comp.final_code = Some(CompiledCode(code.0, optimized_code));
        Ok(final_comp)
    })
}

fn get_env_data_from_common_env(
    name: &[u8],
    common_env: Rc<SExp>,
    common_env_value: Rc<SExp>
) -> Option<Rc<SExp>> {
    eprintln!("get env data {} {common_env} {common_env_value}", decode_string(name));
    if let (SExp::Cons(_, le, re), SExp::Cons(_, lv, rv)) = (common_env.borrow(), common_env_value.borrow()) {
        if let Some(l) = get_env_data_from_common_env(name, le.clone(), lv.clone()) {
            return Some(l);
        }

        if let Some(r) = get_env_data_from_common_env(name, re.clone(), rv.clone()) {
            return Some(r);
        }
    }

    if let SExp::Atom(_, match_name) = common_env.borrow() {
        if match_name == name {
            return Some(common_env_value);
        }
    }

    None
}

fn finalize_env_(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
    _l: Srcloc,
    env: Rc<SExp>,
) -> Result<Rc<SExp>, CompileErr> {
    match env.borrow() {
        SExp::Atom(l, v) => {
            if let Some(res) = c.defuns.get(v) {
                return Ok(res.code.clone());
            }

            if let Some(res) = c.tabled_constants.get(v) {
                return Ok(res.clone());
            }

            if let Some(res) = c.inlines.get(v) {
                let (arg_list, arg_tail) = synthesize_args(res.args.clone());
                return replace_in_inline(
                    context,
                    opts.clone(),
                    c,
                    l.clone(),
                    res,
                    res.args.loc(),
                    &arg_list,
                    arg_tail,
                )
                .map(|x| x.1);
            }

            /* Parentfns are functions in progress in the parent */
            if c.parentfns.get(v).is_some() {
                return Ok(Rc::new(SExp::Nil(l.clone())));
            }

            if let Some(ModulePhase::StandalonePhase(sp)) = c.module_phase.as_ref() {
                eprintln!("Standalone mode: {}", sp.env);
                let wrapped_env_value = Rc::new(SExp::Cons(sp.left_env_value.loc(), sp.left_env_value.clone(), Rc::new(SExp::Nil(sp.left_env_value.loc()))));
                if let Some(res) = get_env_data_from_common_env(v, sp.env.clone(), wrapped_env_value.clone()) {
                    eprintln!("get_env_data: {} => {res}", decode_string(v));
                    return Ok(res);
                }
                eprintln!("standalone: failed to lookup {} in {env} with values {}", decode_string(v), sp.left_env_value);
            }

            todo!();
            Err(CompileErr(
                l.clone(),
                format!(
                    "A defun was referenced in the defun env but not found {}",
                    decode_string(v)
                ),
            ))
        }

        SExp::Cons(l, h, r) => finalize_env_(context, opts.clone(), c, l.clone(), h.clone())
            .and_then(|h| {
                finalize_env_(context, opts.clone(), c, l.clone(), r.clone())
                    .map(|r| Rc::new(SExp::Cons(l.clone(), h.clone(), r)))
            }),

        _ => Ok(env.clone()),
    }
}

fn finalize_env(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
) -> Result<Rc<SExp>, CompileErr> {
    match c.env.borrow() {
        SExp::Cons(l, h, _) => {
            if c.left_env {
                finalize_env_(context, opts.clone(), c, l.clone(), h.clone())
            } else {
                Ok(c.env.clone())
            }
        }
        _ => Ok(c.env.clone()),
    }
}

fn dummy_functions(compiler: &PrimaryCodegen) -> Result<PrimaryCodegen, CompileErr> {
    fold_m(
        &|compiler: &PrimaryCodegen, form: &HelperForm| match form {
            HelperForm::Defun(false, defun) => {
                let mut c_copy = compiler.clone();
                c_copy.parentfns.insert(defun.name.clone());
                Ok(c_copy)
            }
            HelperForm::Defun(true, defun) => Ok(compiler)
                .and_then(|comp| {
                    fail_if_present(defun.loc.clone(), &compiler.inlines, &defun.name, comp)
                })
                .and_then(|comp| {
                    fail_if_present(defun.loc.clone(), &compiler.defuns, &defun.name, comp)
                })
                .map(|comp| {
                    comp.add_inline(
                        &defun.name,
                        &InlineFunction {
                            name: defun.name.clone(),
                            args: defun.args.clone(),
                            body: defun.body.clone(),
                        },
                    )
                }),
            HelperForm::Defconstant(cdata) => {
                if cdata.tabled {
                    let mut c_copy = compiler.clone();
                    c_copy.parentfns.insert(cdata.name.clone());
                    Ok(c_copy)
                } else {
                    Ok(compiler.clone())
                }
            }
            _ => Ok(compiler.clone()),
        },
        compiler.clone(),
        &compiler.to_process,
    )
}

fn do_start_codegen_optimization_and_dead_code_elimination(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    mut start_of_codegen_optimization: StartOfCodegenOptimization,
) -> Result<StartOfCodegenOptimization, CompileErr> {
    // This is a tree-shaking loop.  It results in the minimum number of emitted
    // helpers in the environment by taking only those still alive after each
    // optimization pass.  If a function is constant at all call sites, then
    // then the function will be constant reduced and won't appear when we do
    // the live calculation again, which can also remove the last reference to
    // other helpers.
    loop {
        // We should not modify the environment if we're here on behalf of a
        // function in a program, only the toplevel program itself.
        if opts.in_defun() {
            break;
        }

        let newly_optimized_start = context
            .start_of_codegen_optimization(opts.clone(), start_of_codegen_optimization.clone())?;

        // We got back the same program, so nothing will change anymore.
        if newly_optimized_start.program.to_sexp()
            == start_of_codegen_optimization.program.to_sexp()
        {
            break;
        }

        // Reset the optimization struct so we can go again.
        // The maximum number of iterations should be about (N+1) * M where N is
        // the number of functions and M is the largest number of parameters in
        // any called function or operator.
        let program = newly_optimized_start.program;
        start_of_codegen_optimization = StartOfCodegenOptimization {
            program: program.clone(),
            code_generator: dummy_functions(&start_codegen(context, opts.clone(), program)?)?,
        };
    }

    Ok(start_of_codegen_optimization)
}

fn collect_env_names(env: Rc<SExp>) -> Vec<Rc<SExp>> {
    let mut result = Vec::new();
    let mut stack = Vec::new();
    stack.push(env);
    while let Some(e) = stack.pop() {
        match e.borrow() {
            SExp::Cons(_, a, b) => {
                stack.push(a.clone());
                stack.push(b.clone());
            }
            SExp::Atom(_, n) => {
                result.push(e.clone());
            }
            _ => { }
        }
    }
    result
}

fn make_env_tree(loc: &Srcloc, env: &[Rc<SExp>], start: usize, end: usize) -> Rc<SExp> {
    if start + 1 > end {
        Rc::new(SExp::Nil(loc.clone()))
    } else if start + 1 == end {
        env[start].clone()
    } else {
        let mid = (start + end) / 2;
        let left = make_env_tree(loc, env, start, mid);
        let right = make_env_tree(loc, env, mid, end);
        Rc::new(SExp::Cons(loc.clone(), left, right))
    }
}

pub fn codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    cmod: &CompileForm,
) -> Result<SExp, CompileErr> {
    let mut start_of_codegen_optimization = StartOfCodegenOptimization {
        program: cmod.clone(),
        code_generator: dummy_functions(&start_codegen(context, opts.clone(), cmod.clone())?)?,
    };

    start_of_codegen_optimization = do_start_codegen_optimization_and_dead_code_elimination(context, opts.clone(), start_of_codegen_optimization)?;

    let mut code_generator = start_of_codegen_optimization.code_generator;
    let to_process = code_generator.to_process.clone();

    for f in to_process {
        code_generator = codegen_(context, opts.clone(), &code_generator, &f)?;
    }

    // If stepping 23 or greater, we support no-env mode.
    enable_nil_env_mode_for_stepping_23_or_greater(opts.clone(), &mut code_generator);

    *context.symbols() = code_generator.function_symbols.clone();
    context
        .symbols()
        .insert("source_file".to_string(), opts.filename());

    let mut c = final_codegen(context, opts.clone(), &code_generator)?;
    let final_env = finalize_env(context, opts.clone(), &c)?;
    c.final_env = final_env.clone();

    let normal_produce_code = |code: CompiledCode| {
        // Capture symbols now that we have the final form of the produced code.
        context
            .symbols()
            .insert("__chia__main_arguments".to_string(), cmod.args.to_string());

        if opts.in_defun() {
            let final_code = primapply(
                code.0.clone(),
                Rc::new(primquote(code.0.clone(), code.1)),
                Rc::new(SExp::Integer(code.0, bi_one())),
            );

            final_code
        } else if code_generator.left_env {
            let final_code = primapply(
                code.0.clone(),
                Rc::new(primquote(code.0.clone(), code.1)),
                Rc::new(primcons(
                    code.0.clone(),
                    Rc::new(primquote(code.0.clone(), final_env)),
                    Rc::new(SExp::Integer(code.0, bi_one())),
                )),
            );
            final_code
        } else {
            let code_borrowed: &SExp = code.1.borrow();
            code_borrowed.clone()
        }
    };

    eprintln!("code generation {:?} {:?}", opts.in_defun(), opts.module_phase());
    match (opts.in_defun(), opts.module_phase(), c.final_code) {
        (_, _, None) => Err(CompileErr(
            Srcloc::start(&opts.filename()),
            "Failed to generate code".to_string(),
        )),
        (true, _, Some(code)) => {
            Ok(normal_produce_code(code))
        }
        (_, None, Some(code)) => {
            Ok(normal_produce_code(code))
        }
        (false, Some(ModulePhase::CommonPhase), Some(code)) => {
            // Produce a triple of env shape, env, output code
            eprintln!("common phase env {}", c.env);
            eprintln!("final_env {}", c.final_env);
            Ok(SExp::Cons(
                c.env.loc(),
                c.env.clone(),
                Rc::new(SExp::Cons(
                    c.final_env.loc(),
                    c.final_env.clone(),
                    Rc::new(SExp::Cons(
                        code.1.loc(),
                        Rc::new(normal_produce_code(code.clone())),
                        Rc::new(SExp::Nil(code.0.clone()))
                    ))
                ))
            ))
        }
        (false, Some(ModulePhase::StandalonePhase(_)), Some(code)) => {
            // The program generates one constant or function.
            Ok(normal_produce_code(code))
        }
    }
}
