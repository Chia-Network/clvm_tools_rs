use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::mem::swap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};

use crate::compiler::clvm::{run, truthy};
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    fold_m, join_vecs_to_string, list_to_cons, Binding, BindingPattern, BodyForm, CallSpec,
    Callable, CompileErr, CompileForm, CompiledCode, CompilerOpts, CompilerOutput, ConstantKind,
    DefconstData, DefunCall, DefunData, HelperForm, InlineFunction, LetData, LetFormInlineHint, LetFormKind,
    PrimaryCodegen, ProgramEnvData, RawCallSpec, SyntheticType,
};
use crate::compiler::debug::{build_swap_table_mut, relabel};
use crate::compiler::evaluate::{Evaluator, EVAL_STACK_LIMIT};
use crate::compiler::frontend::{compile_bodyform, make_provides_set};
use crate::compiler::gensym::gensym;
use crate::compiler::inline::{replace_in_inline, synthesize_args};
use crate::compiler::lambda::lambda_codegen;
use crate::compiler::optimize::depgraph::{FunctionDependencyGraph, DepgraphOptions};
use crate::compiler::prims::{primapply, primcons, primquote};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, printable, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::StartOfCodegenOptimization;
use crate::compiler::{BasicCompileContext, CompileContextWrapper};
use crate::util::{toposort, u8_from_number, Number, TopoSortItem};

const MACRO_TIME_LIMIT: usize = 1000000;
pub const CONST_EVAL_LIMIT: usize = 1000000;
const CONSTANT_GENERATIONS_ALLOWED: usize = 50;

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

fn compute_env_shape(l: Srcloc, args: Rc<SExp>, helpers: &[HelperForm]) -> SExp {
    let car = compute_code_shape(l.clone(), helpers);
    let cdr = args;
    SExp::Cons(l, Rc::new(car), cdr)
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
        _ => {
            Err(CompileErr(
                l,
                format!(
                    "operator or function atom {} not found",
                    decode_string(name),
                ),
            ))
        }
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
// (list (q . 2) (c (q . 1) n) (list (q . 4) (c (q . 1) 2) (q . 1)))
//
// Something like:
//   (apply (quoted (expanded n)) (cons (quoted (expanded 2)) given-args))
//
fn lambda_for_defun(loc: Srcloc, lookup: Rc<SExp>) -> Rc<SExp> {
    let one_atom = Rc::new(SExp::Atom(loc.clone(), vec![1]));
    let two_atom = Rc::new(SExp::Atom(loc.clone(), vec![2]));
    let apply_atom = two_atom.clone();
    let cons_atom = Rc::new(SExp::Atom(loc.clone(), vec![4]));
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
                        two_atom,
                    )),
                    Rc::new(primquote(loc, one_atom)),
                ],
            ),
        ],
    )
}

#[deprecated]
fn module_lambda_for_defun(loc: Srcloc, lookup: Rc<SExp>) -> Rc<SExp> {
    lambda_for_defun(loc, lookup)
}

fn create_name_lookup(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &[u8],
    as_variable: bool,
) -> Result<Rc<SExp>, CompileErr> {
    if let Some(x) = compiler
        .constants
        .get(name)
    {
        return Ok(x.clone())
    }

    create_name_lookup_(l.clone(), name, compiler.env.clone(), compiler.env.clone()).map(|i| {
        // Determine if it's a defun.  If so we can ensure that it's
        // callable like a lambda by repeating the left env into it.
        let find_program = Rc::new(SExp::Integer(l.clone(), i.to_bigint().unwrap()));
        if as_variable && is_defun_in_codegen(compiler, name) {
            if !compiler.module_constants.is_empty() {
                module_lambda_for_defun(l.clone(), find_program)
            } else {
                lambda_for_defun(l.clone(), find_program)
            }
        } else {
            find_program
        }
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
    _opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    atom: Rc<SExp>,
) -> Result<Callable, CompileErr> {
    match atom.borrow() {
        SExp::Atom(l, name) => {
            let macro_def = compiler.macros.get(name);
            let inline = compiler.inlines.get(name);
            let defun = create_name_lookup(compiler, l.clone(), name, false);
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
                _ => {
                    let orig_helper_names: Vec<String> = compiler.original_helpers.iter().map(|h| decode_string(h.name())).collect();
                    let to_process_names: Vec<String> = compiler.to_process.iter().map(|h| decode_string(h.name())).collect();
                    todo!();
                    Err(CompileErr(
                        l.clone(),
                        format!("no such callable '{}'", decode_string(name)),
                    ))
                }
            }
        }
        SExp::Integer(_, v) => Ok(Callable::CallPrim(l.clone(), SExp::Integer(l, v.clone()))),
        _ => Err(CompileErr(atom.loc(), format!("can't call object {atom}"))),
    }
}

fn run_failure_to_compile_err(l: Srcloc, e: &RunFailure) -> CompileErr {
    match e {
        RunFailure::RunExn(ml, x) => CompileErr(l, format!("macro aborted at {ml} with {x}")),
        RunFailure::RunErr(rl, e) => CompileErr(l, format!("error executing macro: {rl} {e}")),
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
    .map_err(|e| run_failure_to_compile_err(l, &e))
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
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    a: &[u8],
    mut steps: Number,
) -> Result<CompiledCode, CompileErr> {
    if let Ok(SExp::Integer(l, mut lookup)) = create_name_lookup(compiler, loc.clone(), a, true)
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
                            ) => produce_argument_check(compiler, call.loc.clone(), a, i.clone()),
                            (
                                BodyForm::Value(SExp::Atom(_al, a)),
                                BodyForm::Quoted(SExp::Integer(_il, i)),
                            ) => produce_argument_check(compiler, call.loc.clone(), a, i.clone()),
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
    let without_env = opts.set_start_env(None).set_in_defun(false);
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

#[deprecated]
pub fn generate_constant_expr_code(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    expr: Rc<BodyForm>,
    atom: &[u8],
) -> Result<CompiledCode, CompileErr> {
    if let Some(_) = compiler.tabled_constants.get(atom) {
        let target_select = create_name_lookup(
            compiler,
            expr.loc(),
            atom,
            true,
        )?;
        return Ok(CompiledCode(expr.loc(), target_select));
    }

    generate_expr_code(context, opts, compiler, expr)
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
                        if let Some(mconstant) = compiler
                            .module_constants
                            .get(atom)
                        {
                            // If we get here, we have a standalone module style constant which
                            // observes the full environment.  It does not exist _in_ the environment
                            // because nothing but the exports depend on it.
                            return generate_constant_expr_code(
                                context,
                                opts.clone(),
                                compiler,
                                mconstant.clone(),
                                atom,
                            );
                        }

                        create_name_lookup(compiler, l.clone(), atom, true)
                            .map(|f| Ok(CompiledCode(l.clone(), f)))
                            .unwrap_or_else(|_| {
                                if opts.dialect().strict && printable(atom, false) {
                                    if let Some(c) = compiler.module_constants.get(atom) {
                                        todo!();
                                    }

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

fn codegen_defun(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    h: &HelperForm,
    defun: &DefunData,
) -> Result<Rc<SExp>, CompileErr> {
    let updated_opts = opts
        .set_code_generator(compiler.clone())
        .set_in_defun(true)
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
        let code =
            updated_opts.compile_program(&mut context_wrapper.context, Rc::new(tocompile))?;
        match code {
            CompilerOutput::Program(_, p) => p,
            CompilerOutput::Module(_) => {
                todo!();
            }
        }
    };

    context.post_codegen_function_optimize(opts.clone(), Some(h), Rc::new(code))
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
                let code = codegen_defun(context, opts.clone(), compiler, h, defun)?;
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
        final_env: ProgramEnvData::Simple(nil_rc),
        function_symbols: HashMap::new(),
        left_env: true,
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

// True if the name appears in the env shape specified.
fn name_in_env(env: Rc<SExp>, name: &[u8]) -> bool {
    match env.borrow() {
        SExp::Cons(_, a, b) => name_in_env(a.clone(), name) || name_in_env(b.clone(), name),
        SExp::Atom(_, n) => n == name,
        _ => false,
    }
}

// Ensure that the environment data at __chia__extras becomes nil.
fn purge_chia_extras(compiler: &mut PrimaryCodegen, orig_env: Rc<SExp>) {
    let source_env = compiler.final_env.to_sexp();
    if let Some((chia_extras_path, old_val)) =
        find_named_path(orig_env, b"__chia__extras", bi_one(), bi_zero())
    {
        compiler.final_env = ProgramEnvData::Module(
            chia_extras_path.clone(),
            replace_by_paths(
                source_env,
                &[(chia_extras_path >> 1, Rc::new(SExp::Nil(old_val.loc())))],
            )
        )
    } else {
        todo!();
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
                        ..defun.clone()
                    },
                );

                i += 1;

                for (j, hh) in hoisted_helpers.iter().enumerate() {
                    result.insert(i + j, hh.clone());
                }
            }
            HelperForm::Defconstant(defconst) => {
                if matches!(defconst.kind, ConstantKind::Module(_)) {
                    let helper_result =
                        hoist_body_let_binding(None, Rc::new(SExp::Nil(defconst.loc.clone())), defconst.body.clone())?;
                    let hoisted_helpers = helper_result.0;
                    let hoisted_body = helper_result.1.clone();
                    result[i] = HelperForm::Defconstant(DefconstData {
                        body: hoisted_body,
                        ..defconst.clone()
                    });

                    i += 1;

                    for (j, hh) in hoisted_helpers.iter().enumerate() {
                        result.insert(i + j, hh.clone());
                    }
                } else {
                    i += 1;
                }
            }
            _ => {
                i += 1;
            }
        }
    }

    Ok(result)
}

// Given a function to generate as a freestanding program, compile the program
// using compile_from_helperform and install it in the compiler's notion of
// __chia__extras.  Functions may be generated in any order but only after all
// constants depended upon by every function dependency of to_generate has been
// produced.  If the order can't be determined, then we must fail.
fn generate_function_body_for_constants(
    context: &mut BasicCompileContext,
    compiler: &mut PrimaryCodegen,
    opts: Rc<dyn CompilerOpts>,
    to_generate: &DefunData,
) -> Result<(), CompileErr> {
    let opts = opts.set_optimize(true);
    todo!();
}

fn show_variables_in_env(env: Rc<SExp>, data: Rc<SExp>) -> Rc<SExp> {
    if let (SExp::Cons(l, a, b), SExp::Cons(_, c, d)) = (env.borrow(), data.borrow()) {
        let new_a = show_variables_in_env(a.clone(), c.clone());
        let new_b = show_variables_in_env(b.clone(), d.clone());
        Rc::new(SExp::Cons(env.loc(), new_a, new_b))
    } else {
        Rc::new(SExp::Cons(
            env.loc(),
            env.clone(),
            data.clone()
        ))
    }
}

// Given a constant to generate, generate its program given the compiler's current
// environment and then run the program given the current environment value.  The
// result is a constant that consistently observes the post-optimization full
// program if every function and constant it relies on is generated.  If the
// order can't be solved then we must fail.
fn generate_constant_body_for_constants(
    context: &mut BasicCompileContext,
    compiler: &mut PrimaryCodegen,
    opts: Rc<dyn CompilerOpts>,
    tabled: bool,
    to_generate: &DefconstData,
) -> Result<(), CompileErr> {
    let opts = opts.set_optimize(true);
    let args = Rc::new(SExp::Nil(to_generate.loc.clone()));
    let defun_data = DefunData {
        loc: to_generate.loc.clone(),
        kw: to_generate.kw.clone(),
        nl: to_generate.nl.clone(),
        name: to_generate.name.clone(),
        args: args.clone(),
        orig_args: args.clone(),
        synthetic: Some(SyntheticType::WantNonInline),
        body: to_generate.body.clone(),
        ty: None,
    };
    let generate_value_function = HelperForm::Defun(false, defun_data.clone());
    let generated_code = codegen_defun(
        context,
        opts.clone(),
        compiler,
        &generate_value_function,
        &defun_data,
    )?;
    let runner = context.runner();
    let whole_env = Rc::new(SExp::Cons(
        to_generate.loc.clone(),
        compiler.final_env.to_sexp(),
        args.clone(),
    ));
    let run_result = run(
        context.allocator(),
        runner,
        opts.prim_map(),
        generated_code.clone(),
        // Pass program's environment plus what's been generated.
        // It's expected because we did a function style generation.
        whole_env,
        None,
        Some(MACRO_TIME_LIMIT),
    )
        .map_err(|e| {
            run_failure_to_compile_err(to_generate.loc.clone(), &e)
        })?;

    // eprintln!("generate {tabled} {} => {run_result}", decode_string(&to_generate.name));

    if tabled {
        compiler
            .tabled_constants
            .insert(to_generate.name.clone(), run_result.clone());
    }
    if let Some((cpath, _)) = find_named_path(compiler.env.clone(), &to_generate.name, bi_one(), bi_zero()) {
        if let ProgramEnvData::Module(path_to_constants, _) = &compiler.final_env {
            let orig_final_env = compiler.final_env.to_sexp();
            compiler.final_env = ProgramEnvData::Module(
                path_to_constants.clone(),
                replace_by_paths(
                    compiler.final_env.to_sexp(),
                    &[(cpath >> 1, run_result.clone())],
                )
            );
            //eprintln!("place {}\n{run_result}", decode_string(&to_generate.name));
            // eprintln!("into\n{orig_final_env}");
            // eprintln!("giving\n{}", compiler.final_env);
        } else {
            todo!();
        }
    } else {
        todo!();
    }

    Ok(())
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

fn find_named_path(
    env: Rc<SExp>,
    name: &[u8],
    mask: Number,
    parent: Number,
) -> Option<(Number, Rc<SExp>)> {
    let this_path = mask.clone() | parent.clone();
    match env.borrow() {
        SExp::Cons(_, a, b) => {
            let next_mask = mask * 2_u32.to_bigint().unwrap();
            if let Some((found_path, found_env)) =
                find_named_path(a.clone(), name, next_mask.clone(), parent)
            {
                return Some((found_path, found_env));
            }
            if let Some((found_path, found_env)) =
                find_named_path(b.clone(), name, next_mask, this_path)
            {
                return Some((found_path, found_env));
            }

            None
        }
        SExp::Atom(_, a) => {
            if a == name {
                return Some((this_path, env));
            }

            None
        }

        _ => None,
    }
}

fn replace_by_path(
    env: Rc<SExp>,
    target: Number,
    new_value: Rc<SExp>
) -> Rc<SExp> {
    if target == bi_zero() {
        env
    } else if target == bi_one() {
        new_value
    } else {
        if let SExp::Cons(l, a, b) = env.borrow() {
            let odd = (target.clone() & bi_one()) == bi_one();
            let next = target >> 1;
            if odd {
                return Rc::new(SExp::Cons(l.clone(), a.clone(), replace_by_path(b.clone(), next, new_value)));
            } else {
                return Rc::new(SExp::Cons(l.clone(), replace_by_path(a.clone(), next, new_value), b.clone()));
            }
        }

        env
    }
}

fn replace_by_paths(
    mut env: Rc<SExp>,
    collection: &[(Number, Rc<SExp>)],
) -> Rc<SExp> {
    for (p, v) in collection.iter() {
        env = replace_by_path(env, p.clone(), v.clone());
    }
    env
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
        let do_include = match h {
            HelperForm::Defconstant(dc) => {
                matches!(dc.kind, ConstantKind::Module(true))
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

fn start_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    mut program: CompileForm,
) -> Result<PrimaryCodegen, CompileErr> {

    // Choose code generator configuration
    let mut code_generator = match opts.code_generator() {
        None => empty_compiler(opts.prim_map(), program.loc.clone()),
        Some(c) => c,
    };

    // Start compiler with all macros and constants
    for h in program.helpers.iter() {
        code_generator = match h {
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
                    let updated_opts = opts.set_code_generator(code_generator.clone());
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
                            code_generator.add_tabled_constant(&defc.name, res)
                        } else {
                            let quoted = primquote(defc.loc.clone(), res);
                            code_generator.add_constant(&defc.name, Rc::new(quoted))
                        }
                    })?
                }
                ConstantKind::Complex => {
                    let evaluator =
                        Evaluator::new(opts.clone(), context.runner(), program.helpers.clone());
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
                            code_generator.add_tabled_constant(&defc.name, res)
                        } else {
                            let quoted = primquote(defc.loc.clone(), res);
                            code_generator.add_constant(&defc.name, Rc::new(quoted))
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
                ConstantKind::Module(tabled) => {
                    code_generator.add_module_constant(&defc.name, tabled, defc.body.clone())
                }
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

                code_generator.add_macro(&mac.name, optimized_code)
            }
            _ => code_generator,
        };
    }

    if !opts.in_defun() && !code_generator.module_constants.is_empty() {
        // Process inlines early because we may not have a chance later.
        // They could be eliminated.
        for h in program.helpers.iter() {
            if let HelperForm::Defun(true, defun) = h {
                code_generator = code_generator.add_inline(
                    &defun.name,
                    &InlineFunction {
                        name: defun.name.clone(),
                        args: defun.args.clone(),
                        body: defun.body.clone(),
                    },
                );
            }
        }

        // Generate a __chia__extras constant as a placeholder for extra objects which
        // should appear in the constant tree when constants are evaluated.
        make_extras_constant(&mut program.helpers);
    }

    let only_defuns: Vec<HelperForm> = program
        .helpers
        .iter()
        .filter(|x| is_defun_or_tabled_const(x))
        .cloned()
        .collect();

    code_generator.env = match opts.start_env() {
        Some(env) => env,
        None => Rc::new(compute_env_shape(
            program.loc.clone(),
            program.args,
            &only_defuns,
        )),
    };

    code_generator.to_process = program.helpers.clone();
    // Ensure that we have the synthesis of the previous codegen's helpers and
    // The ones provided with the new form if any.
    let mut combined_helpers_for_codegen = program.helpers.clone();
    combined_helpers_for_codegen.append(&mut code_generator.original_helpers);
    code_generator.original_helpers = combined_helpers_for_codegen;
    code_generator.final_expr = program.exp;

    // Check whether extras was created.  If so, record its path.
    if let Some((path, _)) = find_named_path(
        code_generator.env.clone(),
        b"__chia__extras",
        bi_one(),
        bi_zero()
    ) {
        // Record the path by upgrading code_generator.final_env.
        code_generator.final_env = code_generator.final_env.set_path(path);
    }

    Ok(code_generator)
}

fn make_extras_constant(helpers: &mut Vec<HelperForm>) {
    // Generate the first body of __chia__extras.  The code generator will assume
    // it's safe to generate this and will populate it in dependency order.
    let extras_data = if !helpers.is_empty() {
        let mut extras_data = SExp::Nil(helpers[0].loc());
        for h in helpers.iter() {
            // Make an entry for each helper, regardless.  This will go as the
            // leftmost object in the env, so anything that appears in the
            // real environment will make the corresponding entry here
            // redundant, but we don't precisely know what the env will look
            // like yet.
            extras_data = SExp::Cons(
                h.loc(),
                Rc::new(SExp::Atom(h.loc(), h.name().to_vec())),
                Rc::new(extras_data),
            );
        }
        extras_data
    } else {
        SExp::Nil(Srcloc::start("*no-constants*"))
    };

    // Make a defconst for this.
    helpers.insert(
        0,
        HelperForm::Defconstant(DefconstData {
            loc: extras_data.loc(),
            nl: extras_data.loc(),
            tabled: true,
            kw: None,
            name: b"__chia__extras".to_vec(),
            kind: ConstantKind::Complex,
            body: Rc::new(BodyForm::Quoted(extras_data)),
            ty: None,
        }),
    );
}

fn final_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
) -> Result<PrimaryCodegen, CompileErr> {
    let opt_final_expr = context.pre_final_codegen_optimize(opts.clone(), compiler)?;
    let optimizer_opts = opts.clone();
    let code = generate_expr_code(context, opts, compiler, opt_final_expr)?;
    let mut final_comp = compiler.clone();
    let optimized_code =
        context.post_codegen_function_optimize(optimizer_opts.clone(), None, code.1.clone())?;
    final_comp.final_code = Some(CompiledCode(code.0, optimized_code));
    Ok(final_comp)
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
                Ok(Rc::new(SExp::Nil(l.clone())))
            } else {
                Err(CompileErr(
                    l.clone(),
                    format!(
                        "A defun was referenced in the defun env but not found {}",
                        decode_string(v)
                    ),
                ))
            }
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
                    if compiler.module_constants.is_empty() {
                        fail_if_present(defun.loc.clone(), &compiler.inlines, &defun.name, comp)
                    } else {
                        Ok(compiler)
                    }
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

#[deprecated]
fn compose_final_env(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
) -> Result<ProgramEnvData, CompileErr> {
    match c.final_env.borrow() {
        ProgramEnvData::Simple(_) => {
            todo!();
        }
        ProgramEnvData::Module(p, _) => {
            Ok(ProgramEnvData::Module(p.clone(), finalize_env(context, opts.clone(), &c)?))
        }
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
    c.final_env =
        if !opts.in_defun() && !c.module_constants.is_empty() {
            compose_final_env(context, opts.clone(), &c)?
        } else {
            ProgramEnvData::Simple(finalize_env(context, opts.clone(), &c)?)
        };

    // If we have delayed constants to generate, do them here as we have the final
    // form of the exported program's environment.  We must generate anything
    // needed by the constant time environment, replace the module constants and
    // then erase the intermediate work.  If we're able to do that then we have
    // a consistent constant time view.
    if !opts.in_defun() && !c.module_constants.is_empty() {
        // Install names in the environment based on the contents of the
        // __chia__extras helper.
        let correct_env = c.env.clone();
        // We have module style constants so there is more work to do.
        // Get a viable generation order for the constant generation or fail.
        let generation_order =
            decide_constant_generation_order(&cmod.loc, &c, &c.original_helpers)?;

        // We've got an order for generation that will allow us to have correct
        // constant order.  At this point we know that the constant order is
        // resolvable and doesn't have direct cycles.  It may be the case that
        // some functions didn't have their target constants avaialble, but the
        // functions generated are in their final representations.
        //
        // We start by generating all functions, then all constants and repeat
        // until the representation converges.
        //
        // Consider this program:
        //
        // (include *standard-cl-23*)

        // (defconst C 19191)
        // (defun F (X) (+ C X))
        // (defconst D (list C F (C_hash) (F_hash)))
        //
        // (export C)
        // (export D)
        // (export F)
        //
        // D will contain the full environment, including itself via F.
        //
        // We must ensure that the representation of the environment is quineable.
        //
        // Therefore, we need an environment expression that we're able to express
        // in a function-as-callable context without causing the environment to
        // multiply.  I originally envisioned a method for this.
        //
        // The method is that we'll know the path to __chia__extras and write the
        // environment as an expression that takes unaffected left and right sub
        // trees and places a separately determined value in its place.
        //
        // One thing we must do is produce saturated functions consistently in the
        // quineable way everywhere when module constants exist.
        let mut prev_repr = ProgramEnvData::Simple(Rc::new(SExp::Nil(c.final_env.loc())));
        let mut this_repr = c.final_env.clone();
        let mut steps = 0;

        while prev_repr != this_repr && steps < CONSTANT_GENERATIONS_ALLOWED {
            for h in generation_order.iter() {
                match h {
                    HelperForm::Defun(false, dd) => {
                        if !name_in_env(correct_env.clone(), &dd.name) {
                            todo!();
                            generate_function_body_for_constants(context, &mut c, opts.clone(), dd)?;
                        }
                    }
                    HelperForm::Defconstant(dc) => {
                        if let ConstantKind::Module(tabled) = &dc.kind {
                            generate_constant_body_for_constants(context, &mut c, opts.clone(), *tabled, dc)?;
                        }
                    }
                    _ => {}
                }
            }

            prev_repr = this_repr;
            this_repr = c.final_env.clone();

            steps += 1;
        }

        if steps == CONSTANT_GENERATIONS_ALLOWED {
            return Err(CompileErr(
                Srcloc::start(&opts.filename()),
                "Constant generation didn't converge in allowed iteration limit".to_string(),
            ));
        }

        c = final_codegen(context, opts.clone(), &c)?;
        c.final_env =
            if !opts.in_defun() && !c.module_constants.is_empty() {
                compose_final_env(context, opts.clone(), &c)?
            } else {
                ProgramEnvData::Simple(finalize_env(context, opts.clone(), &c)?)
            };

        // Erase our additions to the environment.
        purge_chia_extras(&mut c, correct_env);
    }

    let code =
        if let Some(code) = c.final_code.as_ref() {
            code.clone()
        } else {
            return Err(CompileErr(
                Srcloc::start(&opts.filename()),
                "Failed to generate code".to_string(),
            ));
        };

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

        Ok(final_code)
    } else if c.left_env {
        let final_code = primapply(
            code.0.clone(),
            Rc::new(primquote(code.0.clone(), code.1)),
            Rc::new(primcons(
                code.0.clone(),
                Rc::new(primquote(code.0.clone(), c.final_env.to_sexp())),
                Rc::new(SExp::Integer(code.0, bi_one())),
            )),
        );
        Ok(final_code)
    } else {
        let code_borrowed: &SExp = code.1.borrow();
        Ok(code_borrowed.clone())
    }
}
