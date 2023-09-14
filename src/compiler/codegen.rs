use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::mem::swap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::clvm::run;
use crate::compiler::compiler::{is_at_capture, run_optimizer};
use crate::compiler::comptypes::{
    fold_m, join_vecs_to_string, list_to_cons, Binding, BindingPattern, BodyForm, CallSpec,
    Callable, CompileErr, CompileForm, CompiledCode, CompilerOpts, ConstantKind, DefunCall,
    DefunData, HelperForm, InlineFunction, LetData, LetFormInlineHint, LetFormKind, PrimaryCodegen,
    RawCallSpec,
};
use crate::compiler::debug::{build_swap_table_mut, relabel};
use crate::compiler::evaluate::{Evaluator, EVAL_STACK_LIMIT};
use crate::compiler::frontend::{compile_bodyform, make_provides_set};
use crate::compiler::gensym::gensym;
use crate::compiler::inline::{replace_in_inline, synthesize_args};
use crate::compiler::optimize::optimize_expr;
use crate::compiler::prims::{primapply, primcons, primquote};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::{BasicCompileContext, CompileContextWrapper};
use crate::util::{toposort, u8_from_number, TopoSortItem};

const MACRO_TIME_LIMIT: usize = 1000000;
const CONST_EVAL_LIMIT: usize = 1000000;

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
        _ => Err(CompileErr(
            l,
            format!(
                "operator or function atom {} not found checking {} in {}",
                decode_string(name),
                find,
                env
            ),
        )),
    }
}

fn create_name_lookup(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &[u8],
) -> Result<Rc<SExp>, CompileErr> {
    compiler
        .constants
        .get(name)
        .map(|x| Ok(x.clone()))
        .unwrap_or_else(|| {
            create_name_lookup_(l.clone(), name, compiler.env.clone(), compiler.env.clone())
                .map(|i| Rc::new(SExp::Integer(l.clone(), i.to_bigint().unwrap())))
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
            let defun = create_name_lookup(compiler, l.clone(), name);
            let prim = get_prim(l.clone(), compiler.prims.clone(), name);
            let atom_is_com = *name == "com".as_bytes().to_vec();
            let atom_is_at = *name == "@".as_bytes().to_vec();
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
        .and_then(|calltype| match calltype {
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
                    loc: l.clone(),
                    name: an,
                    args: &tl,
                    tail: None,
                    original: Rc::new(BodyForm::Value(SExp::Nil(l.clone()))),
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
                        _ => Err(CompileErr(
                            al.clone(),
                            "@ form only accepts integers at present".to_string(),
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
                    let runner = context.runner();
                    updated_opts
                        .compile_program(
                            context.allocator(),
                            runner,
                            Rc::new(use_body),
                            &mut unused_symbol_table,
                        )
                        .map(|code| {
                            CompiledCode(
                                call.loc.clone(),
                                Rc::new(primquote(call.loc.clone(), Rc::new(code))),
                            )
                        })
                } else {
                    error.clone()
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
    let runner = context.runner();
    let mut context_wrapper =
        CompileContextWrapper::new(context.allocator(), runner.clone(), &mut throwaway_symbols);
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
                    if *atom == "@".as_bytes().to_vec() {
                        Ok(CompiledCode(
                            l.clone(),
                            Rc::new(SExp::Integer(l.clone(), bi_one())),
                        ))
                    } else {
                        create_name_lookup(compiler, l.clone(), atom)
                            .map(|f| Ok(CompiledCode(l.clone(), f)))
                            .unwrap_or_else(|_| {
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
                // Since macros are in this language and the runtime has
                // a very narrow data representation, we'll need to
                // accomodate bare numbers coming back in place of identifiers.
                // I'm considering ways to make this better.
                SExp::Integer(l, i) => generate_expr_code(
                    context,
                    opts,
                    compiler,
                    Rc::new(BodyForm::Value(SExp::Atom(
                        l.clone(),
                        u8_from_number(i.clone()),
                    ))),
                ),
                _ => Ok(CompiledCode(
                    v.loc(),
                    Rc::new(primquote(v.loc(), Rc::new(v.clone()))),
                )),
            }
        }
        BodyForm::Call(l, list, tail) => {
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
                    .set_stdenv(false)
                    .set_start_env(Some(combine_defun_env(
                        compiler.env.clone(),
                        defun.args.clone(),
                    )));

                let runner = context.runner();
                let opt = if opts.optimize() {
                    // Run optimizer on frontend style forms.
                    optimize_expr(
                        context.allocator(),
                        opts.clone(),
                        runner,
                        compiler,
                        defun.body.clone(),
                    )
                    .map(|x| x.1)
                    .unwrap_or_else(|| defun.body.clone())
                } else {
                    defun.body.clone()
                };

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
                let runner = context.runner();
                updated_opts
                    .compile_program(
                        context.allocator(),
                        runner.clone(),
                        Rc::new(tocompile),
                        &mut unused_symbol_table,
                    )
                    .and_then(|code| {
                        if opts.optimize() {
                            run_optimizer(context.allocator(), runner, Rc::new(code))
                        } else {
                            Ok(Rc::new(code))
                        }
                    })
                    .and_then(|code| {
                        fail_if_present(defun.loc.clone(), &compiler.inlines, &defun.name, code)
                    })
                    .and_then(|code| {
                        fail_if_present(defun.loc.clone(), &compiler.defuns, &defun.name, code)
                    })
                    .map(|code| {
                        compiler.add_defun(
                            &defun.name,
                            defun.orig_args.clone(),
                            DefunCall {
                                required_env: defun.args.clone(),
                                code,
                            },
                            true, // Always take left env for now
                        )
                    })
            }
        }
        _ => Ok(compiler.clone()),
    }
}

fn is_defun(b: &HelperForm) -> bool {
    matches!(b, HelperForm::Defun(false, _))
}

pub fn empty_compiler(prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>, l: Srcloc) -> PrimaryCodegen {
    let nil = SExp::Nil(l.clone());
    let nil_rc = Rc::new(nil.clone());

    PrimaryCodegen {
        prims: prim_map,
        constants: HashMap::new(),
        inlines: HashMap::new(),
        macros: HashMap::new(),
        defuns: HashMap::new(),
        parentfns: HashSet::new(),
        env: Rc::new(SExp::Cons(l, nil_rc.clone(), nil_rc)),
        to_process: Vec::new(),
        original_helpers: Vec::new(),
        final_expr: Rc::new(BodyForm::Quoted(nil)),
        final_code: None,
        function_symbols: HashMap::new(),
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
                                "@".as_bytes().to_vec(),
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
                        loc: defun.loc.clone(),
                        nl: defun.nl.clone(),
                        kw: defun.kw.clone(),
                        name: defun.name.clone(),
                        args: defun.args.clone(),
                        orig_args: defun.orig_args.clone(),
                        body: hoisted_body,
                        ty: defun.ty.clone(),
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
                    let runner = context.runner();
                    let code = updated_opts.compile_program(
                        context.allocator(),
                        runner.clone(),
                        Rc::new(expand_program),
                        &mut HashMap::new(),
                    )?;
                    run(
                        context.allocator(),
                        runner,
                        opts.prim_map(),
                        Rc::new(code),
                        Rc::new(SExp::Nil(defc.loc.clone())),
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
                        let quoted = primquote(defc.loc.clone(), res);
                        code_generator.add_constant(&defc.name, Rc::new(quoted))
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
                        code_generator.add_constant(
                            &defc.name,
                            Rc::new(SExp::Cons(
                                defc.loc.clone(),
                                Rc::new(SExp::Atom(defc.loc.clone(), vec![1])),
                                Rc::new(q.clone()),
                            )),
                        )
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
                    .set_frontend_opt(false);

                let runner = context.runner();
                updated_opts
                    .compile_program(
                        context.allocator(),
                        runner.clone(),
                        macro_program,
                        &mut HashMap::new(),
                    )
                    .and_then(|code| {
                        if opts.optimize() {
                            run_optimizer(context.allocator(), runner, Rc::new(code))
                        } else {
                            Ok(Rc::new(code))
                        }
                    })
                    .map(|code| code_generator.add_macro(&mac.name, code))?
            }
            _ => code_generator,
        };
    }

    let only_defuns: Vec<HelperForm> = program
        .helpers
        .iter()
        .filter(|x| is_defun(x))
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
    code_generator.original_helpers = program.helpers.clone();
    code_generator.final_expr = program.exp;

    Ok(code_generator)
}

fn final_codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
) -> Result<PrimaryCodegen, CompileErr> {
    let runner = context.runner();
    let opt_final_expr = if opts.optimize() {
        optimize_expr(
            context.allocator(),
            opts.clone(),
            runner,
            compiler,
            compiler.final_expr.clone(),
        )
        .map(|x| x.1)
        .unwrap_or_else(|| compiler.final_expr.clone())
    } else {
        compiler.final_expr.clone()
    };

    generate_expr_code(context, opts, compiler, opt_final_expr).map(|code| {
        let mut final_comp = compiler.clone();
        final_comp.final_code = Some(CompiledCode(code.0, code.1));
        final_comp
    })
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
            match c.defuns.get(v) {
                Some(res) => Ok(res.code.clone()),
                None => {
                    match c.inlines.get(v) {
                        Some(res) => {
                            let (arg_list, arg_tail) = synthesize_args(res.args.clone());
                            replace_in_inline(
                                context,
                                opts.clone(),
                                c,
                                l.clone(),
                                res,
                                res.args.loc(),
                                &arg_list,
                                arg_tail,
                            )
                            .map(|x| x.1)
                        }
                        None => {
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
                    }
                }
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
        SExp::Cons(l, h, _) => finalize_env_(context, opts.clone(), c, l.clone(), h.clone()),
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
            _ => Ok(compiler.clone()),
        },
        compiler.clone(),
        &compiler.to_process,
    )
}

pub fn codegen(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    cmod: &CompileForm,
) -> Result<SExp, CompileErr> {
    let mut code_generator = dummy_functions(&start_codegen(context, opts.clone(), cmod.clone())?)?;

    let to_process = code_generator.to_process.clone();

    for f in to_process {
        code_generator = codegen_(context, opts.clone(), &code_generator, &f)?;
    }

    *context.symbols() = code_generator.function_symbols.clone();
    context
        .symbols()
        .insert("source_file".to_string(), opts.filename());

    final_codegen(context, opts.clone(), &code_generator).and_then(|c| {
        let final_env = finalize_env(context, opts.clone(), &c)?;

        match c.final_code {
            None => Err(CompileErr(
                Srcloc::start(&opts.filename()),
                "Failed to generate code".to_string(),
            )),
            Some(code) => {
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
                } else {
                    let final_code = primapply(
                        code.0.clone(),
                        Rc::new(primquote(code.0.clone(), code.1)),
                        Rc::new(primcons(
                            code.0.clone(),
                            Rc::new(primquote(code.0.clone(), final_env)),
                            Rc::new(SExp::Integer(code.0, bi_one())),
                        )),
                    );

                    Ok(final_code)
                }
            }
        }
    })
}
