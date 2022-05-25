use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::clvm::run;
use crate::compiler::compiler::run_optimizer;
use crate::compiler::comptypes::{
    cons_of_string_map, foldM, join_vecs_to_string, list_to_cons, with_heading, Binding, BodyForm,
    Callable, CompileErr, CompileForm, CompiledCode, CompilerOpts, DefunCall, HelperForm,
    InlineFunction, LetFormKind, PrimaryCodegen,
};
use crate::compiler::debug::{build_swap_table_mut, relabel};
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::gensym::gensym;
use crate::compiler::inline::{replace_in_inline, synthesize_args};
use crate::compiler::optimize::optimize_expr;
use crate::compiler::prims::{primapply, primcons, primquote};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::u8_from_number;

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

fn build_tree(l: Srcloc, s: usize, e: usize, helper_array: &Vec<HelperForm>) -> SExp {
    if e - s == 1 {
        helper_atom(helper_array[s].borrow())
    } else {
        let mid = (e + s) / 2;
        let car = build_tree(l.clone(), s, mid, helper_array);
        let cdr = build_tree(l.clone(), mid, e, helper_array);
        SExp::Cons(l, Rc::new(car), Rc::new(cdr))
    }
}

fn compute_code_shape(l: Srcloc, helpers: &Vec<HelperForm>) -> SExp {
    let alen = helpers.len();
    if alen == 0 {
        SExp::Nil(l)
    } else if alen == 1 {
        SExp::Atom(l, helpers[0].name().clone())
    } else {
        build_tree(l, 0, alen, &helpers)
    }
}

fn compute_env_shape(l: Srcloc, args: Rc<SExp>, helpers: &Vec<HelperForm>) -> SExp {
    let car = compute_code_shape(l.clone(), helpers);
    let cdr = args;
    SExp::Cons(l, Rc::new(car), cdr)
}

fn create_name_lookup_(
    l: Srcloc,
    name: &Vec<u8>,
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
                        decode_string(&name),
                        decode_string(&a)
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
                        decode_string(&name),
                        decode_string(&a)
                    ),
                ))
            }
        }
        SExp::Cons(l, head, rest) => {
            match create_name_lookup_(l.clone(), name, env.clone(), head.clone()) {
                Err(_) => {
                    create_name_lookup_(l.clone(), name, env, rest.clone()).map(|v| 2 * v + 1)
                }
                Ok(v) => Ok(2 * v),
            }
        }
        _ => Err(CompileErr(
            l.clone(),
            format!(
                "operator or function atom {} not found checking {} in {}",
                decode_string(&name),
                find.to_string(),
                env.to_string()
            ),
        )),
    }
}

fn create_name_lookup(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>,
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

fn lookup_prim(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>,
) -> Result<Rc<SExp>, CompileErr> {
    compiler
        .prims
        .get(name)
        .map(|x| Ok(x.clone()))
        .unwrap_or_else(|| {
            Err(CompileErr(
                l.clone(),
                format!("no such prim {}", decode_string(name)),
            ))
        })
}

fn codegen_to_sexp(opts: Rc<dyn CompilerOpts>, compiler: &PrimaryCodegen) -> SExp {
    let l = Srcloc::start(&opts.filename());
    let to_process: Vec<Rc<SExp>> = compiler
        .to_process
        .iter()
        .map(|h| Rc::new(SExp::Atom(l.clone(), h.name().clone())))
        .collect();

    with_heading(
        l.clone(),
        &"codegen".to_string(),
        Rc::new(list_to_cons(
            l.clone(),
            &vec![
                Rc::new(with_heading(
                    l.clone(),
                    &"prims".to_string(),
                    Rc::new(cons_of_string_map(
                        l.clone(),
                        &|x: &Rc<SExp>| x.clone(),
                        &compiler.prims,
                    )),
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"macros".to_string(),
                    Rc::new(cons_of_string_map(
                        l.clone(),
                        &|x: &Rc<SExp>| x.clone(),
                        &compiler.macros,
                    )),
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"defuns".to_string(),
                    Rc::new(cons_of_string_map(
                        l.clone(),
                        &|dc: &DefunCall| {
                            Rc::new(SExp::Cons(
                                l.clone(),
                                dc.required_env.clone(),
                                Rc::new(SExp::Cons(
                                    l.clone(),
                                    dc.code.clone(),
                                    Rc::new(SExp::Nil(l.clone())),
                                )),
                            ))
                        },
                        &compiler.defuns,
                    )),
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"to_process".to_string(),
                    Rc::new(list_to_cons(l.clone(), &to_process)),
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"env".to_string(),
                    Rc::new(SExp::Cons(
                        l.clone(),
                        compiler.env.clone(),
                        Rc::new(SExp::Nil(l.clone())),
                    )),
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"final_expr".to_string(),
                    Rc::new(SExp::Cons(
                        l.clone(),
                        compiler.final_expr.to_sexp(),
                        Rc::new(SExp::Nil(l.clone())),
                    )),
                )),
            ],
        )),
    )
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
            let prim = compiler.prims.get(name);
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
        SExp::Integer(_, v) => Ok(Callable::CallPrim(
            l.clone(),
            SExp::Integer(l.clone(), v.clone()),
        )),
        _ => Err(CompileErr(
            atom.loc(),
            format!("can't call object {}", atom.to_string()),
        )),
    }
}

pub fn process_macro_call(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
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

    let arg_strs: Vec<String> = args.iter().map(|x| x.to_sexp().to_string()).collect();

    run(
        allocator,
        runner.clone(),
        opts.prim_map(),
        code,
        Rc::new(args_to_macro),
    )
    .map_err(|e| match e {
        RunFailure::RunExn(ml, x) => CompileErr(
            l,
            format!("macro aborted at {} with {}", ml.to_string(), x.to_string()),
        ),
        RunFailure::RunErr(rl, e) => CompileErr(
            l,
            format!(
                "error executing macro: {} {}",
                rl.to_string(),
                e.to_string()
            ),
        ),
    })
    .and_then(|v| {
        let relabeled_expr = relabel(&mut swap_table, &v);
        compile_bodyform(Rc::new(relabeled_expr))
    })
    .and_then(|body| generate_expr_code(allocator, runner, opts, compiler, Rc::new(body)))
}

fn generate_args_code(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    list: &Vec<Rc<BodyForm>>,
) -> Result<SExp, CompileErr> {
    if list.len() == 0 {
        Ok(SExp::Nil(l.clone()))
    } else {
        let mut compiled_args: Vec<Rc<SExp>> = Vec::new();
        for hd in list.iter() {
            let generated = generate_expr_code(
                allocator,
                runner.clone(),
                opts.clone(),
                compiler,
                hd.clone(),
            )
            .map(|x| x.1)?;
            compiled_args.push(generated);
        }
        Ok(list_to_cons(l.clone(), &compiled_args))
    }
}

fn cons_up(at: Rc<SExp>) -> Rc<SExp> {
    match at.borrow() {
        SExp::Cons(l, h, r) => Rc::new(primcons(l.clone(), h.clone(), cons_up(r.clone()))),
        _ => at,
    }
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
        cons_up(args),
    );
    Ok(CompiledCode(
        l.clone(),
        Rc::new(primapply(l.clone(), lookup, Rc::new(env))),
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

    return Err(CompileErr(
        l,
        format!("not yet callable {}", body.to_sexp().to_string()),
    ));
}

fn compile_call(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    l: Srcloc,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    list: Vec<Rc<BodyForm>>,
) -> Result<CompiledCode, CompileErr> {
    let arg_string_list: Vec<Vec<u8>> = list
        .iter()
        .map(|v| v.to_sexp().to_string().as_bytes().to_vec())
        .collect();

    let error = Err(CompileErr(
        l.clone(),
        format!(
            "wierdly formed compile request: {}",
            join_vecs_to_string(";".as_bytes().to_vec(), &arg_string_list)
        ),
    ));

    let compile_atom_head = |al: Srcloc, an: &Vec<u8>| {
        let tl = list.iter().skip(1).map(|x| x.clone()).collect();
        get_callable(
            opts.clone(),
            compiler,
            l.clone(),
            Rc::new(SExp::Atom(al.clone(), an.to_vec())),
        )
        .and_then(|calltype| match calltype {
            Callable::CallMacro(l, code) => process_macro_call(
                allocator,
                runner,
                opts.clone(),
                compiler,
                l.clone(),
                tl,
                Rc::new(code),
            ),

            Callable::CallInline(l, inline) => replace_in_inline(
                allocator,
                runner.clone(),
                opts.clone(),
                compiler,
                l.clone(),
                &inline,
                &tl,
            ),

            Callable::CallDefun(l, lookup) => {
                generate_args_code(allocator, runner, opts.clone(), compiler, l.clone(), &tl)
                    .and_then(|args| {
                        process_defun_call(
                            opts.clone(),
                            compiler,
                            l.clone(),
                            Rc::new(args),
                            Rc::new(lookup),
                        )
                    })
            }

            Callable::CallPrim(l, p) => {
                generate_args_code(allocator, runner, opts, compiler, l.clone(), &tl).map(|args| {
                    CompiledCode(l.clone(), Rc::new(SExp::Cons(l, Rc::new(p), Rc::new(args))))
                })
            }

            Callable::EnvPath => {
                if tl.len() == 1 {
                    match tl[0].borrow() {
                        BodyForm::Value(SExp::Integer(l, i)) => Ok(CompiledCode(
                            l.clone(),
                            Rc::new(SExp::Integer(l.clone(), i.clone())),
                        )),
                        _ => Err(CompileErr(
                            al.clone(),
                            format!("@ form only accepts integers at present"),
                        )),
                    }
                } else {
                    Err(CompileErr(
                        al.clone(),
                        format!("@ form accepts one argument"),
                    ))
                }
            }

            Callable::RunCompiler => {
                if list.len() >= 2 {
                    let updated_opts = opts
                        .set_stdenv(false)
                        .set_in_defun(true)
                        .set_start_env(Some(compiler.env.clone()))
                        .set_compiler(compiler.clone());

                    let use_body = SExp::Cons(
                        l.clone(),
                        Rc::new(SExp::Atom(l.clone(), "mod".as_bytes().to_vec())),
                        Rc::new(SExp::Cons(
                            l.clone(),
                            Rc::new(SExp::Nil(l.clone())),
                            Rc::new(SExp::Cons(
                                list[1].loc(),
                                list[1].to_sexp(),
                                Rc::new(SExp::Nil(l.clone())),
                            )),
                        )),
                    );

                    let mut unused_symbol_table = HashMap::new();
                    updated_opts
                        .compile_program(
                            allocator,
                            runner,
                            Rc::new(use_body),
                            &mut unused_symbol_table,
                        )
                        .map(|code| {
                            CompiledCode(l.clone(), Rc::new(primquote(l.clone(), Rc::new(code))))
                        })
                } else {
                    error.clone()
                }
            }
        })
    };

    match list[0].borrow() {
        BodyForm::Value(SExp::Integer(al, an)) => {
            compile_atom_head(al.clone(), &u8_from_number(an.clone()))
        }
        BodyForm::Value(SExp::QuotedString(al, _, an)) => compile_atom_head(al.clone(), an),
        BodyForm::Value(SExp::Atom(al, an)) => compile_atom_head(al.clone(), an),
        _ => error,
    }
}

pub fn generate_expr_code(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    expr: Rc<BodyForm>,
) -> Result<CompiledCode, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(l, LetFormKind::Parallel, bindings, expr) => {
            /* Depends on a defun having been desugared from this let and the let
            expressing rewritten. */
            generate_expr_code(allocator, runner, opts, compiler, expr.clone())
        }
        BodyForm::Quoted(q) => {
            let l = q.loc();
            Ok(CompiledCode(
                l.clone(),
                Rc::new(primquote(l.clone(), Rc::new(q.clone()))),
            ))
        }
        BodyForm::Value(v) => {
            match v.borrow() {
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
                                    allocator,
                                    runner,
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
                    allocator,
                    runner,
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
        BodyForm::Call(l, list) => {
            if list.len() == 0 {
                Err(CompileErr(
                    l.clone(),
                    "created a call with no forms".to_string(),
                ))
            } else {
                compile_call(allocator, runner, l.clone(), opts, compiler, list.to_vec())
            }
        }
        _ => Err(CompileErr(
            expr.loc(),
            format!("don't know how to compile {}", expr.to_sexp().to_string()),
        )),
    }
}

fn combine_defun_env(old_env: Rc<SExp>, new_args: Rc<SExp>) -> Rc<SExp> {
    match old_env.borrow() {
        SExp::Cons(l, h, _) => Rc::new(SExp::Cons(l.clone(), h.clone(), new_args.clone())),
        _ => old_env,
    }
}

// Diverts to failure if a symbol is redefined.
fn fail_if_present<T, R>(
    loc: Srcloc,
    map: &HashMap<Vec<u8>, T>,
    name: &Vec<u8>,
    result: R,
) -> Result<R, CompileErr> {
    if map.contains_key(name) {
        Err(CompileErr(
            loc.clone(),
            format!(
                "Cannot redefine {}",
                SExp::Atom(loc.clone(), name.clone()).to_string()
            ),
        ))
    } else {
        Ok(result)
    }
}

fn codegen_(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    h: &HelperForm,
) -> Result<PrimaryCodegen, CompileErr> {
    match h {
        HelperForm::Defun(loc, name, inline, args, body) => {
            if *inline {
                // Note: this just replaces a dummy function inserted earlier.
                // The real redefinition check is in dummy_functions.
                Ok(compiler.add_inline(
                    name,
                    &InlineFunction {
                        name: name.clone(),
                        args: args.clone(),
                        body: body.clone(),
                    },
                ))
            } else {
                let updated_opts = opts
                    .set_compiler(compiler.clone())
                    .set_in_defun(true)
                    .set_stdenv(false)
                    .set_start_env(Some(combine_defun_env(compiler.env.clone(), args.clone())));

                let opt = if opts.optimize() {
                    // Run optimizer on frontend style forms.
                    optimize_expr(
                        allocator,
                        opts.clone(),
                        runner.clone(),
                        compiler,
                        body.clone(),
                    )
                    .map(|x| x.1)
                    .unwrap_or_else(|| body.clone())
                } else {
                    body.clone()
                };

                let tocompile = SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Atom(loc.clone(), "mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        args.clone(),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            opt.to_sexp(),
                            Rc::new(SExp::Nil(loc.clone())),
                        )),
                    )),
                );

                let mut unused_symbol_table = HashMap::new();
                updated_opts
                    .compile_program(
                        allocator,
                        runner.clone(),
                        Rc::new(tocompile),
                        &mut unused_symbol_table,
                    )
                    .and_then(|code| {
                        if opts.optimize() {
                            run_optimizer(allocator, runner, Rc::new(code))
                        } else {
                            Ok(Rc::new(code))
                        }
                    })
                    .and_then(|code| fail_if_present(loc.clone(), &compiler.inlines, &name, code))
                    .and_then(|code| fail_if_present(loc.clone(), &compiler.defuns, &name, code))
                    .map(|code| {
                        compiler.add_defun(
                            name,
                            DefunCall {
                                required_env: args.clone(),
                                code,
                            },
                        )
                    })
            }
        }
        _ => Ok(compiler.clone()),
    }
}

fn is_defun(b: &HelperForm) -> bool {
    match b {
        HelperForm::Defun(_, _, false, _, _) => true,
        _ => false,
    }
}

pub fn empty_compiler(prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>, l: Srcloc) -> PrimaryCodegen {
    let nil = SExp::Nil(l.clone());
    let nil_rc = Rc::new(nil.clone());

    PrimaryCodegen {
        prims: prim_map.clone(),
        constants: HashMap::new(),
        inlines: HashMap::new(),
        macros: HashMap::new(),
        defuns: HashMap::new(),
        parentfns: HashSet::new(),
        env: Rc::new(SExp::Cons(l.clone(), nil_rc.clone(), nil_rc.clone())),
        to_process: Vec::new(),
        orig_help: Vec::new(),
        final_expr: Rc::new(BodyForm::Quoted(nil.clone())),
        final_code: None,
        function_symbols: HashMap::new(),
    }
}

fn generate_let_defun(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>,
    args: Rc<SExp>,
    bindings: Vec<Rc<Binding>>,
    body: Rc<BodyForm>,
) -> HelperForm {
    let new_arguments: Vec<Rc<SExp>> = bindings
        .iter()
        .map(|b| Rc::new(SExp::Atom(l.clone(), b.name.clone())))
        .collect();

    let inner_function_args = SExp::Cons(
        l.clone(),
        args,
        Rc::new(list_to_cons(l.clone(), &new_arguments)),
    );

    HelperForm::Defun(
        l.clone(),
        name.clone(),
        true,
        Rc::new(inner_function_args),
        body,
    )
}

fn generate_let_args(l: Srcloc, blist: Vec<Rc<Binding>>) -> Vec<Rc<BodyForm>> {
    blist.iter().map(|b| b.body.clone()).collect()
}

fn hoist_body_let_binding(
    compiler: &PrimaryCodegen,
    outer_context: Option<Rc<SExp>>,
    args: Rc<SExp>,
    body: Rc<BodyForm>,
) -> (Vec<HelperForm>, Rc<BodyForm>) {
    match body.borrow() {
        BodyForm::Let(l, LetFormKind::Parallel, bindings, body) => {
            let defun_name = gensym("letbinding".as_bytes().to_vec());
            let generated_defun = generate_let_defun(
                compiler,
                l.clone(),
                &defun_name,
                args.clone(),
                bindings.to_vec(),
                body.clone(),
            );
            let mut let_args = generate_let_args(l.clone(), bindings.to_vec());
            let pass_env = outer_context
                .map(|x| create_let_env_expression(x))
                .unwrap_or_else(|| {
                    BodyForm::Call(
                        l.clone(),
                        vec![
                            Rc::new(BodyForm::Value(SExp::Atom(
                                l.clone(),
                                "r".as_bytes().to_vec(),
                            ))),
                            Rc::new(BodyForm::Value(SExp::Atom(
                                l.clone(),
                                "@".as_bytes().to_vec(),
                            ))),
                        ],
                    )
                });

            let mut call_args = Vec::new();
            call_args.push(Rc::new(BodyForm::Value(SExp::Atom(l.clone(), defun_name))));
            call_args.push(Rc::new(pass_env.clone()));
            call_args.append(&mut let_args);

            let final_call = BodyForm::Call(l.clone(), call_args);
            (vec![generated_defun], Rc::new(final_call.clone()))
        }
        _ => (Vec::new(), body.clone()),
    }
}

fn process_helper_let_bindings(
    compiler: &PrimaryCodegen,
    helpers: &Vec<HelperForm>,
) -> Vec<HelperForm> {
    let mut subcompiler = compiler.clone();
    let mut result = helpers.clone();
    let mut i = 0;

    while i < result.len() {
        match result[i].clone() {
            HelperForm::Defun(l, name, inline, args, body) => {
                let context = if inline { Some(args.clone()) } else { None };
                let helper_result =
                    hoist_body_let_binding(compiler, context, args.clone(), body.clone());
                let hoisted_helpers = helper_result.0;
                let hoisted_body = helper_result.1.clone();

                result[i] =
                    HelperForm::Defun(l.clone(), name.clone(), inline, args.clone(), hoisted_body);

                i += 1;

                for j in 0..hoisted_helpers.len() {
                    result.insert(i + j, hoisted_helpers[j].clone());
                }

                subcompiler =
                    compiler.set_env(combine_defun_env(compiler.env.clone(), args.clone()));
            }
            _ => {
                i += 1;
            }
        }
    }

    result
}

fn start_codegen(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    comp: CompileForm,
) -> Result<PrimaryCodegen, CompileErr> {
    let mut use_compiler = match opts.compiler() {
        None => empty_compiler(opts.prim_map(), comp.loc.clone()),
        Some(c) => c,
    };

    // Start compiler with all macros and constants
    for h in comp.helpers.iter() {
        use_compiler = match h.borrow() {
            HelperForm::Defconstant(loc, name, body) => {
                let expand_program = SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Atom(loc.clone(), "mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::Nil(loc.clone())),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            Rc::new(primquote(loc.clone(), body.to_sexp())),
                            Rc::new(SExp::Nil(loc.clone())),
                        )),
                    )),
                );
                let updated_opts = opts.set_compiler(use_compiler.clone());
                let code = updated_opts.compile_program(
                    allocator,
                    runner.clone(),
                    Rc::new(expand_program),
                    &mut HashMap::new(),
                )?;
                run(
                    allocator,
                    runner.clone(),
                    opts.prim_map(),
                    Rc::new(code),
                    Rc::new(SExp::Nil(loc.clone())),
                )
                .map_err(|r| {
                    CompileErr(
                        loc.clone(),
                        format!("Error evaluating constant: {}", r.to_string()),
                    )
                })
                .and_then(|res| fail_if_present(loc.clone(), &use_compiler.constants, &name, res))
                .map(|res| {
                    let quoted = primquote(loc.clone(), res);
                    use_compiler.add_constant(&name, Rc::new(quoted))
                })?
            }
            HelperForm::Defmacro(loc, name, args, body) => {
                let macro_program = Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Atom(loc.clone(), "mod".as_bytes().to_vec())),
                    body.to_sexp(),
                ));

                let updated_opts = opts
                    .set_compiler(use_compiler.clone())
                    .set_in_defun(false)
                    .set_stdenv(false)
                    .set_frontend_opt(false);

                updated_opts
                    .compile_program(
                        allocator,
                        runner.clone(),
                        macro_program,
                        &mut HashMap::new(),
                    )
                    .and_then(|code| {
                        if opts.optimize() {
                            run_optimizer(allocator, runner.clone(), Rc::new(code))
                        } else {
                            Ok(Rc::new(code))
                        }
                    })
                    .map(|code| use_compiler.add_macro(&name, code))?
            }
            _ => use_compiler,
        };
    }

    let hoisted_bindings = hoist_body_let_binding(&use_compiler, None, comp.args.clone(), comp.exp);
    let mut new_helpers = hoisted_bindings.0;
    let expr = hoisted_bindings.1;
    new_helpers.append(&mut comp.helpers.clone());
    let let_helpers_with_expr = process_helper_let_bindings(&use_compiler.clone(), &new_helpers);
    let live_helpers = let_helpers_with_expr
        .iter()
        .filter(|x| is_defun(x))
        .map(|x| x.clone())
        .collect();

    use_compiler.env = match opts.start_env() {
        Some(env) => env,
        None => Rc::new(compute_env_shape(
            comp.loc.clone(),
            comp.args.clone(),
            &live_helpers,
        )),
    };

    use_compiler.to_process = let_helpers_with_expr.clone();
    use_compiler.orig_help = let_helpers_with_expr.clone();
    use_compiler.final_expr = expr.clone();

    Ok(use_compiler)
}

fn final_codegen(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
) -> Result<PrimaryCodegen, CompileErr> {
    let opt_final_expr = if opts.optimize() {
        optimize_expr(
            allocator,
            opts.clone(),
            runner.clone(),
            compiler,
            compiler.final_expr.clone(),
        )
        .map(|x| x.1)
        .unwrap_or_else(|| compiler.final_expr.clone())
    } else {
        compiler.final_expr.clone()
    };

    generate_expr_code(allocator, runner, opts, compiler, opt_final_expr).map(|code| {
        let mut final_comp = compiler.clone();
        final_comp.final_code = Some(CompiledCode(code.0, code.1));
        final_comp
    })
}

fn finalize_env_(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
    l: Srcloc,
    env: Rc<SExp>,
) -> Result<Rc<SExp>, CompileErr> {
    match env.borrow() {
        SExp::Atom(l, v) => {
            match c.defuns.get(v) {
                Some(res) => Ok(res.code.clone()),
                None => {
                    match c.inlines.get(v) {
                        Some(res) => replace_in_inline(
                            allocator,
                            runner.clone(),
                            opts.clone(),
                            c,
                            l.clone(),
                            res,
                            &synthesize_args(res.args.clone()),
                        )
                        .map(|x| x.1.clone()),
                        None => {
                            /* Parentfns are functions in progress in the parent */
                            if !c.parentfns.get(v).is_none() {
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

        SExp::Cons(l, h, r) => finalize_env_(
            allocator,
            runner.clone(),
            opts.clone(),
            c,
            l.clone(),
            h.clone(),
        )
        .and_then(|h| {
            finalize_env_(
                allocator,
                runner.clone(),
                opts.clone(),
                c,
                l.clone(),
                r.clone(),
            )
            .map(|r| Rc::new(SExp::Cons(l.clone(), h.clone(), r.clone())))
        }),

        _ => Ok(env.clone()),
    }
}

fn finalize_env(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
) -> Result<Rc<SExp>, CompileErr> {
    match c.env.borrow() {
        SExp::Cons(l, h, _) => finalize_env_(
            allocator,
            runner.clone(),
            opts.clone(),
            c,
            l.clone(),
            h.clone(),
        ),
        _ => Ok(c.env.clone()),
    }
}

fn dummy_functions(compiler: &PrimaryCodegen) -> Result<PrimaryCodegen, CompileErr> {
    foldM(
        &|compiler: &PrimaryCodegen, form: &HelperForm| match form {
            HelperForm::Defun(_, name, false, _, _) => {
                let mut c_copy = compiler.clone();
                c_copy.parentfns.insert(name.clone());
                Ok(c_copy)
            }
            HelperForm::Defun(loc, name, true, args, body) => Ok(compiler)
                .and_then(|comp| fail_if_present(loc.clone(), &compiler.inlines, &name, comp))
                .and_then(|comp| fail_if_present(loc.clone(), &compiler.defuns, &name, comp))
                .map(|comp| {
                    comp.add_inline(
                        name,
                        &InlineFunction {
                            name: name.clone(),
                            args: args.clone(),
                            body: body.clone(),
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
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    cmod: &CompileForm,
    symbol_table: &mut HashMap<String, String>,
) -> Result<SExp, CompileErr> {
    let mut compiler = dummy_functions(&start_codegen(
        allocator,
        runner.clone(),
        opts.clone(),
        cmod.clone(),
    )?)?;

    let to_process = compiler.to_process.clone();

    for f in to_process {
        compiler = codegen_(allocator, runner.clone(), opts.clone(), &compiler, &f)?;
    }

    *symbol_table = compiler.function_symbols.clone();

    final_codegen(allocator, runner.clone(), opts.clone(), &compiler).and_then(|c| {
        let final_env = finalize_env(allocator, runner.clone(), opts.clone(), &c)?;
        match c.final_code {
            None => Err(CompileErr(
                Srcloc::start(&opts.filename()),
                "Failed to generate code".to_string(),
            )),
            Some(code) => {
                if opts.in_defun() {
                    let final_code = primapply(
                        code.0.clone(),
                        Rc::new(primquote(code.0.clone(), code.1)),
                        Rc::new(SExp::Integer(code.0.clone(), bi_one())),
                    );

                    Ok(final_code)
                } else {
                    let final_code = primapply(
                        code.0.clone(),
                        Rc::new(primquote(code.0.clone(), code.1)),
                        Rc::new(primcons(
                            code.0.clone(),
                            Rc::new(primquote(code.0.clone(), final_env)),
                            Rc::new(SExp::Integer(code.0.clone(), bi_one())),
                        )),
                    );

                    Ok(final_code)
                }
            }
        }
    })
}
