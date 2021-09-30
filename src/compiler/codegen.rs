use std::borrow::Borrow;
use std::rc::Rc;
use std::collections::HashMap;
use std::collections::HashSet;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    bi_one
};

use crate::compiler::clvm::run;
use crate::compiler::gensym::gensym;
use crate::compiler::prims::prims;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::compiler::comptypes::{
    Binding,
    BodyForm,
    Callable,
    CompileErr,
    CompileForm,
    CompiledCode,
    CompilerOpts,
    DefunCall,
    HelperForm,
    PrimaryCodegen,
    cons_of_string_map,
    decode_string,
    join_vecs_to_string,
    list_to_cons,
    mapM,
    with_heading
};
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::prims::{
    primapply,
    primcons,
    primquote
};
use crate::compiler::runtypes::RunFailure;

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

fn helper_atom(h: &HelperForm) -> SExp {
    SExp::Atom(h.loc(), h.name())
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
        SExp::Atom(l, helpers[0].name())
    } else {
        build_tree(l, 0, alen, &helpers)
    }
}

fn compute_env_shape(
    l: Srcloc,
    args: Rc<SExp>,
    helpers: &Vec<HelperForm>
) -> SExp {
    let car = compute_code_shape(l.clone(), helpers);
    let cdr = args;
    SExp::Cons(l, Rc::new(car), cdr)
}

fn create_name_lookup_(
    l: Srcloc, name: &Vec<u8>, env: Rc<SExp>, find: Rc<SExp>
) -> Result<u64, CompileErr> {
    match find.borrow() {
        SExp::Atom (l,a) => {
            if *a == *name {
                Ok(1_u64)
            } else {
                Err(CompileErr(
                    l.clone(),
                    format!(
                        "{} not found (via {})",
                        decode_string(&name),
                        decode_string(&a)
                    )
                ))
            }
        },
        SExp::Cons (l,head,rest) => {
            create_name_lookup_(l.clone(), name, env, head.clone()).map(
                |v| 2 * v
            )
        },
        _ => {
            Err(CompileErr(
                l.clone(),
                format!(
                    "{} not found checking {} in {}",
                    decode_string(&name),
                    find.to_string(),
                    env.to_string()
                )
            ))
        }
    }
}

fn create_name_lookup(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>
) -> Result<Rc<SExp>, CompileErr> {
    compiler.constants.get(name).map(|x| Ok(x.clone())).unwrap_or_else(|| {
        create_name_lookup_(l.clone(), name, compiler.env.clone(), compiler.env.clone()).map(|i| {
            Rc::new(SExp::Integer(l.clone(),i.to_bigint().unwrap()))
        })
    })
}

fn lookup_prim(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>
) -> Result<Rc<SExp>, CompileErr> {
    compiler.prims.get(name).map(|x| Ok(x.clone())).unwrap_or_else(|| {
        Err(CompileErr(l.clone(), format!("no such prim {}", decode_string(name))))
    })
}

fn codegen_to_sexp(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen
) -> SExp {
    let l = Srcloc::start(&opts.filename());
    let to_process: Vec<Rc<SExp>> =
        compiler.to_process.iter().map(|h| {
            Rc::new(SExp::Atom(l.clone(),h.name()))
        }).collect();

    with_heading(
        l.clone(),
        &"codegen".to_string(),
        Rc::new(list_to_cons(
            l.clone(),
            &vec!(
                Rc::new(with_heading(
                    l.clone(),
                    &"prims".to_string(),
                    Rc::new(cons_of_string_map(l.clone(), &|x: &Rc<SExp>| x.clone(), &compiler.prims))
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"macros".to_string(),
                    Rc::new(cons_of_string_map(l.clone(), &|x: &Rc<SExp>| x.clone(), &compiler.macros))
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
                                    Rc::new(SExp::Nil(l.clone()))
                                ))
                            ))
                        },
                        &compiler.defuns
                    ))
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"to_process".to_string(),
                    Rc::new(list_to_cons(
                        l.clone(),
                        &to_process
                    ))
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"env".to_string(),
                    Rc::new(SExp::Cons(
                        l.clone(),
                        compiler.env.clone(),
                        Rc::new(SExp::Nil(l.clone()))
                    ))
                )),
                Rc::new(with_heading(
                    l.clone(),
                    &"final_expr".to_string(),
                    Rc::new(SExp::Cons(
                        l.clone(),
                        compiler.final_expr.to_sexp(),
                        Rc::new(SExp::Nil(l.clone()))
                    ))
                ))
            )
        ))
    )
}

fn get_callable(
    _opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    _l: Srcloc,
    atom: Rc<SExp>
) -> Result<Callable, CompileErr> {
    match atom.borrow() {
        SExp::Atom(l,name) => {
            let macro_def = compiler.macros.get(name);
            let defun = create_name_lookup(compiler, l.clone(), name);
            let prim = compiler.prims.get(name);
            let atom_is_com = *name == "com".as_bytes().to_vec();
            match (macro_def, defun, prim, atom_is_com) {
                (Some(macro_def), _, _, _) => {
                    let macro_def_clone: &SExp = macro_def.borrow();
                    Ok(Callable::CallMacro(macro_def_clone.clone()))
                },
                (_, Ok(defun), _, _) => {
                    let defun_clone: &SExp = defun.borrow();
                    Ok(Callable::CallDefun(defun_clone.clone()))
                },
                (_, _, Some(prim), _) => {
                    let prim_clone: &SExp = prim.borrow();
                    Ok(Callable::CallPrim(prim_clone.clone()))
                },
                (_, _, _, true) => Ok(Callable::RunCompiler),
                _ => Err(CompileErr(
                    l.clone(),
                    format!("no such callable '{}'", decode_string(name))
                ))
            }
        },
        SExp::Integer(l,v) => {
            Ok(Callable::CallPrim(SExp::Integer(l.clone(),v.clone())))
        },
        _ => Err(CompileErr(
            atom.loc(),
            format!("can't call object {}", atom.to_string())
        ))
    }
}

fn process_macro_call(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    args: Vec<Rc<BodyForm>>,
    code: Rc<SExp>
) -> Result<CompiledCode, CompileErr> {
    let converted_args: Vec<Rc<SExp>> =
        args.iter().map(|b| b.to_sexp()).collect();
    let args_to_macro = list_to_cons(l.clone(), &converted_args);
    run(code, Rc::new(args_to_macro)).map_err(|e| { match e {
        RunFailure::RunExn(ml,x) => {
            CompileErr(
                l,
                format!(
                    "macro aborted at {} with {}",
                    ml.to_string(),
                    x.to_string()
                )
            )
        },
        RunFailure::RunErr(rl,e) => {
            CompileErr(
                l,
                format!(
                    "error executing macro: {} {}",
                    rl.to_string(),
                    e.to_string()
                )
            )
        }
    }}).and_then(|v| {
        compile_bodyform(Rc::new(v))
    }).and_then(|body| generate_expr_code(opts, compiler, Rc::new(body)))
}

fn generate_args_code(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    l: Srcloc,
    list: &Vec<Rc<BodyForm>>
) -> Result<SExp, CompileErr> {
    if list.len() == 0 {
        Ok(SExp::Nil(l.clone()))
    } else {
        let compiled_args: Vec<Rc<SExp>> =
            mapM(
                &|hd: &Rc<BodyForm>| {
                    generate_expr_code(opts.clone(), compiler, hd.clone()).
                        map(|x| x.1)
                },
                &list
            )?;
        Ok(list_to_cons(l.clone(), &compiled_args))
    }
}

fn cons_up(at: Rc<SExp>) -> Rc<SExp> {
    match at.borrow() {
        SExp::Cons(l,h,r) => Rc::new(primcons(l.clone(), h.clone(), cons_up(r.clone()))),
        _ => at
    }
}

fn process_defun_call(
    _opts: Rc<dyn CompilerOpts>,
    _compiler: &PrimaryCodegen,
    l: Srcloc,
    args: Rc<SExp>,
    lookup: Rc<SExp>
) -> Result<CompiledCode, CompileErr> {
    let env = primcons(
        l.clone(),
        Rc::new(SExp::Integer(
            l.clone(),
            2_u32.to_bigint().unwrap()
        )),
        cons_up(args)
    );
    Ok(CompiledCode(l.clone(), Rc::new(primapply(l.clone(), lookup, Rc::new(env)))))
}

fn get_call_name(l: Srcloc, body: BodyForm) -> Result<Rc<SExp>, CompileErr> {
    match &body {
        BodyForm::Value(SExp::Atom(l,name)) => {
            return Ok(Rc::new(SExp::Atom(l.clone(),name.clone())));
        },
        BodyForm::Value(SExp::Integer(l,v)) => {
            return Ok(Rc::new(SExp::Integer(l.clone(),v.clone())));
        },
        _ => { }
    }

    return Err(CompileErr(
        l,
        format!("not yet callable {}", body.to_sexp().to_string())
    ))
}

fn compile_call(
    l: Srcloc,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    list: Vec<Rc<BodyForm>>
) -> Result<CompiledCode, CompileErr> {
    let arg_string_list: Vec<Vec<u8>> =
        list.iter().map(|v| {
            v.to_sexp().to_string().as_bytes().to_vec()
        }).collect();

    let error = Err(CompileErr(
        l.clone(),
        format!(
            "wierdly formed compile request: {}",
            join_vecs_to_string(";".as_bytes().to_vec(), &arg_string_list)
        )
    ));
    match list[0].borrow() {
        BodyForm::Value(SExp::Atom(al,an)) => {
            let tl = list.iter().skip(1).map(|x| x.clone()).collect();
            get_callable(opts.clone(), compiler, al.clone(), Rc::new(SExp::Atom(al.clone(), an.to_vec()))).
                and_then(|calltype| match calltype {
                    Callable::CallMacro(code) => {
                        process_macro_call(opts.clone(), compiler, l.clone(), tl, Rc::new(code))
                    },
                    Callable::CallDefun(lookup) => {
                        generate_args_code(
                            opts.clone(),
                            compiler,
                            l.clone(),
                            &tl
                        ).and_then(|args| {
                            process_defun_call(opts.clone(), compiler, l.clone(), Rc::new(args), Rc::new(lookup))
                        })
                    },

                    Callable::CallPrim(p) => {
                        generate_args_code(opts, compiler, l.clone(), &tl).map(|args| {
                            CompiledCode(l.clone(), Rc::new(SExp::Cons(l,Rc::new(p),Rc::new(args))))
                        })
                    },

                    Callable::RunCompiler => {
                        if list.len() == 2 {
                            let updated_opts = opts.
                                set_assemble(false).
                                set_stdenv(false).
                                set_in_defun(true).
                                set_compiler(compiler.clone());

                            let use_body =
                                SExp::Cons(
                                    l.clone(),
                                    Rc::new(SExp::Atom (l.clone(), "mod".as_bytes().to_vec())),
                                    Rc::new(SExp::Cons(
                                        l.clone(),
                                        Rc::new(SExp::Nil(l.clone())),
                                        Rc::new(SExp::Cons(
                                            l.clone(),
                                            list[1].to_sexp(),
                                            Rc::new(SExp::Nil(l.clone()))
                                        ))
                                    ))
                                );

                            updated_opts.compile_program(
                                Rc::new(use_body)
                            ).map(|code| {
                                CompiledCode(l.clone(), Rc::new(primquote(l.clone(), Rc::new(code))))
                            })
                        } else {
                            error
                        }
                    }
                })
        }
        _ => {
            error
        }
    }
}

fn generate_expr_code(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    expr: Rc<BodyForm>
) -> Result<CompiledCode, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(l,bindings,expr) => {
            /* Depends on a defun having been desugared from this let and the let
            expressing rewritten. */
            generate_expr_code(opts, compiler, expr.clone())
        },
        BodyForm::Quoted(q) => {
            let l = q.loc();
            Ok(CompiledCode(l.clone(), Rc::new(primquote(l.clone(), Rc::new(q.clone())))))
        },
        BodyForm::Value(v) => {
            match v.borrow() {
                SExp::Atom(l,atom) => {
                    if *atom == "@".as_bytes().to_vec() {
                        Ok(CompiledCode(l.clone(), Rc::new(SExp::Integer(l.clone(), bi_one()))))
                    } else {
                        create_name_lookup(compiler, l.clone(), atom).map(|f| {
                            CompiledCode(l.clone(), f)
                        })
                    }
                },
                _ => {
                    Ok(CompiledCode(v.loc(), Rc::new(primquote(v.loc(), Rc::new(v.clone())))))
                }
            }
        },
        BodyForm::Call(l,list) => {
            if list.len() == 0 {
                Err(CompileErr(l.clone(), "created a call with no forms".to_string()))
            } else {
                compile_call(l.clone(), opts, compiler, list.to_vec())
            }
        },
        _ => {
            Err(CompileErr(
                expr.loc(),
                format!(
                    "don't know how to compile {}",
                    expr.to_sexp().to_string()
                )
            ))
        }
    }
}

fn combine_defun_env(old_env: Rc<SExp>, new_args: Rc<SExp>) -> Rc<SExp> {
    match old_env.borrow() {
        SExp::Cons(l,h,_) => {
            Rc::new(SExp::Cons(l.clone(),h.clone(),new_args.clone()))
        },
        _ => old_env
    }
}

fn codegen_(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    h: &HelperForm
) -> Result<PrimaryCodegen, CompileErr> {
    match h {
        HelperForm::Defconstant(loc, name, body) => {
            let expand_program =
                CompileForm {
                    loc: loc.clone(),
                    args: Rc::new(SExp::Nil(loc.clone())),
                    helpers: Vec::new(),
                    exp: body.clone()
                }.to_sexp();

            let updated_opts = opts.set_compiler(compiler.clone());
            let code = updated_opts.compile_program(expand_program)?;
            run(Rc::new(code), Rc::new(SExp::Nil(loc.clone()))).map_err(|r| {
                CompileErr(
                    loc.clone(),
                    format!(
                        "Error evaluating constant: {}",
                        r.to_string()
                    )
                )
            }).map(|res| {
                let quoted = primquote(loc.clone(), Rc::new(res));
                compiler.add_constant(&name, Rc::new(quoted))
            })
        },

        HelperForm::Defmacro(_loc, name, _args, body) => {
            let macro_program = body.to_sexp();
            let updated_opts =
                opts.
                set_compiler(compiler.clone()).
                set_assemble(false).
                set_stdenv(false);

            opts.compile_program(macro_program).map(|code| {
                compiler.add_macro(name, Rc::new(code))
            })
        }

        HelperForm::Defun (loc, name, _inline, args, body) => {
            let updated_opts =
                opts.
                set_compiler(compiler.clone()).
                set_in_defun(true).
                set_assemble(false).
                set_stdenv(false).
                set_start_env(Some(
                    combine_defun_env(compiler.env.clone(), args.clone())
                ));

            let tocompile =
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Atom(loc.clone(),"mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        args.clone(),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            body.to_sexp(),
                            Rc::new(SExp::Nil(loc.clone()))
                        ))
                    ))
                );

            updated_opts.compile_program(Rc::new(tocompile)).map(|code| {
                compiler.add_defun(name, DefunCall {
                    required_env: args.clone(),
                    code: Rc::new(code)
                })
            })
        }
    }
}

fn is_defun(b: &HelperForm) -> bool {
    match b {
        HelperForm::Defun(_,_,_,_,_) => true,
        _ => false
    }
}

pub fn empty_compiler(l: Srcloc) -> PrimaryCodegen {
    let mut prim_map = HashMap::new();
    for p in prims() {
        prim_map.insert(p.0.as_bytes().to_vec(), Rc::new(p.1));
    }

    let nil = SExp::Nil(l.clone());
    let nil_rc = Rc::new(nil.clone());

    PrimaryCodegen {
        prims: prim_map,
        constants: HashMap::new(),
        macros: HashMap::new(),
        defuns: HashMap::new(),
        parentfns: HashMap::new(),
        env: Rc::new(SExp::Cons(l.clone(), nil_rc.clone(), nil_rc.clone())),
        to_process: Vec::new(),
        final_expr: Rc::new(BodyForm::Quoted(nil.clone())),
        final_code: None
    }
}

fn generate_let_defun(
    compiler: &PrimaryCodegen,
    l: Srcloc,
    name: &Vec<u8>,
    bindings: Vec<Rc<Binding>>,
    body: Rc<BodyForm>
) -> HelperForm {
    let args =
        match compiler.env.borrow() {
            SExp::Cons(l, _, fnargs) => {
                fnargs.clone()
            },
            _ => Rc::new(SExp::Nil(compiler.env.loc()))
        };

    let new_arguments: Vec<Rc<SExp>> =
        bindings.iter().map(|b| {
            Rc::new(SExp::Atom(l.clone(), name.clone()))
        }).collect();

    let inner_function_args =
        SExp::Cons(
            l.clone(),
            args,
            Rc::new(list_to_cons(l.clone(), &new_arguments))
        );

    HelperForm::Defun(l.clone(), name.clone(), true, Rc::new(inner_function_args), body)
}

fn generate_let_args(l: Srcloc, blist: Vec<Rc<Binding>>) -> Vec<Rc<BodyForm>> {
    blist.iter().map(|b| b.body.clone()).collect()
}

fn hoist_body_let_binding(
    compiler: &PrimaryCodegen,
    body: Rc<BodyForm>
) -> (Vec<HelperForm>, Rc<BodyForm>) {
    match body.borrow() {
        BodyForm::Let(l, bindings, body) => {
            let defun_name = gensym("letbinding".as_bytes().to_vec());
            let generated_defun = generate_let_defun(
                compiler,
                l.clone(),
                &defun_name,
                bindings.to_vec(),
                body.clone()
            );
            let mut let_args = generate_let_args(l.clone(), bindings.to_vec());
            let pass_env = BodyForm::Call(
                l.clone(),
                vec!(
                    Rc::new(BodyForm::Value(SExp::Atom(l.clone(),"r".as_bytes().to_vec()))),
                    Rc::new(BodyForm::Value(SExp::Atom(l.clone(),"@".as_bytes().to_vec())))
                )
            );

            let mut call_args = Vec::new();
            call_args.push(Rc::new(BodyForm::Value(SExp::Atom(l.clone(), defun_name))));
            call_args.push(Rc::new(pass_env.clone()));
            call_args.append(&mut let_args);

            (vec!(generated_defun), Rc::new(BodyForm::Call(l.clone(), call_args)))
        },
        _ => (Vec::new(), body.clone())
    }
}

fn process_helper_let_bindings(
    compiler: &PrimaryCodegen,
    helpers: &Vec<HelperForm>
) -> Vec<HelperForm> {
    let mut subcompiler = compiler.clone();
    let mut result = helpers.clone();
    let mut i = 0;

    while i < result.len() {
        match result[i].clone() {
            HelperForm::Defun(l, name, inline, args, body) => {
                let helper_result = hoist_body_let_binding(compiler, body.clone());
                let hoisted_helpers = helper_result.0;
                let hoisted_body = helper_result.1.clone();

                result.insert(i, HelperForm::Defun(
                    l.clone(),
                    name.clone(),
                    inline,
                    args.clone(),
                    hoisted_body
                ));
                i += 1;

                for j in 0..hoisted_helpers.len() {
                    result.insert(i+j, hoisted_helpers[j].clone());
                }

                subcompiler = compiler.set_env(
                    combine_defun_env(compiler.env.clone(), args.clone())
                );
            },
            _ => {
                i += 1;
            }
        }
    }

    return result;
}

fn start_codegen(opts: Rc<dyn CompilerOpts>, comp: CompileForm) -> PrimaryCodegen {
    let mut use_compiler =
        match opts.compiler() {
            None => empty_compiler(comp.loc.clone()),
            Some(c) => c
        };

    let hoisted_bindings = hoist_body_let_binding(&use_compiler, comp.exp);
    let mut new_helpers = hoisted_bindings.0;
    let expr = hoisted_bindings.1;
    new_helpers.append(&mut comp.helpers.clone());
    let let_helpers_with_expr =
      process_helper_let_bindings(&use_compiler.clone(), &new_helpers);
    let live_helpers =
        let_helpers_with_expr.iter().filter(|x| is_defun(x)).map(|x| x.clone()).collect();

    use_compiler.env =
        match opts.start_env() {
            Some(env) => env,
            None => Rc::new(compute_env_shape(comp.loc.clone(), comp.args.clone(), &live_helpers))
        };
    use_compiler.to_process = let_helpers_with_expr;
    use_compiler.final_expr = expr.clone();

    use_compiler
}

fn final_codegen(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    comp: &CompileForm
) -> Result<PrimaryCodegen, CompileErr> {
    generate_expr_code(opts, compiler, compiler.final_expr.clone()).map(|code| {
        let mut final_comp = compiler.clone();
        final_comp.final_code = Some(CompiledCode(comp.loc.clone(),code.1));
        final_comp
    })
}

/*
fn finalize_env_(
    opts: Rc<dyn CompilerOpts>,
    c: &PrimaryCodegen,
    l: Srcloc,
    env: Rc<SExp>
) -> Result<SExp, CompileErr> {
    match env.borrow() {
        SExp::Atom(l,v) => {
            match c.defuns.get(v) {
                Some(res) => Ok(res.code),
                None => {
                    /* Parentfns are functions in progress in the parent */
                    if c.parentns.contains(v) {
                        Ok(SExp::Nil(l.clone()))
                    } else {
                        Err(CompileErr(
                            l.clone(),
                            format!("A defun was referenced in the defun env but not found {}", v.to_string())
                        ))
                    }
                }
            }
        },

        SExp::Cons (l,h,r) => {
            finalize_env_ opts c l h
                |> compBind
                (fun h ->
                 finalize_env_ opts c l r |> compMap (fun r -> Cons (l,h,r))
                )
        },

        _ => Ok(env)
    }
}

and finalize_env opts c =
  match c.env with
  | Cons (l,h,_) -> finalize_env_ opts c l h
  | any -> CompileOk any

and dummy_functions compiler =
  List.fold_left
    (fun c -> function
       | Defconstant _ -> c
       | Defmacro _ -> c
       | Defun (_,name,_,_,_) ->
         { c with parentfns = StringSet.add name c.parentfns }
    )
    compiler
    compiler.to_process

and codegen opts cmod =
  let compiler =
    start_codegen opts cmod
    |> dummy_functions
  in
  List.fold_left
    (fun c f -> c |> compBind (fun comp -> codegen_ opts comp f))
    (CompileOk compiler)
    compiler.to_process
  |> compBind (final_codegen opts)
  |> compBind
    (fun c ->
       finalize_env opts c
       |> compBind
         (fun final_env ->
            match c.final_code with
            | None ->
              CompileError (Srcloc.start opts.filename, "Failed to generate code")
            | Some (Code (l,code)) ->
              if opts.inDefun then
                let final_code =
                  (primapply
                     l
                     (primquote l code)
                     (Integer (l,"1"))
                  )
                in
                CompileOk final_code
              else
                let final_code =
                  (primapply
                     l
                     (primquote l code)
                     (primcons
                        l
                        (primquote l final_env)
                        (Integer (l,"1"))
                     )
                  )
                in
                CompileOk final_code
         )
    )
*/
