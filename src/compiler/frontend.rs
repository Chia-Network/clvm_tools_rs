use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::comptypes::{
    Binding,
    BodyForm,
    CompileErr,
    CompileForm,
    CompilerOpts,
    HelperForm,
    LetFormKind,
    ModAccum,
    TypeAnnoKind,
    list_to_cons,
};
use crate::compiler::preprocessor::preprocess;
use crate::compiler::rename::rename_children_compileform;
use crate::compiler::sexp::{enlist, SExp};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::{
    parse_type_sexp
};
use crate::compiler::types::ast::{
    Polytype,
    Type,
    TypeVar
};
use crate::util::u8_from_number;

fn collect_used_names_sexp(body: Rc<SExp>) -> Vec<Vec<u8>> {
    match body.borrow() {
        SExp::Atom(_, name) => vec![name.to_vec()],
        SExp::Cons(_, head, tail) => {
            let mut head_collected = collect_used_names_sexp(head.clone());
            let mut tail_collected = collect_used_names_sexp(tail.clone());
            head_collected.append(&mut tail_collected);
            head_collected
        }
        _ => vec![],
    }
}

fn collect_used_names_binding(body: &Binding) -> Vec<Vec<u8>> {
    collect_used_names_bodyform(body.body.borrow())
}

fn collect_used_names_bodyform(body: &BodyForm) -> Vec<Vec<u8>> {
    match body {
        BodyForm::Let(_, _, bindings, expr) => {
            let mut result = Vec::new();
            for b in bindings {
                let mut new_binding_names = collect_used_names_binding(b);
                result.append(&mut new_binding_names);
            }

            let mut body_names = collect_used_names_bodyform(expr);
            result.append(&mut body_names);
            result
        }
        BodyForm::Quoted(_) => vec![],
        BodyForm::Value(atom) => match atom.borrow() {
            SExp::Atom(_l, v) => vec![v.to_vec()],
            SExp::Cons(_l, f, r) => {
                let mut first_names = collect_used_names_sexp(f.clone());
                let mut rest_names = collect_used_names_sexp(r.clone());
                first_names.append(&mut rest_names);
                first_names
            }
            _ => Vec::new(),
        },
        BodyForm::Call(_l, vs) => {
            let mut result = Vec::new();
            for a in vs {
                let mut argnames = collect_used_names_bodyform(a);
                result.append(&mut argnames);
            }
            result
        }
    }
}

fn collect_used_names_helperform(body: &HelperForm) -> Vec<Vec<u8>> {
    match body {
        HelperForm::Deftype(_, _, _, _) => Vec::new(),
        HelperForm::Defconstant(_, _, value, _) => {
            collect_used_names_bodyform(value)
        },
        HelperForm::Defmacro(_, _, _, body) => {
            collect_used_names_compileform(body)
        },
        HelperForm::Defun(_, _, _, _, body, _) => {
            collect_used_names_bodyform(body)
        },
    }
}

fn collect_used_names_compileform(body: &CompileForm) -> Vec<Vec<u8>> {
    let mut result = Vec::new();
    for h in body.helpers.iter() {
        let mut helper_list = collect_used_names_helperform(h.borrow());
        result.append(&mut helper_list);
    }

    let mut ex_list = collect_used_names_bodyform(body.exp.borrow());
    result.append(&mut ex_list);
    result
}

fn calculate_live_helpers(
    opts: Rc<dyn CompilerOpts>,
    last_names: &HashSet<Vec<u8>>,
    names: &HashSet<Vec<u8>>,
    helper_map: &HashMap<Vec<u8>, HelperForm>,
) -> HashSet<Vec<u8>> {
    if last_names.len() == names.len() {
        names.clone()
    } else {
        let new_names: HashSet<Vec<u8>> =
            names.difference(last_names).map(|x| x.to_vec()).collect();
        let mut needed_helpers: HashSet<Vec<u8>> = names.clone();

        for name in new_names {
            match helper_map.get(&name) {
                Some(new_helper) => {
                    let even_newer_names: HashSet<Vec<u8>> =
                        collect_used_names_helperform(new_helper)
                            .iter()
                            .map(|x| x.to_vec())
                            .collect();
                    needed_helpers = needed_helpers
                        .union(&even_newer_names)
                        .into_iter()
                        .map(|x| x.to_vec())
                        .collect();
                }
                _ => {}
            }
        }

        calculate_live_helpers(opts, names, &needed_helpers, helper_map)
    }
}

fn qq_to_expression(body: Rc<SExp>) -> Result<BodyForm, CompileErr> {
    let body_copy: &SExp = body.borrow();

    match body.borrow() {
        SExp::Cons(l, f, r) => {
            let op = match f.borrow() {
                SExp::Atom(_, o) => o.clone(),
                SExp::QuotedString(_, _, s) => s.clone(),
                SExp::Integer(_, i) => u8_from_number(i.clone()),
                _ => Vec::new(),
            };

            if op.len() == 1 && (op[0] == 'q' as u8 || op[0] == 1) {
                return Ok(BodyForm::Quoted(body_copy.clone()));
            } else {
                match r.proper_list() {
                    Some(list) => {
                        if *op == "quote".as_bytes().to_vec() {
                            if list.len() != 1 {
                                return Err(CompileErr(
                                    l.clone(),
                                    format!("bad form {}", body.to_string()),
                                ));
                            }

                            return Ok(BodyForm::Quoted(list[0].clone()));
                        } else if *op == "unquote".as_bytes().to_vec() {
                            if list.len() != 1 {
                                return Err(CompileErr(
                                    l.clone(),
                                    format!("bad form {}", body.to_string()),
                                ));
                            }

                            return compile_bodyform(Rc::new(list[0].clone()));
                        }
                    }
                    _ => {}
                }
            }

            qq_to_expression_list(body.clone())
        }
        _ => Ok(BodyForm::Quoted(body_copy.clone())),
    }
}

fn qq_to_expression_list(body: Rc<SExp>) -> Result<BodyForm, CompileErr> {
    match body.borrow() {
        SExp::Cons(l, f, r) => {
            m! {
                f_qq <- qq_to_expression(f.clone());
                r_qq <- qq_to_expression_list(r.clone());
                Ok(BodyForm::Call(l.clone(), vec!(
                    Rc::new(BodyForm::Value(
                        SExp::Atom(l.clone(), "c".as_bytes().to_vec())
                    )),
                    Rc::new(f_qq),
                    Rc::new(r_qq)
                )))
            }
        }
        SExp::Nil(l) => Ok(BodyForm::Quoted(SExp::Nil(l.clone()))),
        _ => Err(CompileErr(
            body.loc(),
            format!("Bad list tail in qq {}", body.to_string()),
        )),
    }
}

fn args_to_expression_list(body: Rc<SExp>) -> Result<Vec<Rc<BodyForm>>, CompileErr> {
    if body.nilp() {
        Ok(vec![])
    } else {
        match body.borrow() {
            SExp::Cons(_l, first, rest) => {
                let mut result_list = Vec::new();
                let f_compiled = compile_bodyform(first.clone())?;
                result_list.push(Rc::new(f_compiled));
                let mut args = args_to_expression_list(rest.clone())?;
                result_list.append(&mut args);
                Ok(result_list)
            }
            _ => Err(CompileErr(
                body.loc(),
                "Bad arg list tail ".to_string() + &body.to_string(),
            )),
        }
    }
}

fn make_let_bindings(body: Rc<SExp>) -> Result<Vec<Rc<Binding>>, CompileErr> {
    let err = Err(CompileErr(
        body.loc(),
        "Bad binding tail ".to_string() + &body.to_string(),
    ));
    match body.borrow() {
        SExp::Nil(_) => Ok(vec![]),
        SExp::Cons(_, head, tl) => head
            .proper_list()
            .map(|x| match &x[..] {
                [SExp::Atom(l, name), expr] => {
                    let compiled_body = compile_bodyform(Rc::new(expr.clone()))?;
                    let mut result = Vec::new();
                    let mut rest_bindings = make_let_bindings(tl.clone())?;
                    result.push(Rc::new(Binding {
                        loc: l.clone(),
                        name: name.to_vec(),
                        body: Rc::new(compiled_body),
                    }));
                    result.append(&mut rest_bindings);
                    Ok(result)
                }
                _ => err.clone(),
            })
            .unwrap_or_else(|| err.clone()),
        _ => err.clone(),
    }
}

pub fn compile_bodyform(body: Rc<SExp>) -> Result<BodyForm, CompileErr> {
    match body.borrow() {
        SExp::Cons(l, op, tail) => {
            let application = || {
                args_to_expression_list(tail.clone()).and_then(|args| {
                    compile_bodyform(op.clone()).map(|func| {
                        let mut result_call = vec![Rc::new(func)];
                        let mut args_clone = args.to_vec();
                        result_call.append(&mut args_clone);
                        BodyForm::Call(l.clone(), result_call)
                    })
                })
            };

            let finish_err = |site| {
                Err(CompileErr(
                    l.clone(),
                    format!("{}: bad argument list for form {}", site, body.to_string()),
                ))
            };

            match op.borrow() {
                SExp::Atom(l, atom_name) => {
                    if *atom_name == "q".as_bytes().to_vec()
                        || (atom_name.len() == 1 && atom_name[0] == 1)
                    {
                        let tail_copy: &SExp = tail.borrow();
                        return Ok(BodyForm::Quoted(tail_copy.clone()));
                    }

                    match tail.proper_list() {
                        Some(v) => {
                            if *atom_name == "let".as_bytes().to_vec()
                                || *atom_name == "let*".as_bytes().to_vec()
                            {
                                if v.len() != 2 {
                                    return finish_err("let");
                                }

                                let kind = if *atom_name == "let".as_bytes().to_vec() {
                                    LetFormKind::Parallel
                                } else {
                                    LetFormKind::Sequential
                                };

                                let bindings = v[0].clone();
                                let body = v[1].clone();

                                let let_bindings = make_let_bindings(Rc::new(bindings.clone()))?;
                                let compiled_body = compile_bodyform(Rc::new(body.clone()))?;
                                Ok(BodyForm::Let(
                                    l.clone(),
                                    kind,
                                    let_bindings,
                                    Rc::new(compiled_body),
                                ))
                            } else if *atom_name == "quote".as_bytes().to_vec() {
                                if v.len() != 1 {
                                    return finish_err("quote");
                                }

                                let quote_body = v[0].clone();

                                Ok(BodyForm::Quoted(quote_body.clone()))
                            } else if *atom_name == "qq".as_bytes().to_vec() {
                                if v.len() != 1 {
                                    return finish_err("qq");
                                }

                                let quote_body = v[0].clone();

                                qq_to_expression(Rc::new(quote_body.clone()))
                            } else {
                                application()
                            }
                        }
                        None => finish_err("tail_proper"),
                    }
                }
                SExp::Integer(il, i) => compile_bodyform(Rc::new(SExp::Cons(
                    il.clone(),
                    Rc::new(SExp::Atom(il.clone(), u8_from_number(i.clone()))),
                    tail.clone(),
                ))),
                SExp::QuotedString(_, _, _) => {
                    let body_copy: &SExp = body.borrow();
                    Ok(BodyForm::Value(body_copy.clone()))
                }
                SExp::Nil(_l) => {
                    let body_copy: &SExp = body.borrow();
                    Ok(BodyForm::Quoted(body_copy.clone()))
                }
                SExp::Cons(_, _, _) => finish_err("bad cons"),
            }
        }
        _ => {
            let body_copy: &SExp = body.borrow();
            Ok(BodyForm::Value(body_copy.clone()))
        }
    }
}

fn compile_defconstant(l: Srcloc, name: Vec<u8>, body: Rc<SExp>) -> Result<HelperForm, CompileErr> {
    compile_bodyform(body).map(|bf| HelperForm::Defconstant(l, name.to_vec(), Rc::new(bf), None))
}

fn compile_defun(
    l: Srcloc,
    inline: bool,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
    ty: Option<Polytype>
) -> Result<HelperForm, CompileErr> {
    let mut take_form = body.clone();
    match body.borrow() {
        SExp::Cons(_, f, _r) => {
            take_form = f.clone();
        }
        _ => {}
    }
    compile_bodyform(take_form)
        .map(|bf| HelperForm::Defun(l, name, inline, args.clone(), Rc::new(bf), ty))
}

fn compile_defmacro(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
) -> Result<HelperForm, CompileErr> {
    let program = SExp::Cons(
        l.clone(),
        Rc::new(SExp::Atom(l.clone(), "mod".as_bytes().to_vec())),
        Rc::new(SExp::Cons(l.clone(), args.clone(), body.clone())),
    );
    let new_opts = opts.set_stdenv(false);
    frontend(new_opts, vec![Rc::new(program)])
        .map(|p| HelperForm::Defmacro(l, name, args.clone(), Rc::new(p)))
}

enum TypeKind {
    Arrow,
    Colon
}

struct ParseBodyformMatch {
    op_name: Vec<u8>,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
    ty: Option<(TypeKind, Rc<SExp>)>
}

fn match_op_name_4(
    body: Rc<SExp>,
    pl: &Vec<SExp>,
) -> Option<ParseBodyformMatch> {
    let l = body.loc();

    if pl.len() < 1 {
        return None;
    }

    match &pl[0] {
        SExp::Atom(_, op_name) => {
            if pl.len() < 3 {
                return Some(ParseBodyformMatch {
                    op_name: op_name.clone(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                    ty: None
                });
            }

            match &pl[1] {
                SExp::Atom(_, name) => {
                    let mut tail_idx = 3;
                    let mut tail_list = Vec::new();
                    let mut type_anno = None;
                    if pl.len() > 3 {
                        if let SExp::Atom(_, colon) = &pl[3] {
                            if *colon == vec![b':'] {
                                // Type annotation
                                tail_idx += 2;
                                type_anno = Some((TypeKind::Colon, Rc::new(pl[4].clone())));
                            } else if *colon == vec![b'-',b'>'] {
                                // Type annotation
                                tail_idx += 2;
                                type_anno = Some((TypeKind::Arrow, Rc::new(pl[4].clone())));
                            }
                        }
                    }
                    for elt in pl.iter().skip(tail_idx) {
                        tail_list.push(Rc::new(elt.clone()));
                    }
                    Some(ParseBodyformMatch {
                        op_name: op_name.clone(),
                        name: name.clone(),
                        args: Rc::new(pl[2].clone()),
                        body: Rc::new(enlist(l.clone(), tail_list)),
                        ty: type_anno
                    })
                }
                _ => Some(ParseBodyformMatch {
                    op_name: op_name.clone(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                    ty: None
                }),
            }
        }
        _ => None,
    }
}

fn extract_type_variables_from_forall_stack(
    tvars: &mut Vec<TypeVar>,
    t: &Polytype
) -> Polytype {
    if let Type::TForall(v,t1) = t {
        tvars.push(v.clone());
        extract_type_variables_from_forall_stack(tvars, t1.borrow())
    } else {
        t.clone()
    }
}

struct ArgTypeResult {
    stripped_args: Rc<SExp>,
    individual_types: HashMap<Vec<u8>, Polytype>,
    whole_args: Polytype
}

fn recover_arg_type_inner(
    individual_types: &mut HashMap<Vec<u8>, Polytype>,
    args: Rc<SExp>,
    have_anno: bool
) -> Result<(bool, Rc<SExp>, Polytype), CompileErr> {
    match args.borrow() {
        SExp::Nil(l) => Ok((have_anno, args.clone(), Type::TUnit(l.clone()))),
        SExp::Atom(l,n) => {
            individual_types.insert(n.clone(), Type::TAny(l.clone()));
            Ok((false, args.clone(), Type::TAny(l.clone())))
        },
        SExp::Cons(l,a,b) => {
            // There are a few cases:
            // (normal destructuring)
            // (@ name sub)
            // (@ name sub : ty)
            // (X : ty)
            // We want to catch the final case and pass through its unannotated
            // counterpart.
            if let Some(lst) = args.proper_list() {
                // Dive in
                if lst.len() == 5 {
                    if let (SExp::Atom(l,n), SExp::Atom(l2,n2)) =
                        (&lst[0], &lst[3]) {
                            if n == &vec![b'@'] && n2 == &vec![b':'] {
                                // At capture with annotation
                                todo!()
                            };
                        };
                } else if lst.len() == 3 {
                    if let SExp::Atom(l1,n1) = &lst[1] {
                        if n1 == &vec![b':'] {
                            // Name with annotation
                            let ty = parse_type_sexp(Rc::new(lst[2].clone()))?;
                            return Ok((true, Rc::new(lst[0].clone()), ty));
                        };
                    };
                }
            }

            let (got_ty_a, stripped_a, ty_a) = recover_arg_type_inner(
                individual_types,
                a.clone(),
                have_anno
            )?;
            let (got_ty_b, stripped_b, ty_b) = recover_arg_type_inner(
                individual_types,
                b.clone(),
                have_anno
            )?;
            Ok((got_ty_a || got_ty_b,
                Rc::new(SExp::Cons(
                    l.clone(),
                    stripped_a,
                    stripped_b
                )),
                Type::TPair(Rc::new(ty_a), Rc::new(ty_b))
            ))
        },
        _ => Err(CompileErr(args.loc(), "unrecognized argument form".to_string()))
    }
}

fn recover_arg_type(args: Rc<SExp>) -> Result<Option<ArgTypeResult>, CompileErr> {
    let mut individual_types = HashMap::new();
    let (got_any, stripped, ty) = recover_arg_type_inner(
        &mut individual_types,
        args.clone(),
        false
    )?;
    if got_any {
        Ok(Some(ArgTypeResult {
            stripped_args: stripped,
            individual_types: individual_types,
            whole_args: ty
        }))
    } else {
        Ok(None)
    }
}

// Returns None if result_ty is None and there are no type signatures recovered
// from the args.
//
// If the function's type signature is given with a TForall, the type variables
// given will be in scope for the arguments.
// If type arguments are given, the function's type signature must not be given
// as a function type (since all functions are arity-1 in chialisp).  The final
// result type will be enriched to include the argument types.
fn augment_fun_type_with_args(
    args: Rc<SExp>,
    result_ty: Option<TypeAnnoKind>
) -> Result<(Rc<SExp>, Option<Polytype>), CompileErr> {
    if let Some(atr) = recover_arg_type(args.clone())? {
        let mut tvars = Vec::new();

        let actual_result_ty =
            if let Some(TypeAnnoKind::Arrow(rty)) = result_ty {
                extract_type_variables_from_forall_stack(&mut tvars, &rty)
            } else if let Some(TypeAnnoKind::Colon(rty)) = result_ty {
                let want_rty = extract_type_variables_from_forall_stack(
                    &mut tvars,
                    &rty
                );
                // If it's a function type, we have to give it as "args"
                if let Type::TFun(t1,t2) = want_rty {
                    let t1_borrowed: &Polytype = t1.borrow();
                    if t1_borrowed != &Type::TVar(TypeVar("args".to_string(), t1.loc())) {
                        return Err(CompileErr(t1.loc(), "When arguments are annotated, if the full function type is given, it must be given as (args -> ...).  The 'args' type variable will contain the type implied by the individual argument annotations.".to_string()));
                    }

                    let t2_borrowed: &Polytype = t2.borrow();
                    t2_borrowed.clone()
                } else {
                    want_rty
                }
            } else {
                Type::TAny(args.loc())
            };

        Ok((atr.stripped_args.clone(), Some(actual_result_ty)))
    } else {
        // No arg types were given.  If a type was given for the result (non-fun)
        // use Any -> Any
        // else use the whole thing.
        Ok(result_ty.map(|rty| {
            match rty {
                TypeAnnoKind::Colon(t) => (args.clone(), Some(t.clone())),
                TypeAnnoKind::Arrow(t) => (
                    args.clone(),
                    Some(Type::TFun(
                        Rc::new(Type::TAny(args.loc())),
                        Rc::new(t.clone())
                    ))
                )
            }
        }).unwrap_or_else(|| {
            (args.clone(), None)
        }))
    }
}

fn compile_helperform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Option<HelperForm>, CompileErr> {
    let l = body.loc();
    let plist = body.proper_list();

    match plist.and_then(|pl| match_op_name_4(body.clone(), &pl)) {
        Some(res) => {
            let inline = res.op_name == "defun-inline".as_bytes().to_vec();
            if res.op_name == "defconstant".as_bytes().to_vec() {
                return compile_defconstant(l, res.name.to_vec(), res.args.clone()).map(|x| Some(x));
            } else if res.op_name == "defmacro".as_bytes().to_vec() {
                return compile_defmacro(opts, l, res.name.to_vec(), res.args.clone(), res.body.clone())
                    .map(|x| Some(x));
            } else if res.op_name == "defun".as_bytes().to_vec() || inline {
                let use_type_anno =
                    if let Some((k,ty)) = res.ty {
                        match k {
                            TypeKind::Arrow => Some(TypeAnnoKind::Arrow(parse_type_sexp(ty)?)),
                            TypeKind::Colon => Some(TypeAnnoKind::Colon(parse_type_sexp(ty)?)),
                        }
                    } else {
                        None
                    };

                let (stripped_args, parsed_type) =
                    augment_fun_type_with_args(res.args.clone(), use_type_anno)?;

                return compile_defun(
                    l,
                    inline,
                    res.name.to_vec(),
                    stripped_args,
                    res.body.clone(),
                    parsed_type
                ).map(|x| Some(x));
            }
        }
        _ => {}
    }

    Ok(None)
}

fn compile_mod_(
    mc: &ModAccum,
    opts: Rc<dyn CompilerOpts>,
    args: Rc<SExp>,
    content: Rc<SExp>,
    ty: Option<TypeAnnoKind>
) -> Result<ModAccum, CompileErr> {
    let (stripped_args, parsed_type) =
        augment_fun_type_with_args(args.clone(), ty.clone())?;

    match content.borrow() {
        SExp::Nil(l) => Err(CompileErr(
            l.clone(),
            "no expression at end of mod".to_string(),
        )),
        SExp::Cons(l, body, tail) => match tail.borrow() {
            SExp::Nil(_) => match mc.exp_form {
                Some(_) => Err(CompileErr(l.clone(), "too many expressions".to_string())),
                _ => Ok(mc.set_final(&CompileForm {
                    loc: mc.loc.clone(),
                    args: stripped_args.clone(),
                    helpers: mc.helpers.clone(),
                    exp: Rc::new(compile_bodyform(body.clone())?),
                    ty: parsed_type
                })),
            },
            _ => {
                let helper = compile_helperform(opts.clone(), body.clone())?;
                match helper {
                    None => Err(CompileErr(
                        l.clone(),
                        "only the last form can be an exprssion in mod".to_string(),
                    )),
                    Some(form) => match mc.exp_form {
                        None => {
                            compile_mod_(&mc.add_helper(form), opts, stripped_args.clone(), tail.clone(), ty)
                        }
                        Some(_) => Err(CompileErr(l.clone(), "too many expressions".to_string())),
                    },
                }
            }
        },
        _ => Err(CompileErr(
            content.loc(),
            format!("inappropriate sexp {}", content.to_string()),
        ))
    }
}

fn frontend_start(
    opts: Rc<dyn CompilerOpts>,
    pre_forms: Vec<Rc<SExp>>,
) -> Result<ModAccum, CompileErr> {
    if pre_forms.len() == 0 {
        Err(CompileErr(
            Srcloc::start(&opts.filename()),
            "empty source file not allowed".to_string(),
        ))
    } else {
        let finish = || {
            let loc = pre_forms[0].loc();
            frontend_start(
                opts.clone(),
                vec![Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::Atom(loc.clone(), "mod".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::Nil(loc.clone())),
                        Rc::new(list_to_cons(loc.clone(), &pre_forms)),
                    )),
                ))],
            )
        };
        let l = pre_forms[0].loc();
        pre_forms[0]
            .proper_list()
            .map(|x| {
                if x.len() < 3 {
                    return finish();
                }

                match &x[0] {
                    SExp::Atom(_, mod_atom) => {
                        if pre_forms.len() > 1 {
                            return Err(CompileErr(
                                pre_forms[0].loc(),
                                "one toplevel mod form allowed".to_string(),
                            ));
                        }

                        if *mod_atom == "mod".as_bytes().to_vec() {
                            let args = Rc::new(x[1].clone());
                            let mut skip_idx = 2;
                            let mut ty: Option<TypeAnnoKind> = None;

                            if let SExp::Atom(_,colon) = &x[2] {
                                if *colon == vec![b':'] && x.len() > 3 {
                                    let use_ty = parse_type_sexp(Rc::new(x[3].clone()))?;
                                    ty = Some(TypeAnnoKind::Colon(use_ty));
                                    skip_idx += 2;
                                } else if *colon == vec![b'-',b'>'] && x.len() > 3 {
                                    let use_ty = parse_type_sexp(Rc::new(x[3].clone()))?;
                                    ty = Some(TypeAnnoKind::Arrow(use_ty));
                                    skip_idx += 2;
                                }
                            }

                            let body_vec = x.iter().skip(skip_idx).map(|s| Rc::new(s.clone())).collect();
                            let body = Rc::new(enlist(pre_forms[0].loc(), body_vec));

                            let ls = preprocess(opts.clone(), body.clone())?;
                            return compile_mod_(
                                &ModAccum::new(l.clone()),
                                opts.clone(),
                                args.clone(),
                                Rc::new(list_to_cons(l, &ls)),
                                ty
                            );
                        }
                    }
                    _ => {}
                }

                finish()
            })
            .unwrap_or_else(finish)
    }
}

pub fn frontend(
    opts: Rc<dyn CompilerOpts>,
    pre_forms: Vec<Rc<SExp>>,
) -> Result<CompileForm, CompileErr> {
    let started = frontend_start(opts.clone(), pre_forms)?;

    let compiled: Result<CompileForm, CompileErr> = match started.exp_form {
        None => Err(CompileErr(
            started.loc,
            "mod must end on an expression".to_string(),
        )),
        Some(v) => {
            let compiled_val: &CompileForm = v.borrow();
            Ok(compiled_val.clone())
        }
    };

    let our_mod = rename_children_compileform(&compiled?);

    let expr_names: HashSet<Vec<u8>> = collect_used_names_bodyform(our_mod.exp.borrow())
        .iter()
        .map(|x| x.to_vec())
        .collect();

    let helper_list = our_mod.helpers.iter().map(|h| (h.name(), h));
    let mut helper_map = HashMap::new();

    let _ = for hpair in helper_list {
        helper_map.insert(hpair.0.clone(), hpair.1.clone());
    };

    let helper_names =
        calculate_live_helpers(opts.clone(), &HashSet::new(), &expr_names, &helper_map);

    let mut live_helpers = Vec::new();
    for h in our_mod.helpers {
        if helper_names.contains(h.name()) {
            live_helpers.push(h);
        }
    }

    Ok(CompileForm {
        loc: our_mod.loc.clone(),
        args: our_mod.args.clone(),
        helpers: live_helpers,
        exp: our_mod.exp.clone(),
        ty: our_mod.ty.clone()
    })
}

fn is_quote_op(sexp: Rc<SExp>) -> bool {
    match sexp.borrow() {
        SExp::Atom(_, name) => name.len() == 1 && name[0] as char == 'q',
        SExp::Integer(_, v) => v == &bi_one(),
        _ => false,
    }
}

fn from_clvm_args(args: Rc<SExp>) -> Rc<SExp> {
    match args.borrow() {
        SExp::Cons(l, arg, rest) => {
            let new_arg = from_clvm(arg.clone());
            let new_rest = from_clvm_args(rest.clone());
            Rc::new(SExp::Cons(l.clone(), new_arg, new_rest))
        }
        _ => {
            // Treat tail of proper application list as expression.
            from_clvm(args.clone())
        }
    }
}

// Form proper frontend code from CLVM.
// The languages are related but not identical:
// - Left env references refer to functions from the env.
// - Right env references refer to user arguments.
// We can introduce defconstant helpers that allow us to keep track of what's
// being called via 'a' and use that information.
// Bare numbers in operator position are only prims.
// Bare numbers in argument position are references, rewrite as (@ ..)
pub fn from_clvm(sexp: Rc<SExp>) -> Rc<SExp> {
    match sexp.borrow() {
        SExp::Atom(l, _name) => {
            // An atom encountered as an expression is treated as a path.
            from_clvm(Rc::new(SExp::Integer(l.clone(), sexp.to_bigint().unwrap())))
        }
        SExp::QuotedString(l, _, _v) => {
            // A string is treated as a number.
            // An atom encountered as an expression is treated as a path.
            from_clvm(Rc::new(SExp::Integer(l.clone(), sexp.to_bigint().unwrap())))
        }
        SExp::Integer(l, _n) => {
            // A number is treated as a reference in expression position.
            // Results in (@ n).
            Rc::new(SExp::Cons(
                l.clone(),
                Rc::new(SExp::atom_from_string(l.clone(), &"@".to_string())),
                Rc::new(SExp::Cons(
                    l.clone(),
                    sexp.clone(),
                    Rc::new(SExp::Nil(l.clone())),
                )),
            ))
        }
        SExp::Nil(_l) => {
            // Nil represents nil in both systems.
            sexp.clone()
        }
        SExp::Cons(l, op, args) => {
            // This expression represents applying some primitive.
            if is_quote_op(op.clone()) {
                Rc::new(SExp::Cons(
                    l.clone(),
                    Rc::new(SExp::atom_from_string(l.clone(), &"q".to_string())),
                    args.clone(),
                ))
            } else {
                let new_args = from_clvm_args(args.clone());
                Rc::new(SExp::Cons(l.clone(), op.clone(), new_args))
            }
        }
    }
}
