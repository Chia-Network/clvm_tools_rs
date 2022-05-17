use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::comptypes::{
    list_to_cons, Binding, BodyForm, CompileErr, CompileForm, CompilerOpts, HelperForm,
    LetFormKind, ModAccum,
};
use crate::compiler::preprocessor::preprocess;
use crate::compiler::rename::rename_children_compileform;
use crate::compiler::sexp::{enlist, SExp};
use crate::compiler::srcloc::Srcloc;
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
        HelperForm::Defconstant(_, _, value) => collect_used_names_bodyform(value),
        HelperForm::Defmacro(_, _, _, body) => collect_used_names_compileform(body),
        HelperForm::Defun(_, _, _, _, body) => collect_used_names_bodyform(body),
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
                SExp::Nil(l) => {
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
    compile_bodyform(body).map(|bf| HelperForm::Defconstant(l, name.to_vec(), Rc::new(bf)))
}

fn compile_defun(
    l: Srcloc,
    inline: bool,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
) -> Result<HelperForm, CompileErr> {
    let mut take_form = body.clone();
    match body.borrow() {
        SExp::Cons(_, f, r) => {
            take_form = f.clone();
        }
        _ => {}
    }
    compile_bodyform(take_form)
        .map(|bf| HelperForm::Defun(l, name, inline, args.clone(), Rc::new(bf)))
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

fn match_op_name_4(
    body: Rc<SExp>,
    pl: &Vec<SExp>,
) -> Option<(Vec<u8>, Vec<u8>, Rc<SExp>, Rc<SExp>)> {
    let l = body.loc();

    if pl.len() < 1 {
        return None;
    }

    match &pl[0] {
        SExp::Atom(_, op_name) => {
            if pl.len() < 3 {
                return Some((
                    op_name.clone(),
                    Vec::new(),
                    Rc::new(SExp::Nil(l.clone())),
                    Rc::new(SExp::Nil(l.clone())),
                ));
            }

            match &pl[1] {
                SExp::Atom(_, name) => {
                    let mut tail_list = Vec::new();
                    for elt in pl.iter().skip(3) {
                        tail_list.push(Rc::new(elt.clone()));
                    }
                    Some((
                        op_name.clone(),
                        name.clone(),
                        Rc::new(pl[2].clone()),
                        Rc::new(enlist(l.clone(), tail_list)),
                    ))
                }
                _ => Some((
                    op_name.clone(),
                    Vec::new(),
                    Rc::new(SExp::Nil(l.clone())),
                    Rc::new(SExp::Nil(l.clone())),
                )),
            }
        }
        _ => None,
    }
}

fn compile_helperform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Option<HelperForm>, CompileErr> {
    let l = body.loc();
    let plist = body.proper_list();

    match plist.and_then(|pl| match_op_name_4(body.clone(), &pl)) {
        Some((op_name, name, args, body)) => {
            if *op_name == "defconstant".as_bytes().to_vec() {
                return compile_defconstant(l, name.to_vec(), args.clone()).map(|x| Some(x));
            } else if *op_name == "defmacro".as_bytes().to_vec() {
                return compile_defmacro(opts, l, name.to_vec(), args.clone(), body.clone())
                    .map(|x| Some(x));
            } else if *op_name == "defun".as_bytes().to_vec() {
                return compile_defun(l, false, name.to_vec(), args.clone(), body.clone())
                    .map(|x| Some(x));
            } else if *op_name == "defun-inline".as_bytes().to_vec() {
                return compile_defun(l, true, name.to_vec(), args.clone(), body.clone())
                    .map(|x| Some(x));
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
) -> Result<ModAccum, CompileErr> {
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
                    args: args.clone(),
                    helpers: mc.helpers.clone(),
                    exp: Rc::new(compile_bodyform(body.clone())?),
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
                            compile_mod_(&mc.add_helper(form), opts, args.clone(), tail.clone())
                        }
                        Some(_) => Err(CompileErr(l.clone(), "too many expressions".to_string())),
                    },
                }
            }
        },
        _ => Err(CompileErr(
            content.loc(),
            format!("inappropriate sexp {}", content.to_string()),
        )),
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
                            let body_vec = x.iter().skip(2).map(|s| Rc::new(s.clone())).collect();
                            let body = Rc::new(enlist(pre_forms[0].loc(), body_vec));

                            let ls = preprocess(opts.clone(), body.clone())?;
                            return compile_mod_(
                                &ModAccum::new(l.clone()),
                                opts.clone(),
                                args.clone(),
                                Rc::new(list_to_cons(l, &ls)),
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
        SExp::Atom(l, name) => {
            // An atom encountered as an expression is treated as a path.
            from_clvm(Rc::new(SExp::Integer(l.clone(), sexp.to_bigint().unwrap())))
        }
        SExp::QuotedString(l, _, v) => {
            // A string is treated as a number.
            // An atom encountered as an expression is treated as a path.
            from_clvm(Rc::new(SExp::Integer(l.clone(), sexp.to_bigint().unwrap())))
        }
        SExp::Integer(l, n) => {
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
        SExp::Nil(l) => {
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
