use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::compiler::comptypes::{
    list_to_cons, Binding, BodyForm, CompileErr, CompileForm, CompilerOpts, DefconstData,
    DefmacData, DefunData, HelperForm, IncludeDesc, LetData, LetFormKind, ModAccum,
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
        BodyForm::Let(_, letdata) => {
            let mut result = Vec::new();
            for b in letdata.bindings.iter() {
                let mut new_binding_names = collect_used_names_binding(b);
                result.append(&mut new_binding_names);
            }

            let mut body_names = collect_used_names_bodyform(letdata.body.borrow());
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
        BodyForm::Mod(_, _) => vec![],
    }
}

fn collect_used_names_helperform(body: &HelperForm) -> Vec<Vec<u8>> {
    match body {
        HelperForm::Defconstant(defc) => collect_used_names_bodyform(defc.body.borrow()),
        HelperForm::Defmacro(mac) => collect_used_names_compileform(mac.program.borrow()),
        HelperForm::Defun(_, defun) => collect_used_names_bodyform(&defun.body),
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
            if let Some(new_helper) = helper_map.get(&name) {
                let even_newer_names: HashSet<Vec<u8>> = collect_used_names_helperform(new_helper)
                    .iter()
                    .map(|x| x.to_vec())
                    .collect();
                needed_helpers = needed_helpers
                    .union(&even_newer_names)
                    .into_iter()
                    .map(|x| x.to_vec())
                    .collect();
            }
        }

        calculate_live_helpers(names, &needed_helpers, helper_map)
    }
}

fn qq_to_expression(opts: Rc<dyn CompilerOpts>, body: Rc<SExp>) -> Result<BodyForm, CompileErr> {
    let body_copy: &SExp = body.borrow();

    match body.borrow() {
        SExp::Cons(l, f, r) => {
            let op = match f.borrow() {
                SExp::Atom(_, o) => o.clone(),
                SExp::QuotedString(_, _, s) => s.clone(),
                SExp::Integer(_, i) => u8_from_number(i.clone()),
                _ => Vec::new(),
            };

            if op.len() == 1 && (op[0] == b'q' || op[0] == 1) {
                return Ok(BodyForm::Quoted(body_copy.clone()));
            } else if let Some(list) = r.proper_list() {
                if op == b"quote" {
                    if list.len() != 1 {
                        return Err(CompileErr(l.clone(), format!("bad form {}", body)));
                    }

                    return Ok(BodyForm::Quoted(list[0].clone()));
                } else if op == b"unquote" {
                    if list.len() != 1 {
                        return Err(CompileErr(l.clone(), format!("bad form {}", body)));
                    }

                    return compile_bodyform(opts.clone(), Rc::new(list[0].clone()));
                }
            }

            qq_to_expression_list(opts, body.clone())
        }
        _ => Ok(BodyForm::Quoted(body_copy.clone())),
    }
}

fn qq_to_expression_list(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<BodyForm, CompileErr> {
    match body.borrow() {
        SExp::Cons(l, f, r) => {
            m! {
                f_qq <- qq_to_expression(opts.clone(), f.clone());
                r_qq <- qq_to_expression_list(opts, r.clone());
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
            format!("Bad list tail in qq {}", body),
        )),
    }
}

fn args_to_expression_list(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<BodyForm>>, CompileErr> {
    if body.nilp() {
        Ok(vec![])
    } else {
        match body.borrow() {
            SExp::Cons(_l, first, rest) => {
                let mut result_list = Vec::new();
                let f_compiled = compile_bodyform(opts.clone(), first.clone())?;
                result_list.push(Rc::new(f_compiled));
                let mut args = args_to_expression_list(opts, rest.clone())?;
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

fn make_let_bindings(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<Binding>>, CompileErr> {
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
                    let compiled_body = compile_bodyform(opts.clone(), Rc::new(expr.clone()))?;
                    let mut result = Vec::new();
                    let mut rest_bindings = make_let_bindings(opts, tl.clone())?;
                    result.push(Rc::new(Binding {
                        loc: l.clone(),
                        nl: l.clone(),
                        name: name.to_vec(),
                        body: Rc::new(compiled_body),
                    }));
                    result.append(&mut rest_bindings);
                    Ok(result)
                }
                _ => err.clone(),
            })
            .unwrap_or_else(|| err.clone()),
        _ => err,
    }
}

pub fn compile_bodyform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<BodyForm, CompileErr> {
    match body.borrow() {
        SExp::Cons(l, op, tail) => {
            let application = || {
                args_to_expression_list(opts.clone(), tail.clone()).and_then(|args| {
                    compile_bodyform(opts.clone(), op.clone()).map(|func| {
                        let mut result_call = vec![Rc::new(func)];
                        let mut args_clone = args.to_vec();
                        let ending = if args.is_empty() {
                            l.ending()
                        } else {
                            args[args.len() - 1].loc().ending()
                        };
                        result_call.append(&mut args_clone);
                        BodyForm::Call(l.ext(&ending), result_call)
                    })
                })
            };

            let finish_err = |site| {
                Err(CompileErr(
                    l.clone(),
                    format!("{}: bad argument list for form {}", site, body),
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

                                let let_bindings =
                                    make_let_bindings(opts.clone(), Rc::new(bindings))?;
                                let compiled_body = compile_bodyform(opts, Rc::new(body))?;
                                Ok(BodyForm::Let(
                                    kind,
                                    LetData {
                                        loc: l.clone(),
                                        kw: Some(l.clone()),
                                        bindings: let_bindings,
                                        body: Rc::new(compiled_body),
                                    },
                                ))
                            } else if *atom_name == "quote".as_bytes().to_vec() {
                                if v.len() != 1 {
                                    return finish_err("quote");
                                }

                                let quote_body = v[0].clone();

                                Ok(BodyForm::Quoted(quote_body))
                            } else if *atom_name == "qq".as_bytes().to_vec() {
                                if v.len() != 1 {
                                    return finish_err("qq");
                                }

                                let quote_body = v[0].clone();

                                qq_to_expression(opts, Rc::new(quote_body))
                            } else if *atom_name == "mod".as_bytes().to_vec() {
                                let subparse = frontend(opts, &[body.clone()])?;
                                Ok(BodyForm::Mod(op.loc(), subparse))
                            } else {
                                application()
                            }
                        }
                        None => finish_err("tail_proper"),
                    }
                }
                SExp::Integer(il, i) => compile_bodyform(
                    opts,
                    Rc::new(SExp::Cons(
                        il.clone(),
                        Rc::new(SExp::Atom(il.clone(), u8_from_number(i.clone()))),
                        tail.clone(),
                    )),
                ),
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

fn compile_defconstant(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    nl: Srcloc,
    kwl: Option<Srcloc>,
    name: Vec<u8>,
    body: Rc<SExp>,
) -> Result<HelperForm, CompileErr> {
    let body_borrowed: &SExp = body.borrow();
    if let SExp::Cons(_, _, _) = body_borrowed {
        Ok(HelperForm::Defconstant(DefconstData {
            loc: l,
            nl,
            kw: kwl,
            name: name.to_vec(),
            body: Rc::new(BodyForm::Value(body_borrowed.clone())),
        }))
    } else {
        compile_bodyform(opts, body).map(|bf| {
            HelperForm::Defconstant(DefconstData {
                loc: l,
                nl,
                kw: kwl,
                name: name.to_vec(),
                body: Rc::new(bf),
            })
        })
    }
}

fn location_span(l_: Srcloc, lst_: Rc<SExp>) -> Srcloc {
    let mut l = l_;
    let mut lst = lst_;
    while let SExp::Cons(_, a, b) = lst.borrow() {
        l = location_span(l.clone(), a.clone()).ext(&b.loc());
        lst = b.clone();
    }
    l
}

pub struct CompileDefun {
    pub l: Srcloc,
    pub nl: Srcloc,
    pub kwl: Option<Srcloc>,
    pub inline: bool,
    pub name: Vec<u8>,
    pub args: Rc<SExp>,
    pub body: Rc<SExp>,
}

fn compile_defun(opts: Rc<dyn CompilerOpts>, data: CompileDefun) -> Result<HelperForm, CompileErr> {
    let mut take_form = data.body.clone();

    if let SExp::Cons(_, f, _r) = data.body.borrow() {
        take_form = f.clone();
    }
    compile_bodyform(opts, take_form).map(|bf| {
        HelperForm::Defun(
            data.inline,
            DefunData {
                loc: data.l,
                nl: data.nl,
                kw: data.kwl,
                name: data.name,
                args: data.args,
                body: Rc::new(bf),
            },
        )
    })
}

fn compile_defmacro(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    nl: Srcloc,
    kwl: Option<Srcloc>,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
) -> Result<HelperForm, CompileErr> {
    let program = SExp::Cons(
        l.clone(),
        Rc::new(SExp::Atom(l.clone(), b"mod".to_vec())),
        Rc::new(SExp::Cons(l.clone(), args.clone(), body)),
    );
    let new_opts = opts.set_stdenv(false);
    frontend(new_opts, &[Rc::new(program)]).map(|p| {
        HelperForm::Defmacro(DefmacData {
            loc: l,
            nl,
            kw: kwl,
            name,
            args: args.clone(),
            program: Rc::new(p),
        })
    })
}

struct OpName4Match {
    opl: Srcloc,
    op_name: Vec<u8>,
    nl: Srcloc,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
}

#[allow(clippy::type_complexity)]
fn match_op_name_4(pl: &[SExp]) -> Option<OpName4Match> {
    if pl.is_empty() {
        return None;
    }

    match &pl[0] {
        SExp::Atom(l, op_name) => {
            if pl.len() < 3 {
                return Some(OpName4Match {
                    opl: l.clone(),
                    op_name: op_name.clone(),
                    nl: l.clone(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                });
            }

            match &pl[1] {
                SExp::Atom(ll, name) => {
                    let mut tail_list = Vec::new();
                    for elt in pl.iter().skip(3) {
                        tail_list.push(Rc::new(elt.clone()));
                    }
                    Some(OpName4Match {
                        opl: l.clone(),
                        op_name: op_name.clone(),
                        nl: ll.clone(),
                        name: name.clone(),
                        args: Rc::new(pl[2].clone()),
                        body: Rc::new(enlist(l.clone(), tail_list)),
                    })
                }
                _ => Some(OpName4Match {
                    opl: l.clone(),
                    op_name: op_name.clone(),
                    nl: pl[1].loc(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                }),
            }
        }
        _ => None,
    }
}

pub fn compile_helperform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Option<HelperForm>, CompileErr> {
    let l = location_span(body.loc(), body.clone());

    if let Some(matched) = body.proper_list().and_then(|pl| match_op_name_4(&pl)) {
        if matched.op_name == b"defconstant" {
            compile_defconstant(
                opts,
                l,
                matched.nl,
                Some(matched.opl),
                matched.name.to_vec(),
                matched.args,
            )
            .map(Some)
        } else if matched.op_name == b"defmacro" {
            compile_defmacro(
                opts,
                l,
                matched.nl,
                Some(matched.opl),
                matched.name.to_vec(),
                matched.args,
                matched.body,
            )
            .map(Some)
        } else if matched.op_name == b"defun" {
            compile_defun(
                opts,
                CompileDefun {
                    l,
                    nl: matched.nl,
                    kwl: Some(matched.opl),
                    inline: false,
                    name: matched.name.to_vec(),
                    args: matched.args,
                    body: matched.body,
                },
            )
            .map(Some)
        } else if matched.op_name == b"defun-inline" {
            compile_defun(
                opts,
                CompileDefun {
                    l,
                    nl: matched.nl,
                    kwl: Some(matched.opl),
                    inline: true,
                    name: matched.name.to_vec(),
                    args: matched.args,
                    body: matched.body,
                },
            )
            .map(Some)
        } else {
            Err(CompileErr(
                matched.body.loc(),
                "unknown keyword in helper".to_string(),
            ))
        }
    } else {
        Err(CompileErr(
            body.loc(),
            "Helper wasn't in the proper form".to_string(),
        ))
    }
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
                    include_forms: mc.includes.clone(),
                    args,
                    helpers: mc.helpers.clone(),
                    exp: Rc::new(compile_bodyform(opts.clone(), body.clone())?),
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
                        None => compile_mod_(&mc.add_helper(form), opts, args, tail.clone()),
                        Some(_) => Err(CompileErr(l.clone(), "too many expressions".to_string())),
                    },
                }
            }
        },
        _ => Err(CompileErr(
            content.loc(),
            format!("inappropriate sexp {}", content),
        )),
    }
}

fn frontend_step_finish(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    pre_forms: &[Rc<SExp>],
) -> Result<ModAccum, CompileErr> {
    let loc = pre_forms[0].loc();
    frontend_start(
        opts.clone(),
        includes,
        &[Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Atom(loc.clone(), "mod".as_bytes().to_vec())),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Nil(loc.clone())),
                Rc::new(list_to_cons(loc, pre_forms)),
            )),
        ))],
    )
}

fn frontend_start(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    pre_forms: &[Rc<SExp>],
) -> Result<ModAccum, CompileErr> {
    if pre_forms.is_empty() {
        Err(CompileErr(
            Srcloc::start(&opts.filename()),
            "empty source file not allowed".to_string(),
        ))
    } else {
        let l = pre_forms[0].loc();
        pre_forms[0]
            .proper_list()
            .map(|x| {
                if x.is_empty() {
                    return frontend_step_finish(opts.clone(), includes, pre_forms);
                }

                if let SExp::Atom(_, mod_atom) = &x[0] {
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

                        let ls = preprocess(opts.clone(), includes, body)?;
                        return compile_mod_(
                            &ModAccum::new(l.clone()),
                            opts.clone(),
                            args,
                            Rc::new(list_to_cons(l, &ls)),
                        );
                    }
                }

                frontend_step_finish(opts.clone(), includes, pre_forms)
            })
            .unwrap_or_else(|| frontend_step_finish(opts, includes, pre_forms))
    }
}

pub fn frontend(
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>],
) -> Result<CompileForm, CompileErr> {
    let mut includes = Vec::new();
    let started = frontend_start(opts.clone(), &mut includes, pre_forms)?;

    for i in includes.iter() {
        started.add_include(i.clone());
    }

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

    for hpair in helper_list {
        helper_map.insert(hpair.0.clone(), hpair.1.clone());
    }

    let helper_names = calculate_live_helpers(&HashSet::new(), &expr_names, &helper_map);

    let mut live_helpers = Vec::new();
    for h in our_mod.helpers {
        if helper_names.contains(h.name()) {
            live_helpers.push(h);
        }
    }

    Ok(CompileForm {
        loc: our_mod.loc.clone(),
        include_forms: includes.to_vec(),
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
                Rc::new(SExp::atom_from_string(l.clone(), "@")),
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
                    Rc::new(SExp::atom_from_string(l.clone(), "q")),
                    args.clone(),
                ))
            } else {
                let new_args = from_clvm_args(args.clone());
                Rc::new(SExp::Cons(l.clone(), op.clone(), new_args))
            }
        }
    }
}
