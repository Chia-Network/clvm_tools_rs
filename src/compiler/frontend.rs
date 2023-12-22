use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use log::debug;
use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::comptypes::{
    list_to_cons, ArgsAndTail, Binding, BindingPattern, BodyForm, ChiaType, CompileErr,
    CompileForm, CompilerOpts, ConstantKind, DefconstData, DefmacData, DeftypeData, DefunData,
    HelperForm, ImportLongName, IncludeDesc, LetData, LetFormInlineHint, LetFormKind, LongNameTranslation, ModAccum, ModuleImportSpec, NamespaceData, NamespaceRefData, StructDef,
    StructMember, SyntheticType, TypeAnnoKind,
};
use crate::compiler::lambda::handle_lambda;
use crate::compiler::preprocessor::{parse_toplevel_mod, preprocess, ToplevelModParseResult};
use crate::compiler::rename::{rename_assign_bindings, rename_children_compileform};
use crate::compiler::sexp::{decode_string, enlist, SExp};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::{parse_type_sexp, parse_type_var};
use crate::compiler::types::ast::{Polytype, Type, TypeVar};
use crate::util::{u8_from_number, Number};

pub fn collect_used_names_sexp(body: Rc<SExp>) -> Vec<Vec<u8>> {
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
        BodyForm::Value(atom) => match atom {
            SExp::Atom(_l, v) => vec![v.to_vec()],
            SExp::Cons(_l, f, r) => {
                let mut first_names = collect_used_names_sexp(f.clone());
                let mut rest_names = collect_used_names_sexp(r.clone());
                first_names.append(&mut rest_names);
                first_names
            }
            _ => Vec::new(),
        },
        BodyForm::Call(_l, vs, tail) => {
            let mut result = Vec::new();
            for a in vs {
                let mut argnames = collect_used_names_bodyform(a);
                result.append(&mut argnames);
            }
            if let Some(t) = tail {
                let mut tail_names = collect_used_names_bodyform(t);
                result.append(&mut tail_names);
            }
            result
        }
        BodyForm::Mod(_, _) => vec![],
        BodyForm::Lambda(ldata) => {
            let mut capture_names = collect_used_names_bodyform(ldata.captures.borrow());
            capture_names.append(&mut collect_used_names_bodyform(ldata.body.borrow()));
            capture_names
        }
    }
}

fn collect_used_names_helperform(body: &HelperForm) -> Vec<Vec<u8>> {
    match body {
        HelperForm::Deftype(_) => Vec::new(),
        HelperForm::Defnamespace(_ns) => Vec::new(),
        HelperForm::Defnsref(_ns) => Vec::new(),
        HelperForm::Defconstant(defc) => collect_used_names_bodyform(defc.body.borrow()),
        HelperForm::Defmacro(mac) => {
            let mut res = collect_used_names_compileform(mac.program.borrow());
            // Ensure any other names mentioned in qq blocks are included.
            let mut all_token_res = collect_used_names_sexp(mac.program.to_sexp());
            res.append(&mut all_token_res);
            res
        }
        HelperForm::Defun(_, defun) => collect_used_names_bodyform(&defun.body),
    }
}

fn collect_used_names_compileform(body: &CompileForm) -> Vec<Vec<u8>> {
    let mut result = Vec::new();
    for h in body.helpers.iter() {
        let mut helper_list = collect_used_names_helperform(h);
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
                        return Err(CompileErr(l.clone(), format!("bad form {body}")));
                    }

                    return Ok(BodyForm::Quoted(list[0].clone()));
                } else if op == b"unquote" {
                    if list.len() != 1 {
                        return Err(CompileErr(l.clone(), format!("bad form {body}")));
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
                ), None))
            }
        }
        SExp::Nil(l) => Ok(BodyForm::Quoted(SExp::Nil(l.clone()))),
        _ => Err(CompileErr(
            body.loc(),
            format!("Bad list tail in qq {body}"),
        )),
    }
}

fn args_to_expression_list(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<ArgsAndTail, CompileErr> {
    if body.nilp() {
        Ok(ArgsAndTail::default())
    } else {
        match body.borrow() {
            SExp::Cons(_l, first, rest) => {
                if let SExp::Atom(_fl, fname) = first.borrow() {
                    if fname == b"&rest" {
                        // Rest is a list containing one item that becomes the
                        // tail.
                        //
                        // Downstream, we'll use the tail instead of a nil as the
                        // final element of a call form.  In the inline case, this
                        // means that argument references will be generated into
                        // the runtime tail expression when appropriate.
                        let args_no_tail = args_to_expression_list(opts, rest.clone())?;

                        if args_no_tail.tail.is_some() {
                            return Err(CompileErr(
                                rest.loc(),
                                "only one use of &rest is allowed".to_string(),
                            ));
                        }

                        if args_no_tail.args.len() != 1 {
                            return Err(CompileErr(
                                body.loc(),
                                "&rest specified with bad tail".to_string(),
                            ));
                        }

                        // Return a tail.
                        return Ok(ArgsAndTail {
                            args: vec![],
                            tail: Some(args_no_tail.args[0].clone()),
                        });
                    }
                }
                let mut result_list = Vec::new();
                let f_compiled = compile_bodyform(opts.clone(), first.clone())?;
                result_list.push(Rc::new(f_compiled));
                let mut args_and_tail = args_to_expression_list(opts, rest.clone())?;
                result_list.append(&mut args_and_tail.args);
                Ok(ArgsAndTail {
                    args: result_list,
                    tail: args_and_tail.tail,
                })
            }
            _ => Err(CompileErr(body.loc(), format!("Bad arg list tail {body}"))),
        }
    }
}

fn make_let_bindings(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<Binding>>, CompileErr> {
    let err = Err(CompileErr(body.loc(), format!("Bad binding tail {body:?}")));
    match body.borrow() {
        SExp::Nil(_) => Ok(vec![]),
        SExp::Cons(_, head, tl) => head
            .proper_list()
            .filter(|x| x.len() == 2)
            .map(|x| match (x[0].clone(), &x[1]) {
                (SExp::Atom(l, name), expr) => {
                    let compiled_body = compile_bodyform(opts.clone(), Rc::new(expr.clone()))?;
                    let mut result = Vec::new();
                    let mut rest_bindings = make_let_bindings(opts, tl.clone())?;
                    result.push(Rc::new(Binding {
                        loc: l.clone(),
                        nl: l,
                        pattern: BindingPattern::Name(name.to_vec()),
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

// Make a set of names in this sexp.
pub fn make_provides_set(provides_set: &mut HashSet<Vec<u8>>, body_sexp: Rc<SExp>) {
    match body_sexp.atomize() {
        SExp::Cons(_, a, b) => {
            make_provides_set(provides_set, a);
            make_provides_set(provides_set, b);
        }
        SExp::Atom(_, name) => {
            provides_set.insert(name);
        }
        _ => {}
    }
}

fn at_or_above_23(opts: Rc<dyn CompilerOpts>) -> bool {
    opts.dialect().stepping.unwrap_or(0) > 22
}

fn handle_assign_form(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    v: &[SExp],
    inline_hint: Option<LetFormInlineHint>,
) -> Result<BodyForm, CompileErr> {
    if v.len() % 2 == 0 {
        return Err(CompileErr(
            l,
            "assign form should be in pairs of pattern value followed by an expression".to_string(),
        ));
    }

    let mut bindings = Vec::new();
    let mut check_duplicates = HashSet::new();

    for idx in (0..(v.len() - 1) / 2).map(|idx| idx * 2) {
        let destructure_pattern = Rc::new(v[idx].clone());
        let binding_body = compile_bodyform(opts.clone(), Rc::new(v[idx + 1].clone()))?;
        // Ensure bindings aren't duplicated as we won't be able to
        // guarantee their order during toposort.
        let mut this_provides = HashSet::new();
        make_provides_set(&mut this_provides, destructure_pattern.clone());

        for item in this_provides.iter() {
            if check_duplicates.contains(item) {
                return Err(CompileErr(
                    destructure_pattern.loc(),
                    format!("Duplicate binding {}", decode_string(item)),
                ));
            }
            check_duplicates.insert(item.clone());
        }

        bindings.push(Rc::new(Binding {
            loc: v[idx].loc().ext(&v[idx + 1].loc()),
            nl: destructure_pattern.loc(),
            pattern: BindingPattern::Complex(destructure_pattern),
            body: Rc::new(binding_body),
        }));
    }

    let mut compiled_body = compile_bodyform(opts.clone(), Rc::new(v[v.len() - 1].clone()))?;
    // We don't need to do much if there were no bindings.
    if bindings.is_empty() {
        return Ok(compiled_body);
    }

    if at_or_above_23(opts) {
        let (new_compiled_body, new_bindings) =
            rename_assign_bindings(&l, &bindings, Rc::new(compiled_body))?;
        compiled_body = new_compiled_body;
        bindings = new_bindings;
    };

    // Return a precise representation of this assign while storing up the work
    // we did breaking it down.
    Ok(BodyForm::Let(
        LetFormKind::Assign,
        Box::new(LetData {
            loc: l.clone(),
            kw: Some(l),
            bindings,
            inline_hint,
            body: Rc::new(compiled_body),
        }),
    ))
}

pub fn compile_bodyform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<BodyForm, CompileErr> {
    match body.borrow() {
        SExp::Cons(l, op, tail) => {
            let application = || {
                args_to_expression_list(opts.clone(), tail.clone()).and_then(|atail| {
                    compile_bodyform(opts.clone(), op.clone()).map(|func| {
                        let mut result_call = vec![Rc::new(func)];
                        let mut args_clone = atail.args.to_vec();
                        // Ensure that the full extent of the call expression
                        // in the source file becomes the Srcloc given to the
                        // call itself.
                        let ending = if atail.args.is_empty() {
                            l.ending()
                        } else {
                            atail.args[atail.args.len() - 1].loc().ending()
                        };
                        result_call.append(&mut args_clone);
                        BodyForm::Call(l.ext(&ending), result_call, atail.tail)
                    })
                })
            };

            let finish_err = |site| {
                Err(CompileErr(
                    l.clone(),
                    format!("{site}: bad argument list for form {body}"),
                ))
            };

            match op.borrow() {
                SExp::Atom(l, atom_name) => {
                    if *atom_name == b"q" || (atom_name.len() == 1 && atom_name[0] == 1) {
                        let tail_copy: &SExp = tail.borrow();
                        return Ok(BodyForm::Quoted(tail_copy.clone()));
                    }

                    let assign_lambda = *atom_name == "assign-lambda".as_bytes().to_vec();
                    let assign_inline = *atom_name == "assign-inline".as_bytes().to_vec();

                    match tail.proper_list() {
                        Some(v) => {
                            if *atom_name == b"let" || *atom_name == b"let*" {
                                if v.len() != 2 {
                                    return finish_err("let");
                                }

                                let kind = if *atom_name == b"let" {
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
                                    Box::new(LetData {
                                        loc: l.clone(),
                                        kw: Some(l.clone()),
                                        bindings: let_bindings,
                                        inline_hint: None,
                                        body: Rc::new(compiled_body),
                                    }),
                                ))
                            } else if assign_lambda
                                || assign_inline
                                || *atom_name == "assign".as_bytes().to_vec()
                            {
                                handle_assign_form(
                                    opts.clone(),
                                    l.clone(),
                                    &v,
                                    if assign_lambda {
                                        Some(LetFormInlineHint::NonInline(l.clone()))
                                    } else if assign_inline {
                                        Some(LetFormInlineHint::Inline(l.clone()))
                                    } else {
                                        Some(LetFormInlineHint::NoChoice)
                                    },
                                )
                            } else if *atom_name == b"quote" {
                                if v.len() != 1 {
                                    return finish_err("quote");
                                }

                                let quote_body = v[0].clone();

                                Ok(BodyForm::Quoted(quote_body))
                            } else if *atom_name == b"qq" {
                                if v.len() != 1 {
                                    return finish_err("qq");
                                }

                                let quote_body = v[0].clone();

                                qq_to_expression(opts, Rc::new(quote_body))
                            } else if *atom_name == b"mod" {
                                let subparse = frontend(opts, &[body.clone()])?;
                                Ok(BodyForm::Mod(op.loc(), subparse))
                            } else if *atom_name == b"lambda" {
                                handle_lambda(opts, Some(l.clone()), &v)
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

// More modern constant definition that interprets code ala constexpr.
fn compile_defconst(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    nl: Srcloc,
    kl: Option<Srcloc>,
    name: Vec<u8>,
    body: Rc<SExp>,
) -> Result<HelperForm, CompileErr> {
    let bf = compile_bodyform(opts.clone(), body)?;
    Ok(HelperForm::Defconstant(DefconstData {
        kw: kl,
        nl,
        loc: l,
        kind: ConstantKind::Complex,
        name: name.to_vec(),
        body: Rc::new(bf),
        tabled: opts.frontend_opt() || opts.dialect().stepping.unwrap_or(0) > 22,
        ty: None,
    }))
}

fn compile_defconstant(
    opts: Rc<dyn CompilerOpts>,
    l: Srcloc,
    nl: Srcloc,
    kl: Option<Srcloc>,
    name: Vec<u8>,
    body: Rc<SExp>,
    ty: Option<Polytype>,
) -> Result<HelperForm, CompileErr> {
    let body_borrowed: &SExp = body.borrow();
    if let SExp::Cons(_, _, _) = body_borrowed {
        Ok(HelperForm::Defconstant(DefconstData {
            loc: l,
            nl,
            kw: kl,
            kind: ConstantKind::Simple,
            name: name.to_vec(),
            body: Rc::new(BodyForm::Value(body_borrowed.clone())),
            tabled: false,
            ty,
        }))
    } else {
        compile_bodyform(opts, body).map(|bf| {
            HelperForm::Defconstant(DefconstData {
                loc: l,
                nl,
                kw: kl,
                kind: ConstantKind::Simple,
                name: name.to_vec(),
                body: Rc::new(bf),
                tabled: false,
                ty,
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

fn compile_defun(
    opts: Rc<dyn CompilerOpts>,
    data: CompileDefun,
    ty: Option<Polytype>,
) -> Result<HelperForm, CompileErr> {
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
                args: data.args.clone(),
                orig_args: data.args,
                body: Rc::new(bf),
                synthetic: None,
                ty,
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
            advanced: false,
        })
    })
}

enum TypeKind {
    Arrow,
    Colon,
}

struct OpName4Match {
    opl: Srcloc,
    op_name: Vec<u8>,
    nl: Srcloc,
    name: Vec<u8>,
    args: Rc<SExp>,
    body: Rc<SExp>,
    orig: Vec<SExp>,
    ty: Option<(TypeKind, Rc<SExp>)>,
}

fn match_op_name_4(pl: &[SExp]) -> Option<OpName4Match> {
    if pl.is_empty() {
        return None;
    }

    match &pl[0].atomize() {
        SExp::Atom(l, op_name) => {
            if pl.len() < 3 {
                return Some(OpName4Match {
                    opl: l.clone(),
                    op_name: op_name.clone(),
                    nl: l.clone(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                    orig: pl.to_owned(),
                    ty: None,
                });
            }

            match &pl[1].atomize() {
                SExp::Atom(ll, name) => {
                    let mut tail_idx = 3;
                    let mut tail_list = Vec::new();
                    let mut type_anno = None;
                    if pl.len() > 3 {
                        if let SExp::Atom(_, colon) = &pl[3] {
                            if *colon == vec![b':'] {
                                // Type annotation
                                tail_idx += 2;
                                type_anno = Some((TypeKind::Colon, Rc::new(pl[4].clone())));
                            } else if *colon == vec![b'-', b'>'] {
                                // Type annotation
                                tail_idx += 2;
                                type_anno = Some((TypeKind::Arrow, Rc::new(pl[4].clone())));
                            }
                        }
                    }
                    for elt in pl.iter().skip(tail_idx) {
                        tail_list.push(Rc::new(elt.clone()));
                    }

                    Some(OpName4Match {
                        nl: ll.clone(),
                        op_name: op_name.clone(),
                        opl: l.clone(),
                        name: name.clone(),
                        args: Rc::new(pl[2].clone()),
                        body: Rc::new(enlist(l.clone(), &tail_list)),
                        orig: pl.to_owned(),
                        ty: type_anno,
                    })
                }
                _ => Some(OpName4Match {
                    nl: pl[0].loc(),
                    opl: l.clone(),
                    op_name: op_name.clone(),
                    name: Vec::new(),
                    args: Rc::new(SExp::Nil(l.clone())),
                    body: Rc::new(SExp::Nil(l.clone())),
                    orig: pl.to_owned(),
                    ty: None,
                }),
            }
        }
        _ => None,
    }
}

fn extract_type_variables_from_forall_stack(tvars: &mut Vec<TypeVar>, t: &Polytype) -> Polytype {
    if let Type::TForall(v, t1) = t {
        tvars.push(v.clone());
        extract_type_variables_from_forall_stack(tvars, t1.borrow())
    } else {
        t.clone()
    }
}

pub struct ArgTypeResult {
    pub stripped_args: Rc<SExp>,
    pub arg_names: Vec<Vec<u8>>,
    pub individual_types: HashMap<Vec<u8>, Polytype>,
    pub individual_paths: HashMap<Vec<u8>, Number>,
    pub individual_locs: HashMap<Vec<u8>, Srcloc>,
    pub whole_args: Polytype,
}

#[allow(clippy::too_many_arguments)]
fn recover_arg_type_inner(
    arg_names: &mut Vec<Vec<u8>>,
    individual_types: &mut HashMap<Vec<u8>, Polytype>,
    individual_paths: &mut HashMap<Vec<u8>, Number>,
    individual_locs: &mut HashMap<Vec<u8>, Srcloc>,
    depth: Number,
    path: Number,
    args: Rc<SExp>,
    have_anno: bool,
) -> Result<(bool, Rc<SExp>, Polytype), CompileErr> {
    match &args.atomize() {
        SExp::Nil(l) => Ok((have_anno, args.clone(), Type::TUnit(l.clone()))),
        SExp::Atom(l, n) => {
            arg_names.push(n.clone());
            individual_types.insert(n.clone(), Type::TAny(l.clone()));
            individual_paths.insert(n.clone(), depth + path);
            individual_locs.insert(n.clone(), l.clone());
            Ok((false, args.clone(), Type::TAny(l.clone())))
        }
        SExp::Cons(l, a, b) => {
            // There are a few cases:
            // (normal destructuring)
            // (@ name sub)
            // (@ name sub : ty)
            // (X : ty)
            // We want to catch the final case and pass through its unannotated
            // counterpart.
            let next_depth = depth.clone() * 2_u32.to_bigint().unwrap();
            if let Some(lst) = args.proper_list() {
                // Dive in
                if lst.len() == 5 {
                    if let (SExp::Atom(l, n), SExp::Atom(_l2, n2)) =
                        (&lst[0].atomize(), &lst[3].atomize())
                    {
                        if n == &vec![b'@'] && n2 == &vec![b':'] {
                            // At capture with annotation
                            return Err(CompileErr(l.clone(), "An at-capture with a type alias is currently unsupported.  A struct can be used instead.".to_string()));
                        };
                    };
                } else if lst.len() == 3 {
                    if let (SExp::Atom(l0, n0), SExp::Atom(_l1, n1)) =
                        (&lst[0].atomize(), &lst[1].atomize())
                    {
                        if n1 == &vec![b':'] {
                            // Name with annotation
                            let ty = parse_type_sexp(Rc::new(lst[2].clone()))?;
                            arg_names.push(n0.clone());
                            individual_types.insert(n0.clone(), ty.clone());
                            individual_paths.insert(n0.clone(), depth + path);
                            individual_locs.insert(n0.clone(), l0.clone());
                            return Ok((true, Rc::new(lst[0].clone()), ty));
                        };
                    };
                }
            }

            let (got_ty_a, stripped_a, ty_a) = recover_arg_type_inner(
                arg_names,
                individual_types,
                individual_paths,
                individual_locs,
                next_depth.clone(),
                path.clone(),
                a.clone(),
                have_anno,
            )?;
            let (got_ty_b, stripped_b, ty_b) = recover_arg_type_inner(
                arg_names,
                individual_types,
                individual_paths,
                individual_locs,
                next_depth,
                path + depth,
                b.clone(),
                have_anno,
            )?;
            Ok((
                got_ty_a || got_ty_b,
                Rc::new(SExp::Cons(l.clone(), stripped_a, stripped_b)),
                Type::TPair(Rc::new(ty_a), Rc::new(ty_b)),
            ))
        }
        _ => Err(CompileErr(
            args.loc(),
            "unrecognized argument form".to_string(),
        )),
    }
}

pub fn recover_arg_type(args: Rc<SExp>, always: bool) -> Result<Option<ArgTypeResult>, CompileErr> {
    let mut arg_names = Vec::new();
    let mut individual_types = HashMap::new();
    let mut individual_paths = HashMap::new();
    let mut individual_locs = HashMap::new();
    let (got_any, stripped, ty) = recover_arg_type_inner(
        &mut arg_names,
        &mut individual_types,
        &mut individual_paths,
        &mut individual_locs,
        bi_one(),
        bi_zero(),
        args,
        false,
    )?;
    if got_any || always {
        Ok(Some(ArgTypeResult {
            arg_names,
            stripped_args: stripped,
            individual_types,
            individual_paths,
            individual_locs,
            whole_args: ty,
        }))
    } else {
        Ok(None)
    }
}

// Given type recovered argument type and a candidate return type (possibly with
// a forall stack), construct the user's expected function type. If no arg types
// were given, the arg type is Any. If the bottom of the stack is a function
// type, its left hand type is replaced with the given arg type or Any. If it
// isn't a function type, it's promoted to be a function taking the given arg
// type or Any.
fn promote_with_arg_type(argty: &Polytype, funty: &Polytype) -> Polytype {
    match funty {
        Type::TForall(v, t) => {
            Type::TForall(v.clone(), Rc::new(promote_with_arg_type(argty, t.borrow())))
        }
        Type::TFun(_t1, t2) => Type::TFun(Rc::new(argty.clone()), t2.clone()),
        _ => Type::TFun(Rc::new(argty.clone()), Rc::new(funty.clone())),
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
pub fn augment_fun_type_with_args(
    args: Rc<SExp>,
    result_ty: Option<TypeAnnoKind>,
) -> Result<(Rc<SExp>, Option<Polytype>), CompileErr> {
    if let Some(atr) = recover_arg_type(args.clone(), false)? {
        let mut tvars = Vec::new();

        let actual_result_ty = if let Some(TypeAnnoKind::Arrow(rty)) = result_ty {
            extract_type_variables_from_forall_stack(&mut tvars, &rty)
        } else if let Some(TypeAnnoKind::Colon(rty)) = result_ty {
            let want_rty = extract_type_variables_from_forall_stack(&mut tvars, &rty);
            // If it's a function type, we have to give it as "args"
            if let Type::TFun(t1, t2) = want_rty {
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

        Ok((
            atr.stripped_args.clone(),
            Some(promote_with_arg_type(&atr.whole_args, &actual_result_ty)),
        ))
    } else {
        // No arg types were given.  If a type was given for the result (non-fun)
        // use Any -> Any
        // else use the whole thing.
        Ok(result_ty
            .map(|rty| match rty {
                TypeAnnoKind::Colon(t) => (args.clone(), Some(t)),
                TypeAnnoKind::Arrow(t) => (
                    args.clone(),
                    Some(Type::TFun(Rc::new(Type::TAny(args.loc())), Rc::new(t))),
                ),
            })
            .unwrap_or_else(|| (args.clone(), None)))
    }
}

fn create_constructor_code(
    sdef: &StructDef,
    proto: Rc<SExp>
) -> BodyForm {
    match proto.atomize() {
        SExp::Atom(l, n) => BodyForm::Value(SExp::Atom(l, n)),
        SExp::Cons(l, a, b) => BodyForm::Call(
            l.clone(),
            vec![
                Rc::new(BodyForm::Value(SExp::Atom(l, b"c*".to_vec()))),
                Rc::new(create_constructor_code(sdef, a)),
                Rc::new(create_constructor_code(sdef, b)),
            ],
            None,
        ),
        _ => BodyForm::Quoted(SExp::Nil(sdef.loc.clone())),
    }
}

fn create_constructor(sdef: &StructDef) -> HelperForm {
    let mut access_name = "new_".as_bytes().to_vec();
    access_name.append(&mut sdef.name.clone());

    // Iterate through the arguments in reverse to build up a linear argument
    // list.
    // Build up the type list in the same way.
    let mut arguments = Rc::new(SExp::Nil(sdef.loc.clone()));
    let mut argtype = Type::TUnit(sdef.loc.clone());

    for m in sdef.members.iter().rev() {
        argtype = Type::TPair(Rc::new(m.ty.clone()), Rc::new(argtype));
        arguments = Rc::new(SExp::Cons(
            m.loc.clone(),
            Rc::new(SExp::Atom(m.loc.clone(), m.name.clone())),
            arguments,
        ));
    }

    let construction = create_constructor_code(sdef, sdef.proto.clone());
    let mut target_ty = Type::TVar(TypeVar(decode_string(&sdef.name), sdef.loc.clone()));

    for a in sdef.vars.iter().rev() {
        target_ty = Type::TApp(Rc::new(target_ty), Rc::new(Type::TVar(a.clone())));
    }

    let mut funty = Type::TFun(Rc::new(argtype), Rc::new(target_ty));

    for a in sdef.vars.iter().rev() {
        funty = Type::TForall(a.clone(), Rc::new(funty));
    }

    HelperForm::Defun(
        true,
        DefunData {
            kw: None,
            nl: sdef.loc.clone(),
            loc: sdef.loc.clone(),
            name: access_name,
            orig_args: arguments.clone(),
            args: arguments,
            body: Rc::new(construction),
            synthetic: Some(SyntheticType::NoInlinePreference),
            ty: Some(funty),
        },
    )
}

pub fn generate_type_helpers(ty: &ChiaType) -> Vec<HelperForm> {
    match ty {
        ChiaType::Abstract(_, _) => vec![],
        ChiaType::Struct(sdef) => {
            // Construct ((S : <type>))
            let struct_argument = Rc::new(SExp::Cons(
                sdef.loc.clone(),
                Rc::new(SExp::Atom(sdef.loc.clone(), vec![b'S'])),
                Rc::new(SExp::Nil(sdef.loc.clone())),
            ));
            let mut members: Vec<HelperForm> = sdef
                .members
                .iter()
                .map(|m| {
                    let mut access_name = "get_".as_bytes().to_vec();
                    access_name.append(&mut sdef.name.clone());
                    access_name.push(b'_');
                    access_name.append(&mut m.name.clone());

                    let mut argty = Type::TVar(TypeVar(decode_string(&sdef.name), m.loc.clone()));

                    for a in sdef.vars.iter().rev() {
                        argty = Type::TApp(Rc::new(argty), Rc::new(Type::TVar(a.clone())));
                    }

                    let mut funty = Type::TFun(
                        Rc::new(Type::TPair(
                            Rc::new(argty),
                            Rc::new(Type::TUnit(m.loc.clone())),
                        )),
                        Rc::new(m.ty.clone()),
                    );

                    for a in sdef.vars.iter().rev() {
                        funty = Type::TForall(a.clone(), Rc::new(funty));
                    }

                    HelperForm::Defun(
                        true,
                        DefunData {
                            kw: None,
                            nl: m.loc.clone(),
                            loc: m.loc.clone(),
                            name: access_name,
                            orig_args: struct_argument.clone(),
                            args: struct_argument.clone(),
                            body: Rc::new(BodyForm::Call(
                                m.loc.clone(),
                                vec![
                                    Rc::new(BodyForm::Value(SExp::Atom(
                                        m.loc.clone(),
                                        vec![b'a', b'*'],
                                    ))),
                                    Rc::new(BodyForm::Quoted(SExp::Integer(
                                        m.loc.clone(),
                                        m.path.clone(),
                                    ))),
                                    Rc::new(BodyForm::Value(SExp::Atom(m.loc.clone(), vec![b'S']))),
                                ],
                                None,
                            )),
                            synthetic: Some(SyntheticType::NoInlinePreference),
                            ty: Some(funty),
                        },
                    )
                })
                .collect();

            let ctor = create_constructor(sdef);
            members.push(ctor);
            members
        }
    }
}

fn parse_chia_type(v: Vec<SExp>) -> Result<ChiaType, CompileErr> {
    // (deftype name args... (def))
    if let SExp::Atom(l, n) = &v[1].atomize() {
        // Name
        if v.len() == 2 {
            // An abstract type
            return Ok(ChiaType::Abstract(v[1].loc(), n.clone()));
        }

        let vars: Vec<SExp> = v.iter().skip(2).take(v.len() - 3).cloned().collect();
        let expr = Rc::new(v[v.len() - 1].clone());

        let mut var_vec = Vec::new();
        for var in vars.iter() {
            var_vec.push(parse_type_var(Rc::new(var.clone()))?);
        }

        let type_of_body = recover_arg_type(expr, true)?.unwrap();
        let mut member_vec = Vec::new();
        for k in type_of_body.arg_names.iter() {
            let arg_path = type_of_body
                .individual_paths
                .get(k)
                .cloned()
                .unwrap_or_else(bi_one);
            let arg_loc = type_of_body
                .individual_locs
                .get(k)
                .cloned()
                .unwrap_or_else(|| l.clone());
            let arg_type = type_of_body
                .individual_types
                .get(k)
                .cloned()
                .unwrap_or_else(|| Type::TAny(arg_loc.clone()));
            member_vec.push(StructMember {
                loc: arg_loc,
                name: k.clone(),
                path: arg_path,
                ty: arg_type,
            });
        }
        return Ok(ChiaType::Struct(StructDef {
            loc: l.clone(),
            name: n.clone(),
            vars: var_vec,
            members: member_vec,
            proto: type_of_body.stripped_args,
            ty: type_of_body.whole_args,
        }));
    }

    Err(CompileErr(
        v[0].loc(),
        "Don't know how to interpret as type definition".to_string(),
    ))
}

#[derive(Debug, Clone)]
pub struct HelperFormResult {
    pub chia_type: Option<ChiaType>,
    pub new_helpers: Vec<HelperForm>,
}

impl HelperFormResult {
    pub fn new(helpers: &[HelperForm], ty: Option<ChiaType>) -> Self {
        HelperFormResult {
            chia_type: ty,
            new_helpers: helpers.iter().cloned().collect()
        }
    }
}

pub fn compile_namespace(
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
    internal: &[SExp]
) -> Result<HelperForm, CompileErr> {
    if internal.len() < 2 {
        return Err(CompileErr(loc, "Namespace must have a name".to_string()));
    }

    let (_, parsed) =
        if let SExp::Atom(_, name) = &internal[1] {
            ImportLongName::parse(&name)
        } else {
            return Err(CompileErr(internal[1].loc(), "Namespace name must be an atom".to_string()));
        };

    let mut helpers = Vec::new();
    for sexp in internal.iter().skip(2) {
        if let Some(hresult) = compile_helperform(opts.clone(), Rc::new(sexp.clone()))? {
            for h in hresult.new_helpers.iter() {
                helpers.push(h.clone());
            }
        } else {
            return Err(CompileErr(sexp.loc(), "Namespaces must contain only definitions".to_string()));
        }
    }

    Ok(HelperForm::Defnamespace(NamespaceData {
        loc: loc.clone(),
        kw: internal[0].loc(),
        nl: internal[1].loc(),
        rendered_name: parsed.as_u8_vec(LongNameTranslation::Namespace),
        longname: parsed,
        helpers,
    }))
}

pub fn compile_nsref(
    loc: Srcloc,
    internal: &[SExp]
) -> Result<HelperForm, CompileErr> {
    if internal.len() < 2 {
        return Err(CompileErr(loc.clone(), "import must import a module".to_string()));
    }

    let import_spec = ModuleImportSpec::parse(loc.clone(), internal[0].loc(), internal, 1)?;
    if let ModuleImportSpec::Qualified(q) = &import_spec {
        return Ok(HelperForm::Defnsref(NamespaceRefData {
            loc,
            kw: internal[0].loc(),
            nl: q.nl.clone(),
            rendered_name: q.name.as_u8_vec(LongNameTranslation::Namespace),
            longname: q.name.clone(),
            specification: import_spec.clone()
        }));
    }

    let (_, parsed) =
        if let SExp::Atom(_nl, name) = &internal[1] {
            ImportLongName::parse(&name)
        } else {
            return Err(CompileErr(internal[1].loc(), "Import name must be an atom".to_string()));
        };

    Ok(HelperForm::Defnsref(NamespaceRefData {
        loc,
        kw: internal[0].loc(),
        nl: import_spec.name_loc(),
        rendered_name: parsed.as_u8_vec(LongNameTranslation::Namespace),
        longname: parsed,
        specification: import_spec
    }))
}

pub fn compile_helperform(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Option<HelperFormResult>, CompileErr> {
    let l = location_span(body.loc(), body.clone());
    let plist = body.proper_list();

    if let Some(matched) = plist.and_then(|pl| match_op_name_4(&pl)) {
        let inline = matched.op_name == "defun-inline".as_bytes().to_vec();
        let is_defmac = matched.op_name == "defmac".as_bytes().to_vec();
        if matched.op_name == "defconstant".as_bytes().to_vec() {
            let definition = compile_defconstant(
                opts,
                l,
                matched.nl,
                Some(matched.opl),
                matched.name.to_vec(),
                matched.args,
                None,
            )?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![definition],
            }))
        } else if matched.op_name == b"defconst" {
            let definition = compile_defconst(
                opts,
                l,
                matched.nl,
                Some(matched.opl),
                matched.name.to_vec(),
                matched.args,
            )?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![definition],
            }))
        } else if matched.op_name == b"defmacro" || is_defmac {
            if is_defmac {
                return Ok(Some(HelperFormResult {
                    chia_type: None,
                    new_helpers: vec![],
                }));
            }

            let definition = compile_defmacro(
                opts,
                l,
                matched.nl,
                Some(matched.opl),
                matched.name.to_vec(),
                matched.args,
                matched.body,
            )?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![definition],
            }))
        } else if matched.op_name == "defun".as_bytes().to_vec() || inline {
            let use_type_anno = if let Some((k, ty)) = matched.ty {
                match k {
                    TypeKind::Arrow => Some(TypeAnnoKind::Arrow(parse_type_sexp(ty)?)),
                    TypeKind::Colon => Some(TypeAnnoKind::Colon(parse_type_sexp(ty)?)),
                }
            } else {
                None
            };

            let (stripped_args, parsed_type) =
                augment_fun_type_with_args(matched.args.clone(), use_type_anno)?;

            let definition = compile_defun(
                opts,
                CompileDefun {
                    l,
                    nl: matched.nl,
                    kwl: Some(matched.opl),
                    inline,
                    name: matched.name.to_vec(),
                    args: stripped_args,
                    body: matched.body,
                },
                parsed_type,
            )?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![definition],
            }))
        } else if matched.op_name == "deftype".as_bytes().to_vec() {
            let parsed_chia = parse_chia_type(matched.orig)?;
            let mut helpers = generate_type_helpers(&parsed_chia);
            debug!("parsed_chia {:?}", parsed_chia);
            let new_form = match &parsed_chia {
                ChiaType::Abstract(l, n) => HelperForm::Deftype(DeftypeData {
                    kw: matched.opl,
                    nl: matched.nl,
                    loc: l.clone(),
                    name: n.clone(),
                    args: vec![],
                    parsed: parsed_chia.clone(),
                    ty: None,
                }),
                ChiaType::Struct(sdef) => {
                    if let SExp::Atom(_, _) = sdef.proto.borrow() {
                        return Err(CompileErr(sdef.loc.clone(), "A struct with a single element acting as an alias is currently a hazard.  This will be fixed in the future.".to_string()));
                    }
                    HelperForm::Deftype(DeftypeData {
                        kw: matched.opl,
                        nl: matched.nl,
                        loc: sdef.loc.clone(),
                        name: sdef.name.clone(),
                        args: sdef.vars.clone(),
                        parsed: parsed_chia.clone(),
                        ty: Some(sdef.ty.clone()),
                    })
                }
            };
            helpers.insert(0, new_form);
            Ok(Some(HelperFormResult {
                chia_type: Some(parsed_chia),
                new_helpers: helpers,
            }))
        } else if matched.op_name == "namespace".as_bytes().to_vec() {
            let ns = compile_namespace(opts, body.loc(), &matched.orig)?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![ns],
            }))
        } else if matched.op_name == "import".as_bytes().to_vec() {
            let nsref = compile_nsref(body.loc(), &matched.orig)?;
            Ok(Some(HelperFormResult {
                chia_type: None,
                new_helpers: vec![nsref],
            }))
        } else {
            Err(CompileErr(
                matched.body.loc(),
                format!("unknown keyword in helper {body}")
            ))
        }
    } else {
        Ok(None)
    }
}

trait ModCompileForms {
    fn compile_mod_body(
        &self,
        opts: Rc<dyn CompilerOpts>,
        include_forms: Vec<IncludeDesc>,
        args: Rc<SExp>,
        body: Rc<SExp>,
        ty: Option<Polytype>,
    ) -> Result<ModAccum, CompileErr>;

    fn compile_mod_helper(
        &self,
        opts: Rc<dyn CompilerOpts>,
        args: Rc<SExp>,
        body: Rc<SExp>,
        ty: Option<Polytype>,
    ) -> Result<ModAccum, CompileErr>;
}

impl ModCompileForms for ModAccum {
    fn compile_mod_body(
        &self,
        opts: Rc<dyn CompilerOpts>,
        include_forms: Vec<IncludeDesc>,
        args: Rc<SExp>,
        body: Rc<SExp>,
        ty: Option<Polytype>,
    ) -> Result<ModAccum, CompileErr> {
        Ok(self.set_final(&CompileForm {
            loc: self.loc.clone(),
            args,
            include_forms,
            helpers: self.helpers.clone(),
            exp: Rc::new(compile_bodyform(opts, body)?),
            ty,
        }))
    }

    fn compile_mod_helper(
        &self,
        opts: Rc<dyn CompilerOpts>,
        _args: Rc<SExp>,
        body: Rc<SExp>,
        _ty: Option<Polytype>,
    ) -> Result<ModAccum, CompileErr> {
        let mut mc = self.clone();
        if let Some(helpers) = compile_helperform(opts.clone(), body.clone())? {
            for form in helpers.new_helpers.iter() {
                debug!("process helper {}", decode_string(form.name()));
                mc = mc.add_helper(form.clone());
            }
            Ok(mc)
        } else {
            Err(CompileErr(
                body.loc(),
                "only the last form can be an exprssion in mod".to_string(),
            ))
        }
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
    match parse_toplevel_mod(opts.clone(), includes, pre_forms)? {
        ToplevelModParseResult::Mod(tm) => {
            let ls = preprocess(opts.clone(), includes, &tm.forms)?;
            let l = ls[0].loc();

            let mut ma = ModAccum::new(l.clone(), false);
            for form in ls.iter().take(ls.len() - 1) {
                ma = ma.compile_mod_helper(
                    opts.clone(),
                    tm.stripped_args.clone(),
                    form.clone(),
                    tm.parsed_type.clone(),
                )?;
            }

            ma.compile_mod_body(
                opts.clone(),
                includes.clone(),
                tm.stripped_args,
                ls[ls.len() - 1].clone(),
                tm.parsed_type,
            )
        }
        ToplevelModParseResult::Simple(t) => {
            frontend_step_finish(opts.clone(), includes, &t)
        }
    }
}

/// Given the available helper list and the main expression, compute the list of
/// reachable helpers.
pub fn compute_live_helpers(
    opts: Rc<dyn CompilerOpts>,
    helper_list: &[HelperForm],
    main_exp: Rc<BodyForm>,
) -> Vec<HelperForm> {
    let expr_names: HashSet<Vec<u8>> = collect_used_names_bodyform(main_exp.borrow())
        .iter()
        .map(|x| x.to_vec())
        .collect();

    let mut helper_map = HashMap::new();

    for h in helper_list.iter() {
        helper_map.insert(h.name().clone(), h.clone());
    }

    let helper_names = calculate_live_helpers(&HashSet::new(), &expr_names, &helper_map);

    helper_list
        .iter()
        .filter(|h| {
            matches!(h, HelperForm::Deftype(_))
                || !opts.frontend_check_live()
                || helper_names.contains(h.name())
        })
        .cloned()
        .collect()
}

/// Entrypoint for compilation.  This yields a CompileForm which represents a full
/// program.
///
/// Given a CompilerOpts specifying the global options for the compilation, return
/// a representation of the parsed program.  Desugaring is not done in this step
/// so this is a close representation of the user's input, containing location
/// references etc.
///
/// pre_forms is a list of forms, because most SExp readers, including parse_sexp
/// parse a list of complete forms from a source text.  It is possible for frontend
/// to use a list of forms, but it is most often used with a single list in
/// chialisp.  Usually pre_forms will contain a slice containing one list or
/// mod form.
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
            let compiled_val: &CompileForm = &v;
            Ok(compiled_val.clone())
        }
    };

    let our_mod = rename_children_compileform(&compiled?)?;

    let live_helpers = compute_live_helpers(opts.clone(), &our_mod.helpers, our_mod.exp.clone());

    Ok(CompileForm {
        include_forms: includes.to_vec(),
        helpers: live_helpers,
        ..our_mod
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
