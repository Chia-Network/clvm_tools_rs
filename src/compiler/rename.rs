use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::codegen::toposort_assign_bindings;
use crate::compiler::comptypes::{
    Binding, BindingPattern, BodyForm, CompileErr, CompileForm, DefconstData, DefmacData,
    DefunData, HelperForm, LambdaData, LetData, LetFormKind,
};
use crate::compiler::gensym::gensym;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

/// Rename in a qq form.  This searches for (unquote ...) forms inside and performs
/// rename inside them, leaving the rest of the qq form as is.
fn rename_in_qq(namemap: &HashMap<Vec<u8>, Vec<u8>>, body: Rc<SExp>) -> Rc<SExp> {
    body.proper_list()
        .and_then(|x| {
            if let [SExp::Atom(_, q), body] = &x[..] {
                if q == b"unquote" {
                    return Some(rename_in_cons(namemap, Rc::new(body.clone()), true));
                }
            }

            None
        })
        .unwrap_or_else(|| match body.borrow() {
            SExp::Cons(l, x, y) => {
                let l_renamed = rename_in_qq(namemap, x.clone());
                let r_renamed = rename_in_qq(namemap, y.clone());
                Rc::new(SExp::Cons(l.clone(), l_renamed, r_renamed))
            }
            _ => body,
        })
}

/* Given a cons cell, rename occurrences of oldname to newname */
fn rename_in_cons(
    namemap: &HashMap<Vec<u8>, Vec<u8>>,
    body: Rc<SExp>,
    qq_handling: bool,
) -> Rc<SExp> {
    match body.borrow() {
        SExp::Atom(l, name) => match namemap.get(name) {
            Some(v) => Rc::new(SExp::Atom(l.clone(), v.to_vec())),
            None => body,
        },
        SExp::Cons(l, f, r) => {
            if let SExp::Atom(la, q) = f.borrow() {
                if q == b"q" {
                    return Rc::new(SExp::Cons(
                        l.clone(),
                        Rc::new(SExp::Atom(la.clone(), "q".as_bytes().to_vec())),
                        r.clone(),
                    ));
                } else if *q == "quote".as_bytes().to_vec() {
                    return r
                        .proper_list()
                        .map(|x| match &x[..] {
                            [v] => Rc::new(SExp::Cons(
                                l.clone(),
                                Rc::new(SExp::atom_from_string(la.clone(), "quote")),
                                Rc::new(SExp::Cons(
                                    v.loc(),
                                    Rc::new(v.clone()),
                                    Rc::new(SExp::Nil(v.loc())),
                                )),
                            )),
                            _ => body.clone(),
                        })
                        .unwrap_or_else(|| body.clone());
                } else if *q == "qq".as_bytes().to_vec() && qq_handling {
                    return r
                        .proper_list()
                        .map(|x| match &x[..] {
                            [qqexpr] => rename_in_qq(namemap, Rc::new(qqexpr.clone())),
                            _ => body.clone(),
                        })
                        .unwrap_or_else(|| body.clone());
                }
            }

            Rc::new(SExp::Cons(
                l.clone(),
                rename_in_cons(namemap, f.clone(), qq_handling),
                rename_in_cons(namemap, r.clone(), qq_handling),
            ))
        }
        _ => body.clone(),
    }
}

/* Returns a list of pairs containing the old and new atom names */
pub fn invent_new_names_sexp(body: Rc<SExp>) -> Vec<(Vec<u8>, Vec<u8>)> {
    match body.borrow() {
        SExp::Atom(_, name) => {
            if name != &[b'@'] {
                vec![(name.to_vec(), gensym(name.to_vec()))]
            } else {
                vec![]
            }
        }
        SExp::Cons(_, head, tail) => {
            let mut head_list = invent_new_names_sexp(head.clone());
            let mut tail_list = invent_new_names_sexp(tail.clone());
            head_list.append(&mut tail_list);
            head_list
        }
        _ => {
            vec![]
        }
    }
}

#[derive(Debug, Clone)]
struct InnerRenameList {
    bindings: HashMap<Vec<u8>, Vec<u8>>,
    from_wing: Binding,
}

fn make_binding_unique(b: &Binding) -> InnerRenameList {
    match &b.pattern {
        BindingPattern::Name(name) => {
            let mut single_name_map = HashMap::new();
            let new_name = gensym(name.clone());
            single_name_map.insert(name.to_vec(), new_name.clone());
            InnerRenameList {
                bindings: single_name_map,
                from_wing: Binding {
                    loc: b.loc.clone(),
                    nl: b.nl.clone(),
                    pattern: BindingPattern::Name(new_name),
                    body: b.body.clone(),
                },
            }
        }
        BindingPattern::Complex(pat) => {
            let new_names_vec = invent_new_names_sexp(pat.clone());
            let mut new_names = HashMap::new();

            for (n, v) in new_names_vec.iter() {
                new_names.insert(n.clone(), v.clone());
            }

            let renamed_pattern = rename_in_cons(&new_names, pat.clone(), false);
            InnerRenameList {
                bindings: new_names,
                from_wing: Binding {
                    loc: b.loc.clone(),
                    nl: b.nl.clone(),
                    pattern: BindingPattern::Complex(renamed_pattern),
                    body: b.body.clone(),
                },
            }
        }
    }
}

pub fn rename_assign_bindings(
    l: &Srcloc,
    bindings: &[Rc<Binding>],
    body: Rc<BodyForm>,
) -> Result<(BodyForm, Vec<Rc<Binding>>), CompileErr> {
    // Order the bindings.
    let sorted_bindings = toposort_assign_bindings(l, bindings)?;
    let mut renames = HashMap::new();
    let renamed_bindings = sorted_bindings
        .iter()
        .rev()
        .map(|item| {
            let b: &Binding = bindings[item.index].borrow();
            if let BindingPattern::Complex(p) = &b.pattern {
                let new_names = invent_new_names_sexp(p.clone());
                for (name, renamed) in new_names.iter() {
                    renames.insert(name.clone(), renamed.clone());
                }
                Binding {
                    pattern: BindingPattern::Complex(rename_in_cons(&renames, p.clone(), false)),
                    body: Rc::new(rename_in_bodyform(&renames, b.body.clone())),
                    ..b.clone()
                }
            } else {
                b.clone()
            }
        })
        .rev()
        .map(Rc::new)
        .collect();
    Ok((rename_in_bodyform(&renames, body), renamed_bindings))
}

fn rename_in_bodyform(namemap: &HashMap<Vec<u8>, Vec<u8>>, b: Rc<BodyForm>) -> BodyForm {
    match b.borrow() {
        BodyForm::Let(kind, letdata) => {
            let new_bindings = letdata
                .bindings
                .iter()
                .map(|b| {
                    Rc::new(Binding {
                        loc: b.loc(),
                        nl: b.nl.clone(),
                        pattern: b.pattern.clone(),
                        body: Rc::new(rename_in_bodyform(namemap, b.body.clone())),
                    })
                })
                .collect();
            let new_body = rename_in_bodyform(namemap, letdata.body.clone());
            BodyForm::Let(
                kind.clone(),
                Box::new(LetData {
                    bindings: new_bindings,
                    body: Rc::new(new_body),
                    ..*letdata.clone()
                }),
            )
        }

        BodyForm::Quoted(atom) => match atom {
            SExp::Atom(l, n) => match namemap.get(n) {
                Some(named) => BodyForm::Quoted(SExp::Atom(l.clone(), named.to_vec())),
                None => BodyForm::Quoted(atom.clone()),
            },
            _ => BodyForm::Quoted(atom.clone()),
        },

        BodyForm::Value(atom) => match atom {
            SExp::Atom(l, n) => match namemap.get(n) {
                Some(named) => BodyForm::Value(SExp::Atom(l.clone(), named.to_vec())),
                None => BodyForm::Value(atom.clone()),
            },
            _ => BodyForm::Value(atom.clone()),
        },

        BodyForm::Call(l, vs, tail) => {
            let new_vs = vs
                .iter()
                .enumerate()
                .map(|(i, x)| {
                    if i == 0 {
                        x.clone()
                    } else {
                        Rc::new(rename_in_bodyform(namemap, x.clone()))
                    }
                })
                .collect();
            let new_tail = tail
                .as_ref()
                .map(|t| Rc::new(rename_in_bodyform(namemap, t.clone())));
            BodyForm::Call(l.clone(), new_vs, new_tail)
        }

        BodyForm::Mod(l, prog) => BodyForm::Mod(l.clone(), prog.clone()),
        BodyForm::Lambda(ldata) => {
            let renamed_capture_inputs =
                Rc::new(rename_in_bodyform(namemap, ldata.captures.clone()));
            let renamed_capture_outputs =
                rename_in_cons(namemap, ldata.capture_args.clone(), false);
            // Rename the lambda's own arguments.
            let arg_renames = invent_new_names_sexp(ldata.args.clone());
            let mut arg_rename_map = HashMap::new();
            let mut downstream_namemap = namemap.clone();
            for (n, v) in arg_renames.into_iter() {
                arg_rename_map.insert(n.clone(), v.clone());
                downstream_namemap.insert(n, v);
            }
            let renamed_args = rename_in_cons(&arg_rename_map, ldata.args.clone(), false);
            let renamed_body = rename_in_bodyform(&downstream_namemap, ldata.body.clone());
            BodyForm::Lambda(Box::new(LambdaData {
                captures: renamed_capture_inputs,
                capture_args: renamed_capture_outputs,
                args: renamed_args,
                body: Rc::new(renamed_body),
                ..*ldata.clone()
            }))
        }
    }
}

pub fn desugar_sequential_let_bindings(
    bindings: &[Rc<Binding>],
    body: &BodyForm,
    n: usize, // Zero is for post-termination
) -> BodyForm {
    if n == 0 {
        body.clone()
    } else {
        let want_binding = bindings[n - 1].clone();
        desugar_sequential_let_bindings(
            bindings,
            &BodyForm::Let(
                LetFormKind::Parallel,
                Box::new(LetData {
                    loc: want_binding.loc(),
                    kw: None,
                    bindings: vec![want_binding],
                    inline_hint: None,
                    body: Rc::new(body.clone()),
                }),
            ),
            n - 1,
        )
    }
}

fn rename_args_bodyform(b: &BodyForm) -> BodyForm {
    match b {
        BodyForm::Let(LetFormKind::Sequential, letdata) => {
            // Renaming a sequential let is exactly as if the bindings were
            // nested in separate parallel lets.
            rename_args_bodyform(&desugar_sequential_let_bindings(
                &letdata.bindings,
                letdata.body.borrow(),
                letdata.bindings.len(),
            ))
        }

        BodyForm::Let(LetFormKind::Parallel, letdata) => {
            let renames: Vec<InnerRenameList> = letdata
                .bindings
                .iter()
                .map(|x| make_binding_unique(x.borrow()))
                .collect();
            let new_renamed_bindings: Vec<Rc<Binding>> = renames
                .iter()
                .map(|ir| Rc::new(ir.from_wing.clone()))
                .collect();
            let mut local_namemap = HashMap::new();
            for ir in renames.iter() {
                for (oldname, binding_name) in ir.bindings.iter() {
                    local_namemap.insert(oldname.to_vec(), binding_name.clone());
                }
            }
            let new_bindings = new_renamed_bindings
                .iter()
                .map(|x| {
                    Rc::new(Binding {
                        loc: x.loc.clone(),
                        nl: x.nl.clone(),
                        pattern: x.pattern.clone(),
                        body: Rc::new(rename_args_bodyform(&x.body)),
                    })
                })
                .collect();
            let locally_renamed_body = rename_in_bodyform(&local_namemap, letdata.body.clone());
            BodyForm::Let(
                LetFormKind::Parallel,
                Box::new(LetData {
                    bindings: new_bindings,
                    body: Rc::new(locally_renamed_body),
                    ..*letdata.clone()
                }),
            )
        }

        BodyForm::Let(LetFormKind::Assign, _letdata) => b.clone(),

        BodyForm::Quoted(e) => BodyForm::Quoted(e.clone()),
        BodyForm::Value(v) => BodyForm::Value(v.clone()),

        BodyForm::Call(l, vs, tail) => {
            let new_vs = vs
                .iter()
                .map(|a| Rc::new(rename_args_bodyform(a)))
                .collect();
            let new_tail = tail
                .as_ref()
                .map(|t| Rc::new(rename_args_bodyform(t.borrow())));
            BodyForm::Call(l.clone(), new_vs, new_tail)
        }
        BodyForm::Mod(l, program) => BodyForm::Mod(l.clone(), program.clone()),
        BodyForm::Lambda(ldata) => BodyForm::Lambda(ldata.clone()),
    }
}

fn rename_in_helperform(namemap: &HashMap<Vec<u8>, Vec<u8>>, h: &HelperForm) -> HelperForm {
    match h {
        HelperForm::Deftype(_) => h.clone(),
        HelperForm::Defconstant(defc) => HelperForm::Defconstant(DefconstData {
            body: Rc::new(rename_in_bodyform(namemap, defc.body.clone())),
            ..defc.clone()
        }),
        HelperForm::Defmacro(mac) => HelperForm::Defmacro(DefmacData {
            program: Rc::new(rename_in_compileform(namemap, mac.program.clone())),
            ..mac.clone()
        }),
        HelperForm::Defun(inline, defun) => HelperForm::Defun(
            *inline,
            DefunData {
                body: Rc::new(rename_in_bodyform(namemap, defun.body.clone())),
                ..defun.clone()
            },
        ),
    }
}

pub fn rename_args_helperform(h: &HelperForm) -> HelperForm {
    match h {
        HelperForm::Deftype(_) => h.clone(),
        HelperForm::Defconstant(defc) => HelperForm::Defconstant(DefconstData {
            body: Rc::new(rename_args_bodyform(defc.body.borrow())),
            ..defc.clone()
        }),
        HelperForm::Defmacro(mac) => {
            let mut new_names: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();
            for x in invent_new_names_sexp(mac.args.clone()).iter() {
                new_names.insert(x.0.clone(), x.1.clone());
            }
            let mut local_namemap = HashMap::new();
            for x in new_names.iter() {
                local_namemap.insert(x.0.to_vec(), x.1.to_vec());
            }
            let local_renamed_arg = rename_in_cons(&local_namemap, mac.args.clone(), true);
            let local_renamed_body = rename_args_compileform(mac.program.borrow());
            HelperForm::Defmacro(DefmacData {
                args: local_renamed_arg,
                program: Rc::new(rename_in_compileform(
                    &local_namemap,
                    Rc::new(local_renamed_body),
                )),
                ..mac.clone()
            })
        }
        HelperForm::Defun(inline, defun) => {
            let new_names = invent_new_names_sexp(defun.args.clone());
            let mut local_namemap = HashMap::new();
            for x in new_names.iter() {
                local_namemap.insert(x.0.clone(), x.1.clone());
            }
            let local_renamed_arg = rename_in_cons(&local_namemap, defun.args.clone(), true);
            let local_renamed_body = rename_args_bodyform(defun.body.borrow());
            let renamed_bodyform = rename_in_bodyform(&local_namemap, Rc::new(local_renamed_body));
            HelperForm::Defun(
                *inline,
                DefunData {
                    args: local_renamed_arg,
                    body: Rc::new(renamed_bodyform),
                    ..defun.clone()
                },
            )
        }
    }
}

fn rename_in_compileform(namemap: &HashMap<Vec<u8>, Vec<u8>>, c: Rc<CompileForm>) -> CompileForm {
    CompileForm {
        loc: c.loc.clone(),
        args: c.args.clone(),
        include_forms: c.include_forms.clone(),
        helpers: c
            .helpers
            .iter()
            .map(|x| rename_in_helperform(namemap, x))
            .collect(),
        exp: Rc::new(rename_in_bodyform(namemap, c.exp.clone())),
        ty: c.ty.clone(),
    }
}

pub fn rename_children_compileform(c: &CompileForm) -> CompileForm {
    let local_renamed_helpers = c.helpers.iter().map(rename_args_helperform).collect();
    let local_renamed_body = rename_args_bodyform(c.exp.borrow());
    CompileForm {
        loc: c.loc.clone(),
        args: c.args.clone(),
        include_forms: c.include_forms.clone(),
        helpers: local_renamed_helpers,
        exp: Rc::new(local_renamed_body),
        ty: c.ty.clone(),
    }
}

pub fn rename_args_compileform(c: &CompileForm) -> CompileForm {
    let new_names = invent_new_names_sexp(c.args.clone());
    let mut local_namemap = HashMap::new();
    for x in new_names.iter() {
        local_namemap.insert(x.0.clone(), x.1.clone());
    }
    let local_renamed_arg = rename_in_cons(&local_namemap, c.args.clone(), true);
    let local_renamed_helpers: Vec<HelperForm> =
        c.helpers.iter().map(rename_args_helperform).collect();
    let local_renamed_body = rename_args_bodyform(c.exp.borrow());
    CompileForm {
        loc: c.loc(),
        args: local_renamed_arg,
        include_forms: c.include_forms.clone(),
        helpers: local_renamed_helpers
            .iter()
            .map(|x| rename_in_helperform(&local_namemap, x))
            .collect(),
        exp: Rc::new(rename_in_bodyform(
            &local_namemap,
            Rc::new(local_renamed_body),
        )),
        ty: c.ty.clone(),
    }
}
