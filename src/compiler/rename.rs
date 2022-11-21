use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::comptypes::{
    Binding, BodyForm, CompileForm, DefconstData, DefmacData, DefunData, HelperForm, LetData,
    LetFormKind,
};
use crate::compiler::gensym::gensym;
use crate::compiler::sexp::SExp;

fn rename_in_qq(namemap: &HashMap<Vec<u8>, Vec<u8>>, body: Rc<SExp>) -> Rc<SExp> {
    body.proper_list()
        .and_then(|x| {
            if let [SExp::Atom(_, q), body] = &x[..] {
                if q == b"unquote" {
                    return Some(rename_in_cons(namemap, Rc::new(body.clone())));
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
fn rename_in_cons(namemap: &HashMap<Vec<u8>, Vec<u8>>, body: Rc<SExp>) -> Rc<SExp> {
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
                } else if *q == "qq".as_bytes().to_vec() {
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
                rename_in_cons(namemap, f.clone()),
                rename_in_cons(namemap, r.clone()),
            ))
        }
        _ => body.clone(),
    }
}

/* Returns a list of pairs containing the old and new atom names */
fn invent_new_names_sexp(body: Rc<SExp>) -> Vec<(Vec<u8>, Vec<u8>)> {
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

fn make_binding_unique(b: &Binding) -> (Vec<u8>, Binding) {
    (
        b.name.to_vec(),
        Binding {
            loc: b.loc.clone(),
            nl: b.nl.clone(),
            name: gensym(b.name.clone()),
            body: b.body.clone(),
        },
    )
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
                        name: b.name.clone(),
                        body: Rc::new(rename_in_bodyform(namemap, b.body.clone())),
                    })
                })
                .collect();
            let new_body = rename_in_bodyform(namemap, letdata.body.clone());
            BodyForm::Let(
                kind.clone(),
                LetData {
                    loc: letdata.loc.clone(),
                    kw: letdata.kw.clone(),
                    bindings: new_bindings,
                    body: Rc::new(new_body),
                },
            )
        }

        BodyForm::Quoted(atom) => match atom.borrow() {
            SExp::Atom(l, n) => match namemap.get(n) {
                Some(named) => BodyForm::Quoted(SExp::Atom(l.clone(), named.to_vec())),
                None => BodyForm::Quoted(atom.clone()),
            },
            _ => BodyForm::Quoted(atom.clone()),
        },

        BodyForm::Value(atom) => match atom.borrow() {
            SExp::Atom(l, n) => match namemap.get(n) {
                Some(named) => BodyForm::Value(SExp::Atom(l.clone(), named.to_vec())),
                None => BodyForm::Value(atom.clone()),
            },
            _ => BodyForm::Value(atom.clone()),
        },

        BodyForm::Call(l, vs) => {
            let new_vs = vs
                .iter()
                .map(|x| Rc::new(rename_in_bodyform(namemap, x.clone())))
                .collect();
            BodyForm::Call(l.clone(), new_vs)
        }

        BodyForm::Mod(l, prog) => BodyForm::Mod(l.clone(), prog.clone()),
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
                LetData {
                    loc: want_binding.loc(),
                    kw: None,
                    bindings: vec![want_binding],
                    body: Rc::new(body.clone()),
                },
            ),
            n - 1,
        )
    }
}

fn rename_args_bodyform(b: &BodyForm) -> BodyForm {
    match b.borrow() {
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
            let renames: Vec<(Vec<u8>, Binding)> = letdata
                .bindings
                .iter()
                .map(|x| make_binding_unique(x.borrow()))
                .collect();
            let new_renamed_bindings: Vec<Rc<Binding>> =
                renames.iter().map(|(_, x)| Rc::new(x.clone())).collect();
            let mut local_namemap = HashMap::new();
            for x in renames.iter() {
                let (oldname, binding) = x;
                local_namemap.insert(oldname.to_vec(), binding.name.clone());
            }
            let new_bindings = new_renamed_bindings
                .iter()
                .map(|x| {
                    Rc::new(Binding {
                        loc: x.loc.clone(),
                        nl: x.nl.clone(),
                        name: x.name.clone(),
                        body: Rc::new(rename_args_bodyform(&x.body)),
                    })
                })
                .collect();
            let locally_renamed_body = rename_in_bodyform(&local_namemap, letdata.body.clone());
            BodyForm::Let(
                LetFormKind::Parallel,
                LetData {
                    loc: letdata.loc.clone(),
                    kw: letdata.kw.clone(),
                    bindings: new_bindings,
                    body: Rc::new(locally_renamed_body),
                },
            )
        }

        BodyForm::Quoted(e) => BodyForm::Quoted(e.clone()),
        BodyForm::Value(v) => BodyForm::Value(v.clone()),

        BodyForm::Call(l, vs) => {
            let new_vs = vs
                .iter()
                .map(|a| Rc::new(rename_args_bodyform(a)))
                .collect();
            BodyForm::Call(l.clone(), new_vs)
        }
        BodyForm::Mod(l, program) => BodyForm::Mod(l.clone(), program.clone()),
    }
}

fn rename_in_helperform(namemap: &HashMap<Vec<u8>, Vec<u8>>, h: &HelperForm) -> HelperForm {
    match h {
        HelperForm::Defconstant(defc) => HelperForm::Defconstant(DefconstData {
            loc: defc.loc.clone(),
            name: defc.name.to_vec(),
            nl: defc.nl.clone(),
            kw: defc.kw.clone(),
            body: Rc::new(rename_in_bodyform(namemap, defc.body.clone())),
        }),
        HelperForm::Defmacro(mac) => HelperForm::Defmacro(DefmacData {
            loc: mac.loc.clone(),
            kw: mac.kw.clone(),
            nl: mac.nl.clone(),
            name: mac.name.to_vec(),
            args: mac.args.clone(),
            program: Rc::new(rename_in_compileform(namemap, mac.program.clone())),
        }),
        HelperForm::Defun(inline, defun) => HelperForm::Defun(
            *inline,
            DefunData {
                loc: defun.loc.clone(),
                kw: defun.kw.clone(),
                nl: defun.nl.clone(),
                name: defun.name.to_vec(),
                args: defun.args.clone(),
                body: Rc::new(rename_in_bodyform(namemap, defun.body.clone())),
            },
        ),
    }
}

fn rename_args_helperform(h: &HelperForm) -> HelperForm {
    match h {
        HelperForm::Defconstant(defc) => HelperForm::Defconstant(DefconstData {
            loc: defc.loc.clone(),
            nl: defc.nl.clone(),
            kw: defc.kw.clone(),
            name: defc.name.clone(),
            body: Rc::new(rename_args_bodyform(defc.body.borrow())),
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
            let local_renamed_arg = rename_in_cons(&local_namemap, mac.args.clone());
            let local_renamed_body = rename_args_compileform(mac.program.borrow());
            HelperForm::Defmacro(DefmacData {
                loc: mac.loc.clone(),
                kw: mac.kw.clone(),
                nl: mac.nl.clone(),
                name: mac.name.clone(),
                args: local_renamed_arg,
                program: Rc::new(rename_in_compileform(
                    &local_namemap,
                    Rc::new(local_renamed_body),
                )),
            })
        }
        HelperForm::Defun(inline, defun) => {
            let new_names = invent_new_names_sexp(defun.args.clone());
            let mut local_namemap = HashMap::new();
            for x in new_names.iter() {
                local_namemap.insert(x.0.clone(), x.1.clone());
            }
            let local_renamed_arg = rename_in_cons(&local_namemap, defun.args.clone());
            let local_renamed_body = rename_args_bodyform(defun.body.borrow());
            HelperForm::Defun(
                *inline,
                DefunData {
                    loc: defun.loc.clone(),
                    nl: defun.nl.clone(),
                    kw: defun.kw.clone(),
                    name: defun.name.clone(),
                    args: local_renamed_arg,
                    body: Rc::new(rename_in_bodyform(
                        &local_namemap,
                        Rc::new(local_renamed_body),
                    )),
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
    }
}

pub fn rename_args_compileform(c: &CompileForm) -> CompileForm {
    let new_names = invent_new_names_sexp(c.args.clone());
    let mut local_namemap = HashMap::new();
    for x in new_names.iter() {
        local_namemap.insert(x.0.clone(), x.1.clone());
    }
    let local_renamed_arg = rename_in_cons(&local_namemap, c.args.clone());
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
    }
}
