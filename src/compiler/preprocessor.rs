use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::comptypes::{CompileErr, CompilerOpts, IncludeDesc};
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

pub fn process_include(
    opts: Rc<dyn CompilerOpts>,
    include: IncludeDesc,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename_and_content = opts.read_new_file(opts.filename(), decode_string(&include.name))?;
    let content = filename_and_content.1;
    let start_of_file = Srcloc::start(&decode_string(&include.name));

    parse_sexp(start_of_file.clone(), content.bytes())
        .map_err(|e| CompileErr(e.0.clone(), e.1))
        .and_then(|x| match x[0].proper_list() {
            None => Err(CompileErr(
                start_of_file,
                "Includes should contain a list of forms".to_string(),
            )),
            Some(v) => Ok(v.iter().map(|x| Rc::new(x.clone())).collect()),
        })
}

/* Expand include inline in forms */
fn process_pp_form(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let included: Option<IncludeDesc> = body
        .proper_list()
        .map(|x| {
            match &x[..] {
                [SExp::Atom(kw, inc), SExp::Atom(nl, fname)] => {
                    if "include".as_bytes().to_vec() == *inc {
                        return Ok(Some(IncludeDesc {
                            kw: kw.clone(),
                            nl: nl.clone(),
                            name: fname.clone(),
                        }));
                    }
                }
                [SExp::Atom(kw, inc), SExp::QuotedString(nl, _, fname)] => {
                    if "include".as_bytes().to_vec() == *inc {
                        return Ok(Some(IncludeDesc {
                            kw: kw.clone(),
                            nl: nl.clone(),
                            name: fname.clone(),
                        }));
                    }
                }

                [] => {}

                // Ensure that legal empty or atom expressions don't try include
                _ => {
                    // Include is only allowed as a proper form.  It's a keyword in
                    // this language.
                    if let SExp::Atom(_, inc) = &x[0] {
                        if "include".as_bytes().to_vec() == *inc {
                            return Err(CompileErr(
                                body.loc(),
                                format!("bad tail in include {}", body),
                            ));
                        }
                    }
                }
            }

            Ok(None)
        })
        .unwrap_or_else(|| Ok(None))?;

    if let Some(i) = included {
        includes.push(i.clone());
        process_include(opts, i)
    } else {
        Ok(vec![body])
    }
}

fn preprocess_(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    match body.borrow() {
        SExp::Cons(_, head, rest) => match rest.borrow() {
            SExp::Nil(_nl) => process_pp_form(opts, includes, head.clone()),
            _ => {
                let lst = process_pp_form(opts.clone(), includes, head.clone())?;
                let mut rs = preprocess_(opts, includes, rest.clone())?;
                let mut result = lst;
                result.append(&mut rs);
                Ok(result)
            }
        },
        _ => Ok(vec![body]),
    }
}

fn inject_std_macros(body: Rc<SExp>) -> SExp {
    match body.proper_list() {
        Some(v) => {
            let include_form = Rc::new(SExp::Cons(
                body.loc(),
                Rc::new(SExp::atom_from_string(body.loc(), "include")),
                Rc::new(SExp::Cons(
                    body.loc(),
                    Rc::new(SExp::quoted_from_string(body.loc(), "*macros*")),
                    Rc::new(SExp::Nil(body.loc())),
                )),
            ));
            let mut v_clone: Vec<Rc<SExp>> = v.iter().map(|x| Rc::new(x.clone())).collect();
            let include_copy: &SExp = include_form.borrow();
            v_clone.insert(0, Rc::new(include_copy.clone()));
            enlist(body.loc(), v_clone)
        }
        _ => {
            let body_clone: &SExp = body.borrow();
            body_clone.clone()
        }
    }
}

pub fn preprocess(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    cmod: Rc<SExp>,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let tocompile = if opts.stdenv() {
        let injected = inject_std_macros(cmod);
        Rc::new(injected)
    } else {
        cmod
    };

    preprocess_(opts, includes, tocompile)
}
