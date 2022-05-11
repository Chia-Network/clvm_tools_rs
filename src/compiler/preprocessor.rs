use std::borrow::Borrow;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};

use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::sexp::{enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

pub fn process_include(
    opts: Rc<dyn CompilerOpts>,
    name: &String,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename_and_content = opts.read_new_file(opts.filename(), name.to_string())?;
    let content = filename_and_content.1;

    let start_of_file = Srcloc::start(&name);

    parse_sexp(start_of_file.clone(), &content)
        .map_err(|e| CompileErr(e.0.clone(), e.1.clone()))
        .and_then(|x| match x[0].proper_list() {
            None => Err(CompileErr(
                start_of_file,
                "Includes should contain a list of forms".to_string(),
            )),
            Some(v) => {
                let res: Vec<Rc<SExp>> = v.iter().map(|x| Rc::new(x.clone())).collect();
                Ok(res)
            }
        })
}

/* Expand include inline in forms */
fn process_pp_form(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename: Option<Vec<u8>> = body
        .proper_list()
        .map(|x| {
            match &x[..] {
                [SExp::Atom(_, inc), SExp::Atom(_, fname)] => {
                    if "include".as_bytes().to_vec() == *inc {
                        return Ok(Some(fname.clone()));
                    }
                }
                [SExp::Atom(_, inc), SExp::QuotedString(_, _, fname)] => {
                    if "include".as_bytes().to_vec() == *inc {
                        return Ok(Some(fname.clone()));
                    }
                }

                [] => {}

                // Ensure that legal empty or atom expressions don't try include
                _ => {
                    // Include is only allowed as a proper form.  It's a keyword in
                    // this language.
                    match &x[0] {
                        SExp::Atom(_, inc) => {
                            if "include".as_bytes().to_vec() == *inc {
                                return Err(CompileErr(
                                    body.loc(),
                                    format!("bad tail in include {}", body.to_string()),
                                ));
                            }
                        }
                        _ => {}
                    }
                }
            }

            Ok(None)
        })
        .unwrap_or_else(|| Ok(None))?;

    match filename {
        Some(f) => process_include(
            opts,
            &Bytes::new(Some(BytesFromType::Raw(f.to_vec()))).decode(),
        ),
        _ => Ok(vec![body]),
    }
}

fn preprocess_(opts: Rc<dyn CompilerOpts>, body: Rc<SExp>) -> Result<Vec<Rc<SExp>>, CompileErr> {
    match body.borrow() {
        SExp::Cons(_, head, rest) => match rest.borrow() {
            SExp::Nil(_nl) => process_pp_form(opts, head.clone()),
            _ => {
                let lst = process_pp_form(opts.clone(), head.clone())?;
                let mut rs = preprocess_(opts, rest.clone())?;
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
                Rc::new(SExp::atom_from_string(body.loc(), &"include".to_string())),
                Rc::new(SExp::Cons(
                    body.loc(),
                    Rc::new(SExp::quoted_from_string(
                        body.loc(),
                        &"*macros*".to_string(),
                    )),
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

pub fn preprocess(opts: Rc<dyn CompilerOpts>, cmod: Rc<SExp>) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let tocompile = if opts.stdenv() {
        let injected = inject_std_macros(cmod);
        Rc::new(injected)
    } else {
        cmod
    };

    preprocess_(opts, tocompile)
}
