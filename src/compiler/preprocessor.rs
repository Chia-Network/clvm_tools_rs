use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::compiler::KNOWN_DIALECTS;
use crate::compiler::comptypes::{CompileErr, CompilerOpts, IncludeDesc};
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::ErrInto;

pub fn process_include(
    opts: Rc<dyn CompilerOpts>,
    include: IncludeDesc,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename_and_content = opts.read_new_file(opts.filename(), decode_string(&include.name))?;
    let content = filename_and_content.1;
    let start_of_file = Srcloc::start(&decode_string(&include.name));

    // Because we're also subsequently returning CompileErr later in the pipe,
    // this needs an explicit err map.
    parse_sexp(start_of_file.clone(), content.bytes())
        .err_into()
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
    // Support using the preprocessor to collect dependencies recursively.
    let recurse_dependencies = |opts: Rc<dyn CompilerOpts>,
                                includes: &mut Vec<IncludeDesc>,
                                desc: IncludeDesc|
     -> Result<(), CompileErr> {
        let name_string = decode_string(&desc.name);
        if KNOWN_DIALECTS.contains_key(&name_string) {
            return Ok(());
        }

        let (full_name, content) = opts.read_new_file(opts.filename(), name_string)?;
        includes.push(IncludeDesc {
            name: full_name.as_bytes().to_vec(),
            ..desc
        });

        let parsed = parse_sexp(Srcloc::start(&full_name), content.bytes())?;
        if parsed.is_empty() {
            return Ok(());
        }

        let program_form = parsed[0].clone();
        if let Some(l) = program_form.proper_list() {
            for elt in l.iter() {
                process_pp_form(opts.clone(), includes, Rc::new(elt.clone()))?;
            }
        }

        Ok(())
    };

    let included: Option<IncludeDesc> = body
        .proper_list()
        .map(|x| x.iter().map(|elt| elt.atomize()).collect())
        .map(|x: Vec<SExp>| {
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
                                format!("bad tail in include {body}"),
                            ));
                        }
                    }
                }
            }

            Ok(None)
        })
        .unwrap_or_else(|| Ok(None))?;

    if let Some(i) = included {
        recurse_dependencies(opts.clone(), includes, i.clone())?;
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

// Visit all files used during compilation.
pub fn gather_dependencies(
    opts: Rc<dyn CompilerOpts>,
    real_input_path: &str,
    file_content: &str,
) -> Result<Vec<IncludeDesc>, CompileErr> {
    let mut includes = Vec::new();
    let loc = Srcloc::start(real_input_path);

    let parsed = parse_sexp(loc.clone(), file_content.bytes())?;

    if parsed.is_empty() {
        return Ok(vec![]);
    }

    if let Some(l) = parsed[0].proper_list() {
        for elt in l.iter() {
            process_pp_form(opts.clone(), &mut includes, Rc::new(elt.clone()))?;
        }
    } else {
        return Err(CompileErr(loc, "malformed list body".to_string()));
    };

    Ok(includes)
}
