use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::clvmc::compile_clvm_text_maybe_opt;

use crate::compiler::cldb::hex_to_modern_sexp;
use crate::compiler::clvm::convert_from_clvm_rs;
use crate::compiler::compiler::KNOWN_DIALECTS;
use crate::compiler::comptypes::{CompileErr, CompilerOpts, IncludeDesc, IncludeProcessType};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::ErrInto;

/// Determines how an included file is used.
///
/// Basic means that the file contains helper forms to include in the program.
/// Processed means that some kind of processing is done and the result is a named
/// constant.
#[derive(Clone, Debug)]
enum IncludeType {
    /// Normal include in chialisp.  The code in the target file will join the
    /// program being compiled.
    Basic(IncludeDesc),
    /// The data in the file will be processed in some way and the result will
    /// live in a named constant.
    Processed(IncludeDesc, IncludeProcessType, Vec<u8>),
}

/// Given a specification of an include file, load up the forms inside it and
/// return them (or an error if the file couldn't be read or wasn't a list).
pub fn process_include(
    opts: Rc<dyn CompilerOpts>,
    include: IncludeDesc,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename_and_content = opts.read_new_file(opts.filename(), decode_string(&include.name))?;
    let content = filename_and_content.1;
    let start_of_file = Srcloc::start(&decode_string(&include.name));

    // Because we're also subsequently returning CompileErr later in the pipe,
    // this needs an explicit err map.
    parse_sexp(start_of_file.clone(), content.iter().copied())
        .err_into()
        .and_then(|x| match x[0].proper_list() {
            None => Err(CompileErr(
                start_of_file,
                "Includes should contain a list of forms".to_string(),
            )),
            Some(v) => Ok(v.iter().map(|x| Rc::new(x.clone())).collect()),
        })
}

fn compose_defconst(loc: Srcloc, name: &[u8], sexp: Rc<SExp>) -> Rc<SExp> {
    Rc::new(enlist(
        loc.clone(),
        &[
            Rc::new(SExp::Atom(loc.clone(), b"defconst".to_vec())),
            Rc::new(SExp::Atom(loc.clone(), name.to_vec())),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc, vec![1])),
                sexp,
            )),
        ],
    ))
}

fn process_embed(
    loc: Srcloc,
    opts: Rc<dyn CompilerOpts>,
    fname: &str,
    kind: IncludeProcessType,
    constant_name: &[u8],
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let mut allocator = Allocator::new();
    let run_to_compile_err = |e| match e {
        RunFailure::RunExn(l, x) => CompileErr(
            l,
            format!("failed to convert compiled clvm to expression: throw ({x})"),
        ),
        RunFailure::RunErr(l, e) => CompileErr(
            l,
            format!("failed to convert compiled clvm to expression: {e}"),
        ),
    };

    let (full_name, content) = opts.read_new_file(opts.filename(), fname.to_string())?;
    let content = match kind {
        IncludeProcessType::Bin => Rc::new(SExp::Atom(loc.clone(), content)),
        IncludeProcessType::Hex => hex_to_modern_sexp(
            &mut allocator,
            &HashMap::new(),
            loc.clone(),
            &decode_string(&content),
        )
        .map_err(run_to_compile_err)?,
        IncludeProcessType::SExpression => {
            let parsed = parse_sexp(Srcloc::start(&full_name), content.iter().copied())
                .map_err(|e| CompileErr(e.0, e.1))?;
            if parsed.len() != 1 {
                return Err(CompileErr(loc, format!("More than one form in {fname}")));
            }

            parsed[0].clone()
        }
        IncludeProcessType::Compiled => {
            let decoded_content = decode_string(&content);
            let mut symtab = HashMap::new();
            let newly_compiled = compile_clvm_text_maybe_opt(
                &mut allocator,
                opts.optimize(),
                opts,
                &mut symtab,
                &decoded_content,
                &full_name,
                true,
            )
            .map_err(|e| CompileErr(loc.clone(), format!("Subcompile failed: {}", e.1)))?;

            convert_from_clvm_rs(&mut allocator, loc.clone(), newly_compiled)
                .map_err(run_to_compile_err)?
        }
    };

    Ok(vec![compose_defconst(loc, constant_name, content)])
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
                                kind: IncludeProcessType,
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

        if !matches!(kind, IncludeProcessType::Compiled) {
            return Ok(());
        }

        let parsed = parse_sexp(Srcloc::start(&full_name), content.iter().copied())
            .map_err(|e| CompileErr(e.0, e.1))?;
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

    let include_type: Option<IncludeType> = body
        .proper_list()
        .map(|x| x.iter().map(|elt| elt.atomize()).collect())
        .map(|x: Vec<SExp>| {
            match &x[..] {
                [SExp::Atom(kw, inc), SExp::Atom(nl, fname)] => {
                    if inc == b"include" {
                        return Ok(Some(IncludeType::Basic(IncludeDesc {
                            kw: kw.clone(),
                            nl: nl.clone(),
                            kind: None,
                            name: fname.clone(),
                        })));
                    }
                }

                [SExp::Atom(kl, compile_file), SExp::Atom(_, name), SExp::Atom(nl, fname)] => {
                    if compile_file == b"compile-file" {
                        return Ok(Some(IncludeType::Processed(
                            IncludeDesc {
                                kw: kl.clone(),
                                nl: nl.clone(),
                                kind: Some(IncludeProcessType::Compiled),

                                name: fname.clone(),
                            },
                            IncludeProcessType::Compiled,
                            name.clone()
                        )));
                    }
                }

                [SExp::Atom(kl, embed_file), SExp::Atom(_, name), SExp::Atom(_, kind), SExp::Atom(nl, fname)] => {
                    if embed_file == b"embed-file" {
                        if kind == b"hex" {
                            return Ok(Some(IncludeType::Processed(
                                IncludeDesc {
                                    kw: kl.clone(),
                                    nl: nl.clone(),
                                    kind: Some(IncludeProcessType::Hex),
                                    name: fname.clone(),
                                },
                                IncludeProcessType::Hex,
                                name.clone()
                            )));
                        } else if kind == b"bin" {
                            return Ok(Some(IncludeType::Processed(
                                IncludeDesc {
                                    kw: kl.clone(),
                                    nl: nl.clone(),
                                    kind: Some(IncludeProcessType::Bin),
                                    name: fname.clone(),
                                },
                                IncludeProcessType::Bin,
                                name.clone(),
                            )));
                        } else if kind == b"sexp" {
                            return Ok(Some(IncludeType::Processed(
                                IncludeDesc {
                                    kw: kl.clone(),
                                    nl: nl.clone(),
                                    kind: Some(IncludeProcessType::SExpression),
                                    name: fname.clone(),
                                },
                                IncludeProcessType::SExpression,
                                name.clone(),
                            )));
                        } else {
                            return Err(CompileErr(
                                body.loc(),
                                format!("bad include kind in embed-file {body}")
                            ));
                        }
                    }
                }

                [] => {}

                // Ensure that legal empty or atom expressions don't try include
                _ => {
                    // Include is only allowed as a proper form.  It's a keyword in
                    // this language.
                    if let SExp::Atom(_, inc) = &x[0] {
                        if inc == b"include" {
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

    match include_type {
        Some(IncludeType::Basic(f)) => {
            recurse_dependencies(
                opts.clone(),
                includes,
                IncludeProcessType::Compiled,
                f.clone(),
            )?;
            process_include(opts, f)
        }
        Some(IncludeType::Processed(f, kind, name)) => {
            recurse_dependencies(opts.clone(), includes, kind.clone(), f.clone())?;
            process_embed(
                body.loc(),
                opts,
                &Bytes::new(Some(BytesFromType::Raw(f.name.to_vec()))).decode(),
                kind,
                &name,
            )
        }
        _ => Ok(vec![body]),
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
            enlist(body.loc(), &v_clone)
        }
        _ => {
            let body_clone: &SExp = body.borrow();
            body_clone.clone()
        }
    }
}

/// Run the preprocessor over this code, which at present just finds (include ...)
/// forms in the source and includes the content of in a combined list.  If a file
/// can't be found via the directory list in CompilerOrs.
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

/// Visit all files used during compilation.
/// This reports a list of all files used while compiling the input file, via any
/// form that causes compilation to include another file.  The file names are path
/// expanded based on the include path they were found in (from opts).
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
