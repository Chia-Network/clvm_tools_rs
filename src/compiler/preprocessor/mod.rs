mod macros;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::clvmc::compile_clvm_text_maybe_opt;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};

use crate::compiler::cldb::hex_to_modern_sexp;
use crate::compiler::clvm::convert_from_clvm_rs;
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompilerOpts, HelperForm, IncludeDesc, IncludeProcessType,
};
use crate::compiler::dialect::KNOWN_DIALECTS;
use crate::compiler::evaluate::{create_argument_captures, dequote, ArgInputs, Evaluator};
use crate::compiler::frontend::compile_helperform;
use crate::compiler::preprocessor::macros::PreprocessorExtension;
use crate::compiler::rename::rename_args_helperform;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{
    decode_string, enlist, parse_sexp, Atom, NodeSel, SExp, SelectNode, ThisNode,
};
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

struct Preprocessor {
    opts: Rc<dyn CompilerOpts>,
    runner: Rc<dyn TRunProgram>,
    helpers: Vec<HelperForm>,
    strict: bool,
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

fn make_defmac_name(name: &[u8]) -> Vec<u8> {
    let mut res = b"__chia__defmac__".to_vec();
    res.append(&mut name.to_vec());
    res
}

impl Preprocessor {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        let runner = Rc::new(DefaultProgramRunner::new());
        Preprocessor {
            opts: opts.clone(),
            runner,
            helpers: Vec::new(),
            strict: opts.dialect().strict,
        }
    }

    /// Given a specification of an include file, load up the forms inside it and
    /// return them (or an error if the file couldn't be read or wasn't a list).
    pub fn process_include(&mut self, include: &IncludeDesc) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let filename_and_content = self
            .opts
            .read_new_file(self.opts.filename(), decode_string(&include.name))?;
        let content = filename_and_content.1;
        let start_of_file = Srcloc::start(&decode_string(&include.name));

        // Because we're also subsequently returning CompileErr later in the pipe,
        // this needs an explicit err map.
        let parsed: Vec<Rc<SExp>> = parse_sexp(start_of_file.clone(), content.iter().copied())
            .err_into()
            .and_then(|x| match x[0].proper_list() {
                None => Err(CompileErr(
                    start_of_file,
                    "Includes should contain a list of forms".to_string(),
                )),
                Some(v) => Ok(v.iter().map(|x| Rc::new(x.clone())).collect()),
            })?;

        if self.strict {
            let mut result = Vec::new();
            for p in parsed.into_iter() {
                if let Some(res) = self.expand_macros(p.clone(), true)? {
                    result.push(res);
                }
            }

            Ok(result)
        } else {
            Ok(parsed)
        }
    }

    fn process_embed(
        &mut self,
        loc: Srcloc,
        fname: &str,
        kind: &IncludeProcessType,
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

        let (full_name, content) = self
            .opts
            .read_new_file(self.opts.filename(), fname.to_string())?;
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
                    self.opts.optimize(),
                    self.opts.clone(),
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

    // Support using the preprocessor to collect dependencies recursively.
    fn recurse_dependencies(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        kind: IncludeProcessType,
        desc: IncludeDesc,
    ) -> Result<(), CompileErr> {
        let name_string = decode_string(&desc.name);
        if KNOWN_DIALECTS.contains_key(&name_string) {
            return Ok(());
        }

        let (full_name, content) = self.opts.read_new_file(self.opts.filename(), name_string)?;
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
                self.process_pp_form(includes, Rc::new(elt.clone()))?;
            }
        }

        Ok(())
    }

    fn add_helper(&mut self, h: HelperForm) {
        for i in 0..=self.helpers.len() {
            if i == self.helpers.len() {
                self.helpers.push(h);
                break;
            } else if self.helpers[i].name() == h.name() {
                self.helpers[i] = h;
                break;
            }
        }
    }

    // Check for and apply preprocessor level macros.
    // This is maximally permissive.
    fn expand_macros(
        &mut self,
        body: Rc<SExp>,
        start: bool,
    ) -> Result<Option<Rc<SExp>>, CompileErr> {
        if let SExp::Cons(l, f, r) = body.borrow() {
            // First expand inner macros.
            let first_expanded = self.expand_macros(f.clone(), true)?;
            let rest_expanded = self.expand_macros(r.clone(), false)?;
            let new_self = match (first_expanded, rest_expanded) {
                (None, None) => Some(body.clone()),
                (Some(f), None) => Some(Rc::new(SExp::Cons(l.clone(), f, r.clone()))),
                (None, Some(r)) => Some(Rc::new(SExp::Cons(l.clone(), f.clone(), r))),
                (Some(f), Some(r)) => Some(Rc::new(SExp::Cons(l.clone(), f, r))),
            };

            if !start {
                return Ok(new_self);
            }

            if let Ok(NodeSel::Cons((_, name), args)) =
                NodeSel::Cons(Atom::Here(()), ThisNode::Here)
                    .select_nodes(new_self.clone().unwrap_or_else(|| body.clone()))
            {
                let defmac_name = make_defmac_name(&name);

                // See if it's a form that calls one of our macros.
                for m in self.helpers.iter() {
                    if let HelperForm::Defun(_, mdata) = &m {
                        // We record upfront macros
                        if mdata.name != defmac_name {
                            continue;
                        }

                        // as inline defuns because they're closest to that
                        // semantically.
                        let mut allocator = Allocator::new();
                        // The name matched, try calling it.

                        // Form argument env.
                        let mut macro_arg_env = HashMap::new();
                        let args_borrowed: &SExp = args.borrow();
                        create_argument_captures(
                            &mut macro_arg_env,
                            &ArgInputs::Whole(Rc::new(BodyForm::Quoted(args_borrowed.clone()))),
                            mdata.args.clone(),
                        )?;

                        let ppext = Rc::new(PreprocessorExtension::new());
                        let mut eval = Evaluator::new(
                            ppext.enrich_prims(self.opts.clone()),
                            self.runner.clone(),
                            self.helpers.clone(),
                        );
                        eval.add_extension(ppext);
                        let res = eval.shrink_bodyform(
                            &mut allocator,
                            mdata.args.clone(),
                            &macro_arg_env,
                            mdata.body.clone(),
                            false,
                            None,
                        )?;

                        if let Ok(unquoted) = dequote(body.loc(), res) {
                            return Ok(Some(unquoted));
                        } else {
                            return Err(CompileErr(
                                body.loc(),
                                "Failed to fully evaluate macro".to_string(),
                            ));
                        }
                    }
                }
            }

            return Ok(new_self);
        }

        Ok(None)
    }

    // If it's a defmac (preprocessor level macro), add it to the evaulator.
    fn decode_macro(&mut self, definition: Rc<SExp>) -> Result<Option<()>, CompileErr> {
        if let Ok(NodeSel::Cons(
            (defmac_loc, kw),
            NodeSel::Cons((nl, name), NodeSel::Cons(args, body)),
        )) = NodeSel::Cons(
            Atom::Here(()),
            NodeSel::Cons(
                Atom::Here(()),
                NodeSel::Cons(ThisNode::Here, ThisNode::Here),
            ),
        )
        .select_nodes(definition.clone())
        {
            let is_defmac = kw == b"defmac";
            if is_defmac
                || kw == b"defmacro"
                || kw == b"defun"
                || kw == b"defun-inline"
                || kw == b"defconst"
                || kw == b"defconstant"
            {
                if is_defmac {
                    let target_defun = Rc::new(SExp::Cons(
                        defmac_loc.clone(),
                        Rc::new(SExp::atom_from_string(defmac_loc, "defun")),
                        Rc::new(SExp::Cons(
                            nl.clone(),
                            Rc::new(SExp::Atom(nl, make_defmac_name(&name))),
                            Rc::new(SExp::Cons(args.loc(), args.clone(), body)),
                        )),
                    ));
                    if let Some(helper) = compile_helperform(self.opts.clone(), target_defun)? {
                        self.add_helper(rename_args_helperform(&helper));
                    } else {
                        return Err(CompileErr(
                            definition.loc(),
                            "defmac found but couldn't be converted to function".to_string(),
                        ));
                    }
                } else if let Some(helper) = compile_helperform(self.opts.clone(), definition)? {
                    self.add_helper(rename_args_helperform(&helper));
                }
            }
        }

        Ok(None)
    }

    /* Expand include inline in forms */
    fn process_pp_form(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        unexpanded_body: Rc<SExp>,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let body = self
            .expand_macros(unexpanded_body.clone(), true)?
            .unwrap_or_else(|| unexpanded_body.clone());
        // Support using the preprocessor to collect dependencies recursively.
        let included: Option<IncludeType> = body
            .proper_list()
            .map(|x| x.iter().map(|elt| elt.atomize()).collect())
            .map(|x: Vec<SExp>| {
                match &x[..] {
                    [SExp::Atom(kw, inc), SExp::Atom(nl, fname)] => {
                        if "include".as_bytes().to_vec() == *inc {
                            return Ok(Some(IncludeType::Basic(
                                IncludeDesc {
                                    kw: kw.clone(),
                                    nl: nl.clone(),
                                    name: fname.clone(),
                                    kind: None,
                                }
                            )));
                        }
                    }
                    [SExp::Atom(kw, inc), SExp::QuotedString(nl, _, fname)] => {
                        if "include".as_bytes().to_vec() == *inc {
                            return Ok(Some(IncludeType::Basic(
                                IncludeDesc {
                                    kw: kw.clone(),
                                    nl: nl.clone(),
                                    name: fname.clone(),
                                    kind: None,
                                }
                            )));
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
                            if "include".as_bytes().to_vec() == *inc {
                                return Err(CompileErr(
                                    body.loc(),
                                    format!("bad tail in include {body}"),
                                ));
                            } else {
                                // Try to pick up helperforms.
                                if let Some(()) = self.decode_macro(body.clone())? {
                                    return Ok(None);
                                }
                            }
                        }
                    }
                }

                Ok(None)
            })
            .unwrap_or_else(|| Ok(None))?;

        if let Some(()) = self.decode_macro(body.clone())? {
            Ok(vec![])
        } else if let Some(IncludeType::Basic(i)) = &included {
            self.recurse_dependencies(includes, IncludeProcessType::Compiled, i.clone())?;
            self.process_include(i)
        } else if let Some(IncludeType::Processed(f, kind, name)) = &included {
            self.recurse_dependencies(includes, kind.clone(), f.clone())?;
            self.process_embed(body.loc(), &decode_string(&f.name), kind, name)
        } else {
            Ok(vec![body])
        }
    }

    fn inject_std_macros(&mut self, body: Rc<SExp>) -> SExp {
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

    pub fn run(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        cmod: Rc<SExp>,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let mut result = Vec::new();
        let mut tocompile = if self.opts.stdenv() {
            let injected = self.inject_std_macros(cmod);
            Rc::new(injected)
        } else {
            cmod
        };

        while let SExp::Cons(_, f, r) = tocompile.borrow() {
            let mut lst = self.process_pp_form(includes, f.clone())?;
            result.append(&mut lst);
            tocompile = r.clone();
        }

        Ok(result)
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
    let mut p = Preprocessor::new(opts);
    p.run(includes, cmod)
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
    let no_stdenv_opts = opts.set_stdenv(false);
    let mut p = Preprocessor::new(no_stdenv_opts);
    let loc = Srcloc::start(real_input_path);

    let parsed = parse_sexp(loc, file_content.bytes())?;

    if parsed.is_empty() {
        return Ok(vec![]);
    }

    for elt in parsed.iter() {
        p.run(&mut includes, elt.clone())?;
    }

    Ok(includes)
}
