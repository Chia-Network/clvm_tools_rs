use std::borrow::Borrow;
use std::rc::Rc;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::compiler::KNOWN_DIALECTS;
use crate::compiler::comptypes::{CompileErr, CompilerOpts, IncludeDesc};
use crate::compiler::evaluate::Evaluator;
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::ErrInto;

struct Preprocessor {
    opts: Rc<dyn CompilerOpts>,
    evaluator: Evaluator
}

impl Preprocessor {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        let runner = Rc::new(DefaultProgramRunner::new());
        Preprocessor {
            opts: opts.clone(),
            evaluator: Evaluator::new(opts, runner, Vec::new())
        }
    }

    pub fn process_include(
        &mut self,
        include: IncludeDesc,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let filename_and_content = self.opts.read_new_file(self.opts.filename(), decode_string(&include.name))?;
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

    fn recurse_dependencies(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        desc: IncludeDesc
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

        let parsed = parse_sexp(Srcloc::start(&full_name), content.bytes())?;
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

    /* Expand include inline in forms */
    fn process_pp_form(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        body: Rc<SExp>,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        // Support using the preprocessor to collect dependencies recursively.
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
            self.recurse_dependencies(includes, i.clone())?;
            self.process_include(i)
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
                enlist(body.loc(), v_clone)
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

        while let SExp::Cons(_,f,r) = tocompile.borrow() {
            let mut lst = self.process_pp_form(includes, f.clone())?;
            result.append(&mut lst);
            tocompile = r.clone();
        }

        Ok(result)
    }
}

pub fn preprocess(
    opts: Rc<dyn CompilerOpts>,
    includes: &mut Vec<IncludeDesc>,
    cmod: Rc<SExp>
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let mut p = Preprocessor::new(opts);
    p.run(includes, cmod)
}

// Visit all files used during compilation.
pub fn gather_dependencies(
    opts: Rc<dyn CompilerOpts>,
    real_input_path: &str,
    file_content: &str,
) -> Result<Vec<IncludeDesc>, CompileErr> {
    let mut includes = Vec::new();
    let mut p = Preprocessor::new(opts);
    let loc = Srcloc::start(real_input_path);

    let parsed = parse_sexp(loc.clone(), file_content.bytes())?;

    if parsed.is_empty() {
        return Ok(vec![]);
    }

    for elt in parsed.iter() {
        p.run(&mut includes, elt.clone())?;
    }

    Ok(includes)
}
