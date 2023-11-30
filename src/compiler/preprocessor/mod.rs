mod macros;

use num_bigint::ToBigInt;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::binutils::assemble;
use crate::classic::clvm_tools::clvmc::compile_clvm_text_maybe_opt;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};

use crate::compiler::cldb::hex_to_modern_sexp;
use crate::compiler::clvm;
use crate::compiler::clvm::{convert_from_clvm_rs, truthy};
use crate::compiler::compiler::compile_from_compileform;
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, HelperForm, ImportLongName, IncludeDesc, IncludeProcessType, ModuleImportSpec,
};
use crate::compiler::dialect::{detect_modern, KNOWN_DIALECTS};
use crate::compiler::evaluate::{create_argument_captures, ArgInputs};
use crate::compiler::frontend::{compile_helperform, frontend};
use crate::compiler::optimize::get_optimizer;
use crate::compiler::preprocessor::macros::PreprocessorExtension;
use crate::compiler::rename::rename_args_helperform;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{
    decode_string, enlist, parse_sexp, Atom, NodeSel, SExp, SelectNode, ThisNode,
};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::CompileContextWrapper;
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

#[derive(Clone, Debug)]
struct ImportedModule {
    name: ImportLongName,
}

#[derive(Debug, Clone)]
struct ModuleAndImportSpec {
    name: ImportLongName,
    spec: ModuleImportSpec,
}

#[derive(Debug)]
struct ImportNameMap {
    scope_id: usize,
    name: Option<ImportLongName>,
    import_specs: Vec<ModuleAndImportSpec>,
}

#[derive(Debug, Clone)]
struct HelperNamespace {
    defined_in: Option<ImportLongName>,
    with_namespace: Vec<ModuleAndImportSpec>,
}

#[derive(Debug, Clone)]
struct NamespacedHelperForm {
    helper: HelperForm,
    full_name: ImportLongName,
    context: Option<HelperNamespace>
}

struct Preprocessor {
    opts: Rc<dyn CompilerOpts>,
    ppext: Rc<PreprocessorExtension>,
    runner: Rc<dyn TRunProgram>,
    helpers: Vec<NamespacedHelperForm>,
    strict: bool,
    stored_macros: HashMap<Vec<u8>, Rc<SExp>>,

    scope_id: usize,
    namespace_stack: Vec<ImportNameMap>,
    imported_modules: HashMap<ImportLongName, ImportedModule>,
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

fn nilize(v: Rc<SExp>) -> Rc<SExp> {
    if let SExp::Cons(l, a, b) = v.borrow() {
        let a_conv = nilize(a.clone());
        let b_conv = nilize(b.clone());
        if Rc::as_ptr(&a_conv) == Rc::as_ptr(a) && Rc::as_ptr(&b_conv) == Rc::as_ptr(b) {
            v.clone()
        } else {
            Rc::new(SExp::Cons(l.clone(), a_conv, b_conv))
        }
    } else if !truthy(v.clone()) {
        Rc::new(SExp::Nil(v.loc()))
    } else {
        v
    }
}

struct IterateIncludeUnit {
    parsed: Vec<Rc<SExp>>,
    item: usize,
}

impl Iterator for IterateIncludeUnit {
    type Item = Rc<SExp>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item >= self.parsed.len() {
            return None;
        }

        let current_item = self.item;
        self.item += 1;

        Some(self.parsed[current_item].clone())
    }
}

/// Import modules can be enclosed, but needn't be:
///
/// An import file that contains a nil or a list beginning with a nonempty cons is
/// an enclosed clinc (classic style), otherwise it's a list of helper forms.
fn get_module_iterator(parsed: &[Rc<SExp>]) -> IterateIncludeUnit {
    // An empty form is a modern include file with 0 helpers.
    if parsed.is_empty() {
        return IterateIncludeUnit {
            parsed: vec![],
            item: 0,
        };
    }

    // A single form is an enclosed clinc if it is headed by a cons form.
    if parsed.len() == 1 {
        if let Some(lst) = parsed[0].proper_list() {
            if lst.is_empty() {
                return IterateIncludeUnit {
                    parsed: vec![],
                    item: 0,
                };
            }

            if !matches!(lst[0].borrow(), SExp::Cons(_, _, _)) {
                return IterateIncludeUnit {
                    parsed: parsed.iter().cloned().collect(),
                    item: 0,
                };
            }

            return IterateIncludeUnit {
                parsed: lst.iter().cloned().map(Rc::new).collect(),
                item: 0,
            };
        }
    }

    // More than one form: conventional, not enclosed.
    IterateIncludeUnit {
        parsed: parsed.iter().cloned().collect(),
        item: 0,
    }
}

fn import_name_to_module_name(
    loc: Srcloc,
    from_module: Option<&ImportLongName>,
    name: &[u8],
) -> Result<ImportLongName, CompileErr> {
    let (relative, parsed) = ImportLongName::parse(name);
    if relative {
        if let Some(m) = from_module {
            return Ok(m.combine(&parsed));
        }

        return Err(CompileErr(
            loc,
            "Relative module name requested from a module entry file".to_string()
        ));
    }

    Ok(parsed)
}

fn make_defalias_form(
    loc: Srcloc,
    scope_id: usize,
    module_name: &ImportLongName,
    spec: &ModuleImportSpec,
) -> Rc<SExp> {
    let mut form = vec![
        SExp::Atom(loc.clone(), b"defalias".to_vec()),
        SExp::Atom(loc.clone(), b"rename".to_vec()),
        SExp::Atom(loc.clone(), b"scope".to_vec()),
        SExp::Integer(loc.clone(), scope_id.to_bigint().unwrap()),
        SExp::Atom(loc.clone(), module_name.as_u8_vec(false)),
    ];

    match spec {
        ModuleImportSpec::Qualified(Some(qname)) => {
            todo!();
        }
        ModuleImportSpec::Qualified(None) => {
            todo!();
        }
        ModuleImportSpec::Exposing(names) => {
            for n in names.iter() {
                form.push(SExp::Atom(loc.clone(), n.clone()));
            }
        }
        ModuleImportSpec::Hiding(names) => {
            todo!();
        }
    }

    let rc_form_vec: Vec<Rc<SExp>> = form.into_iter().map(Rc::new).collect();
    Rc::new(enlist(loc, &rc_form_vec))
}

fn make_scope_head(
    loc: Srcloc,
    scope_id: usize,
    module_name: &ImportLongName,
) -> Rc<SExp> {
    let form = vec![
        SExp::Atom(loc.clone(), b"defalias".to_vec()),
        SExp::Atom(loc.clone(), b"shorten".to_vec()),
        SExp::Atom(loc.clone(), module_name.as_u8_vec(false)),
        SExp::Integer(loc.clone(), scope_id.to_bigint().unwrap())
    ];

    let rc_form_vec: Vec<Rc<SExp>> = form.into_iter().map(Rc::new).collect();
    Rc::new(enlist(loc, &rc_form_vec))
}

fn make_scope_tail(
    loc: Srcloc,
    scope_id: usize,
    module_name: &ImportLongName,
) -> Rc<SExp> {
    let form = vec![
        SExp::Atom(loc.clone(), b"defalias".to_vec()),
        SExp::Atom(loc.clone(), b"end-scope".to_vec()),
        SExp::Integer(loc.clone(), scope_id.to_bigint().unwrap())
    ];

    let rc_form_vec: Vec<Rc<SExp>> = form.into_iter().map(Rc::new).collect();
    Rc::new(enlist(loc, &rc_form_vec))
}

impl Preprocessor {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        let runner = Rc::new(DefaultProgramRunner::new());
        let ppext = Rc::new(PreprocessorExtension::new());
        let opts_prims = ppext.enrich_prims(opts.clone());
        Preprocessor {
            opts: opts_prims,
            ppext,
            runner,
            helpers: Vec::new(),
            strict: opts.dialect().strict,
            stored_macros: HashMap::default(),
            scope_id: 1,
            imported_modules: HashMap::default(),
            namespace_stack: Vec::new(),
        }
    }

    /// Get the current module name.
    pub fn current_module_name(&self) -> Option<ImportLongName> {
        if self.namespace_stack.is_empty() {
            None
        } else if let Some(name) = &self.namespace_stack[self.namespace_stack.len()-1].name {
            Some(name.clone())
        } else {
            None
        }
    }

    /// Compute the expected filename from a module name.  It must be absolute
    /// if we're in the root file of a program, otherwise it can be relative.
    /// The namespace_stack determines that.
    pub fn import_name_to_module_name(
        &self,
        loc: Srcloc,
        name: &[u8]
    ) -> Result<ImportLongName, CompileErr> {
        let reference_name = self.current_module_name();
        import_name_to_module_name(loc, reference_name.as_ref(), name)
    }

    /// Given a specification of an include file, load up the forms inside it and
    /// return them (or an error if the file couldn't be read or wasn't a list).
    pub fn process_include(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        include: &IncludeDesc,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
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
            for p in get_module_iterator(&parsed).into_iter() {
                let mut new_forms = self.process_pp_form(includes, p.clone())?;
                result.append(&mut new_forms);
            }

            Ok(result)
        } else {
            Ok(parsed)
        }
    }

    fn import_new_module(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        import_name: &ImportLongName
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let filename = decode_string(&import_name.as_u8_vec(true));
        let (full_name, content) = self
            .opts
            .read_new_file(self.opts.filename(), filename)?;

        let parsed = parse_sexp(Srcloc::start(&full_name), content.iter().copied())
            .map_err(|e| CompileErr(e.0, e.1))?;

        let import_name_u8 = import_name.as_u8_vec(false);
        let mut out_forms = vec![];

        self.scope_id += 1;

        self.namespace_stack.push(ImportNameMap {
            scope_id: self.scope_id,
            name: Some(import_name.clone()),
            import_specs: vec![],
        });

        for p in parsed.iter() {
            for form in self.process_pp_form(includes, p.clone())? {
                out_forms.push(form.clone());
            }
        }

        self.namespace_stack.pop();

        Ok(out_forms)
    }

    /// Do common tasks necessary to fix the current namespace for the module
    /// import.
    fn fixup_for_module_import(
        &mut self,
        loc: Srcloc,
        spec: &ModuleImportSpec,
        module: &ImportedModule,
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let mut short_imported_names: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();
        if !self.namespace_stack.is_empty() {
            let len = self.namespace_stack.len();
            let inames: &mut ImportNameMap = &mut self.namespace_stack[len - 1];
            inames.import_specs.push(ModuleAndImportSpec {
                name: module.name.clone(),
                spec: spec.clone(),
            });
        }

        // Make defalias form.
        let scope_id = self.namespace_stack[self.namespace_stack.len()-1].scope_id;
        Ok(vec![make_defalias_form(loc, scope_id, &module.name, spec)])
    }

    fn import_module(
        &mut self,
        loc: Srcloc,
        includes: &mut Vec<IncludeDesc>,
        spec: &ModuleImportSpec,
        import_name: &[u8]
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        // The name of a module needs more processing.
        let full_import_name = self.import_name_to_module_name(loc.clone(), import_name)?;
        if let Some(m) = self.imported_modules.get(&full_import_name) {
            // We've processed this already, generate namespace directives.
            let m_copy = m.clone();
            return self.fixup_for_module_import(loc, spec, &m_copy);
        }

        // Process this module.
        let mut helper_forms: Vec<Rc<SExp>> = Vec::new();
        let scope_id = self.namespace_stack[self.namespace_stack.len()-1].scope_id;

        helper_forms.push(make_scope_head(loc.clone(), scope_id, &full_import_name));
        helper_forms.extend(self.import_new_module(includes, &full_import_name)?);
        helper_forms.push(make_scope_tail(loc.clone(), scope_id, &full_import_name));

        // Generate and install an ImportedModule for self.imported_modules.
        let imported_module = ImportedModule {
            name: full_import_name.clone(),
        };

        self.imported_modules.insert(full_import_name.clone(), imported_module.clone());

        let mut finish_forms: Vec<Rc<SExp>> = self.fixup_for_module_import(loc, spec, &imported_module)?;
        helper_forms.extend(finish_forms);
        Ok(helper_forms)
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

        let content =
            if let IncludeProcessType::Bin = &kind {
                Rc::new(SExp::Atom(loc.clone(), content))
            } else if let IncludeProcessType::Hex = &kind {
                hex_to_modern_sexp(
                    &mut allocator,
                    &HashMap::new(),
                    loc.clone(),
                    &decode_string(&content),
                )
                    .map_err(run_to_compile_err)?
            } else if let IncludeProcessType::Compiled = &kind {
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
            } else { // IncludeProcessType::SExpression
                let parsed = parse_sexp(Srcloc::start(&full_name), content.iter().copied())
                    .map_err(|e| CompileErr(e.0, e.1))?;
                if parsed.len() != 1 {
                    return Err(CompileErr(loc, format!("More than one form in {fname}")));
                }

                parsed[0].clone()
            };

        Ok(vec![compose_defconst(loc, constant_name, content)])
    }

    // Support using the preprocessor to collect dependencies recursively.
    fn recurse_dependencies(
        &mut self,
        includes: &mut Vec<IncludeDesc>,
        kind: Option<IncludeProcessType>,
        desc: IncludeDesc,
    ) -> Result<(), CompileErr> {
        // Process an import
        let name_string =
            if let Some(IncludeProcessType::Module(_)) = kind {
                decode_string(&self.import_name_to_module_name(desc.nl.clone(), &desc.name)?.as_u8_vec(true))
            } else {
                decode_string(&desc.name)
            };

        if KNOWN_DIALECTS.contains_key(&name_string) {
            return Ok(());
        }

        let (full_name, content) = self.opts.read_new_file(self.opts.filename(), name_string)?;
        includes.push(IncludeDesc {
            name: full_name.as_bytes().to_vec(),
            ..desc
        });

        if !matches!(kind, Some(IncludeProcessType::Compiled)) {
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

    fn get_namespace_context(&self) -> Option<HelperNamespace> {
        if self.namespace_stack.is_empty() {
            return None;
        }

        let namespace = &self.namespace_stack[self.namespace_stack.len()-1];
        Some(HelperNamespace {
            defined_in: namespace.name.clone(),
            with_namespace: namespace.import_specs.clone(),
        })
    }

    fn add_helper(&mut self, h: HelperForm) {
        let helper_context = self.get_namespace_context();
        // We compute a qualified name to call the helper by.
        let computed_name = helper_context.as_ref().and_then(|hctx| {
            hctx.defined_in.as_ref().map(|hmod| hmod.with_child(h.name()))
        }).unwrap_or_else(|| {
            let (_, name) = ImportLongName::parse(h.name());
            name
        });

        for i in 0..=self.helpers.len() {
            if i == self.helpers.len() {
                self.helpers.push(NamespacedHelperForm {
                    full_name: computed_name,
                    helper: h,
                    context: helper_context,
                });
                break;
            } else if self.helpers[i].full_name == computed_name {
                self.helpers[i].helper = h;
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
                    if let HelperForm::Defun(_, mdata) = &m.helper {
                        // We record upfront macros
                        if mdata.name != defmac_name {
                            continue;
                        }

                        // The name matched, try calling it.

                        // Form argument env.
                        let mut macro_arg_env = HashMap::new();
                        let args_borrowed: &SExp = args.borrow();
                        create_argument_captures(
                            &mut macro_arg_env,
                            &ArgInputs::Whole(Rc::new(BodyForm::Quoted(args_borrowed.clone()))),
                            mdata.args.clone(),
                        )?;

                        let mut allocator = Allocator::new();
                        let compiled_program =
                            if let Some(compiled_program) = self.stored_macros.get(&mdata.name) {
                                compiled_program.clone()
                            } else {
                                // as inline defuns because they're closest to that
                                // semantically.
                                let optimizer = get_optimizer(&body.loc(), self.opts.clone())?;
                                let mut symbol_table = HashMap::new();
                                let mut wrapper = CompileContextWrapper::new(
                                    &mut allocator,
                                    self.runner.clone(),
                                    &mut symbol_table,
                                    optimizer,
                                );
                                let new_program = CompileForm {
                                    loc: body.loc(),
                                    args: mdata.args.clone(),
                                    include_forms: vec![],
                                    helpers: self.helpers.iter().map(|hn| hn.helper.clone()).collect(),
                                    exp: mdata.body.clone(),
                                    ty: None,
                                };
                                let compiled_program = compile_from_compileform(
                                    &mut wrapper.context,
                                    self.opts.clone(),
                                    new_program,
                                )?;
                                self.stored_macros
                                    .insert(mdata.name.clone(), Rc::new(compiled_program.clone()));
                                Rc::new(compiled_program)
                            };

                        let ppext: &PreprocessorExtension = self.ppext.borrow();
                        let res = clvm::run(
                            &mut allocator,
                            self.runner.clone(),
                            self.opts.prim_map(),
                            compiled_program,
                            args.clone(),
                            Some(ppext),
                            None,
                        )
                        .map(nilize)
                        .map_err(CompileErr::from)?;

                        if let Some(final_result) = self.expand_macros(res.clone(), true)? {
                            return Ok(Some(final_result));
                        } else {
                            return Ok(Some(res));
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
                || kw == b"defalias"
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
                    if let Some(helpers) = compile_helperform(self.opts.clone(), target_defun)? {
                        for h in helpers.new_helpers.iter() {
                            self.add_helper(rename_args_helperform(h)?);
                        }
                    } else {
                        return Err(CompileErr(
                            definition.loc(),
                            "defmac found but couldn't be converted to function".to_string(),
                        ));
                    }
                } else if let Some(helpers) = compile_helperform(self.opts.clone(), definition)? {
                    for h in helpers.new_helpers.iter() {
                        self.add_helper(rename_args_helperform(h)?);
                    }
                }
            }
        }

        Ok(None)
    }

    fn parse_import(&mut self, form: &[SExp]) -> Result<Option<IncludeType>, CompileErr> {
        if form.len() < 2 {
            return Ok(None);
        }

        let kw = form[0].loc();
        if let SExp::Atom(_, import_name) = &form[0] {
            if import_name != b"import" {
                return Ok(None);
            }
        }

        let (nl, fname) = if let SExp::Atom(nl, fname) = &form[1] {
            (nl.clone(), fname.clone())
        } else if let SExp::QuotedString(nl, _, fname) = &form[1] {
            (nl.clone(), fname.clone())
        } else {
            return Err(CompileErr(
                form[1].loc(),
                "Name must be an atom or string".to_string(),
            ));
        };

        let spec = ModuleImportSpec::parse(form, 1)?;
        let mod_kind = IncludeProcessType::Module(spec);

        Ok(Some(IncludeType::Processed(
            IncludeDesc {
                kw: kw.clone(),
                nl: nl.clone(),
                name: fname.clone(),
                kind: Some(mod_kind.clone()),
            },
            mod_kind,
            fname.clone()
        )))
    }

    fn parse_include(&mut self, form: &[SExp]) -> Result<Option<IncludeType>, CompileErr> {
        if let [SExp::Atom(kw, include_kw), include_name] = form {
            if include_kw != b"include" {
                return Ok(None);
            }

            let (nl, fname) = if let SExp::Atom(nl, fname) = include_name {
                (nl.clone(), fname.clone())
            } else if let SExp::QuotedString(nl, _, fname) = include_name {
                (nl.clone(), fname.clone())
            } else {
                return Err(CompileErr(
                    include_name.loc(),
                    "Name must be an atom or string".to_string(),
                ));
            };

            return Ok(Some(IncludeType::Basic(IncludeDesc {
                kw: kw.clone(),
                nl: nl.clone(),
                name: fname.clone(),
                kind: None,
            })));
        }

        Ok(None)
    }

    fn parse_embed(
        &mut self,
        body: Rc<SExp>,
        form: &[SExp],
    ) -> Result<Option<IncludeType>, CompileErr> {
        if let [SExp::Atom(kl, embed_file), SExp::Atom(_, name), SExp::Atom(kind_loc, kind), fname_atom] =
            form
        {
            if embed_file != b"embed-file" {
                return Ok(None);
            }

            let (nl, fname) = if let SExp::Atom(nl, fname) = fname_atom {
                (nl.clone(), fname.clone())
            } else if let SExp::QuotedString(nl, _, fname) = fname_atom {
                (nl.clone(), fname.clone())
            } else {
                return Err(CompileErr(
                    fname_atom.loc(),
                    "Name must be an atom or string".to_string(),
                ));
            };

            if kind == b"hex" {
                return Ok(Some(IncludeType::Processed(
                    IncludeDesc {
                        kw: kl.clone(),
                        nl: nl.clone(),
                        kind: Some(IncludeProcessType::Hex),
                        name: fname.clone(),
                    },
                    IncludeProcessType::Hex,
                    name.clone(),
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
                    kind_loc.clone(),
                    format!("bad include kind in embed-file {body}"),
                ));
            }
        } else if let [SExp::Atom(kl, compile_file), SExp::Atom(_, name), fname_atom] = form {
            if compile_file != b"compile-file" {
                return Ok(None);
            }

            let (nl, fname) = if let SExp::Atom(nl, fname) = fname_atom {
                (nl.clone(), fname.clone())
            } else if let SExp::QuotedString(nl, _, fname) = fname_atom {
                (nl.clone(), fname.clone())
            } else {
                return Err(CompileErr(
                    fname_atom.loc(),
                    "Name must be an atom or string".to_string(),
                ));
            };

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
        let as_list: Option<Vec<SExp>> = body
            .proper_list()
            .map(|x| x.iter().map(|elt| elt.atomize()).collect());
        let included: Option<IncludeType> = if let Some(x) = as_list.as_ref() {
            if let Some(res) = self.parse_import(x)? {
                Some(res)
            } else if let Some(res) = self.parse_include(x)? {
                Some(res)
            } else if let Some(res) = self.parse_embed(body.clone(), x)? {
                Some(res)
            } else if !x.is_empty() {
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

                None
            } else {
                None
            }
        } else {
            None
        };

        if let Some(IncludeType::Basic(i)) = &included {
            self.recurse_dependencies(includes, None, i.clone())?;
            self.process_include(includes, i)
        } else if let Some(IncludeType::Processed(f, IncludeProcessType::Module(spec), name)) = &included {
            if self.namespace_stack.is_empty() {
                self.namespace_stack.push(ImportNameMap {
                    scope_id: 0,
                    name: None,
                    import_specs: Vec::new(),
                });
            }
            self.import_module(body.loc(), includes, spec, name)
        } else if let Some(IncludeType::Processed(f, kind, name)) = &included {
            self.recurse_dependencies(includes, Some(kind.clone()), f.clone())?;
            self.process_embed(body.loc(), &decode_string(&f.name), kind, name)
        } else if let Some(()) = self.decode_macro(body.clone())? {
            Ok(vec![])
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
    mut opts: Rc<dyn CompilerOpts>,
    real_input_path: &str,
    file_content: &str,
) -> Result<Vec<IncludeDesc>, CompileErr> {
    let mut allocator = Allocator::new();

    let assembled_input = assemble(&mut allocator, file_content)
        .map_err(|e| CompileErr(Srcloc::start(real_input_path), e.1))?;
    let dialect = detect_modern(&mut allocator, assembled_input);
    opts = opts.set_stdenv(dialect.strict).set_dialect(dialect.clone());
    if let Some(stepping) = dialect.stepping {
        opts = opts
            .set_optimize(stepping > 22)
            .set_frontend_opt(stepping > 21);
    }

    let parsed = parse_sexp(Srcloc::start(real_input_path), file_content.bytes())?;
    let program = frontend(opts, &parsed)?;

    let filtered_results: Vec<IncludeDesc> = program
        .include_forms
        .into_iter()
        .filter(|f| !f.name.starts_with(b"*"))
        .collect();
    Ok(filtered_results)
}
