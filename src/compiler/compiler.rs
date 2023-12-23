use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero, Stream};
use crate::classic::clvm::sexp::sexp_as_bin;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::{convert_to_clvm_rs, convert_from_clvm_rs, sha256tree};
use crate::compiler::codegen::{codegen, hoist_body_let_binding, process_helper_let_bindings};
use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, IncludeDesc, PrimaryCodegen, SyntheticType};
use crate::compiler::dialect::{AcceptedDialect, KNOWN_DIALECTS, detect_modern};
use crate::compiler::frontend::{compile_bodyform, compile_helperform, frontend};
use crate::compiler::optimize::get_optimizer;
use crate::compiler::preprocessor::preprocess;
use crate::compiler::prims;
use crate::compiler::resolve::resolve_namespaces;
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::{BasicCompileContext, CompileContextWrapper};
use crate::util::Number;

lazy_static! {
    pub static ref STANDARD_MACROS: String = {
        indoc! {"(
            (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @)))
            (defmacro list ARGS
                            (defun compile-list
                                   (args)
                                   (if args
                                       (qq (c (unquote (f args))
                                             (unquote (compile-list (r args)))))
                                       ()))
                            (compile-list ARGS)
                    )
            (defun-inline / (A B) (f (divmod A B)))
            (defun-inline c* (A B) (c A B))
            (defun-inline a* (A B) (a A B))
            (defun-inline coerce (X) : (Any -> Any) X)
            (defun-inline explode (X) : (forall a ((Exec a) -> a)) X)
            (defun-inline bless (X) : (forall a ((Pair a Unit) -> (Exec a))) (coerce X))
            (defun-inline lift (X V) : (forall a (forall b ((Pair (Exec a) (Pair b Unit)) -> (Exec (Pair a b))))) (coerce X))
            (defun-inline unlift (X) : (forall a (forall b ((Pair (Exec (Pair a b)) Unit) -> (Exec b)))) (coerce X))
            )
            "}
        .to_string()
    };
    pub static ref ADVANCED_MACROS: String = {
        indoc! {"(
            (defmac __chia__primitive__if (A B C)
              (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @))
              )

            (defun __chia__if (ARGS)
              (__chia__primitive__if (r (r (r ARGS)))
                (qq (a (i (unquote (f ARGS)) (com (unquote (f (r ARGS)))) (com (unquote (__chia__if (r (r ARGS)))))) @))
                (qq (a (i (unquote (f ARGS)) (com (unquote (f (r ARGS)))) (com (unquote (f (r (r ARGS)))))) @))
                )
              )

            (defmac if ARGS (__chia__if ARGS))

            (defun __chia__compile-list (args)
              (if args
                (c 4 (c (f args) (c (__chia__compile-list (r args)) ())))
                ()
                )
              )

            (defmac list ARGS (__chia__compile-list ARGS))

            (defun-inline / (A B) (f (divmod A B)))

            (defun __chia__sha256tree (t)
              (a
                (i
                  (l t)
                  (com (sha256 2 (__chia__sha256tree (f t)) (__chia__sha256tree (r t))))
                  (com (sha256 1 t))
                  )
                @
                )
              )

            (defun-inline c* (A B) (c A B))
            (defun-inline a* (A B) (a A B))
            (defun-inline coerce (X) : (Any -> Any) X)
            (defun-inline explode (X) : (forall a ((Exec a) -> a)) X)
            (defun-inline bless (X) : (forall a ((Pair a Unit) -> (Exec a))) (coerce X))
            (defun-inline lift (X V) : (forall a (forall b ((Pair (Exec a) (Pair b Unit)) -> (Exec (Pair a b))))) (coerce X))
            (defun-inline unlift (X) : (forall a (forall b ((Pair (Exec (Pair a b)) Unit) -> (Exec b)))) (coerce X))
            )
            "}
        .to_string()
    };
}

#[derive(Clone, Debug)]
pub struct DefaultCompilerOpts {
    pub include_dirs: Vec<String>,
    pub filename: String,
    pub code_generator: Option<PrimaryCodegen>,
    pub in_defun: bool,
    pub stdenv: bool,
    pub optimize: bool,
    pub frontend_opt: bool,
    pub frontend_check_live: bool,
    pub start_env: Option<Rc<SExp>>,
    pub disassembly_ver: Option<usize>,
    pub prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    pub dialect: AcceptedDialect,
}

pub fn create_prim_map() -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
    let mut prim_map: HashMap<Vec<u8>, Rc<SExp>> = HashMap::new();

    for p in prims::prims() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }

    Rc::new(prim_map)
}

pub fn desugar_frontend(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    p0: CompileForm,
) -> Result<CompileForm, CompileErr> {
    let p1 = context.frontend_optimization(opts.clone(), p0)?;

    do_desugar(&p1)
}

pub fn do_desugar(program: &CompileForm) -> Result<CompileForm, CompileErr> {
    // Transform let bindings, merging nested let scopes with the top namespace
    let hoisted_bindings = hoist_body_let_binding(None, program.args.clone(), program.exp.clone())?;
    let mut new_helpers = hoisted_bindings.0;
    let expr = hoisted_bindings.1; // expr is the let-hoisted program

    // TODO: Distinguish the frontend_helpers and the hoisted_let helpers for later stages
    let mut combined_helpers = program.helpers.clone();
    combined_helpers.append(&mut new_helpers);
    let combined_helpers = process_helper_let_bindings(&combined_helpers)?;

    Ok(CompileForm {
        helpers: combined_helpers,
        exp: expr,
        ..program.clone()
    })
}

pub fn finish_compilation(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    p2: CompileForm,
) -> Result<SExp, CompileErr> {
    let p3 = context.post_desugar_optimization(opts.clone(), p2)?;

    // generate code from AST, optionally with optimization
    let generated = codegen(context, opts.clone(), &p3)?;

    let g2 = context.post_codegen_output_optimize(opts, generated)?;

    Ok(g2)
}

pub fn compile_from_compileform(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    p0: CompileForm,
) -> Result<SExp, CompileErr> {
    let p1 = context.frontend_optimization(opts.clone(), p0)?;

    // Resolve includes, convert program source to lexemes
    let p2 = do_desugar(&p1)?;

    finish_compilation(context, opts, p2)
}

#[derive(Debug, Clone)]
enum Export {
    MainProgram(Rc<SExp>, Rc<BodyForm>),
    Function(Vec<u8>),
}

fn match_export_form(
    opts: Rc<dyn CompilerOpts>,
    form: Rc<SExp>
) -> Result<Option<Export>, CompileErr> {
    if let Some(lst) = form.proper_list() {
        // Empty form isn't export
        if lst.is_empty() {
            return Ok(None);
        }

        // Export if it has an export keyword.
        if let SExp::Atom(_, export_name) = lst[0].borrow() {
            if export_name != b"export" {
                return Ok(None);
            }
        } else {
            // No export kw, not export.
            return Ok(None);
        }

        // A main export
        if lst.len() == 3 {
            let expr = compile_bodyform(opts.clone(), Rc::new(lst[2].clone()))?;
            return Ok(Some(Export::MainProgram(
                Rc::new(lst[1].clone()),
                Rc::new(expr)
            )));
        }

        if let SExp::Atom(_, fun_name) = lst[1].borrow() {
            return Ok(Some(Export::Function(fun_name.clone())));
        }

        return Err(CompileErr(form.loc(), format!("Malformed export {form}")));
    }

    Ok(None)
}

struct ModuleOutputEntry {
    name: Vec<u8>,
    hash: Vec<u8>,
    func: Rc<SExp>,
}

fn break_down_module_output(loc: Srcloc, run_result: Rc<SExp>) -> Result<Vec<ModuleOutputEntry>, CompileErr> {
    let list_data =
        if let Some(lst) = run_result.proper_list() {
            lst
        } else {
            return Err(CompileErr(
                loc,
                "output from intermediate module program should have been a proper list".to_string(),
            ));
        };

    if list_data.len() % 3 != 0 {
        return Err(CompileErr(loc, "output length from intermediate module program should have been divisible by 3".to_string()));
    }

    let mut result = Vec::new();
    for tuple_idx in 0..(list_data.len() / 3) {
        let i = tuple_idx * 3;
        if let (SExp::Atom(_, name), SExp::Atom(_, hash)) = (list_data[i].atomize(), list_data[i+1].atomize()) {
            result.push(ModuleOutputEntry {
                name: name.clone(),
                hash: hash.clone(),
                func: Rc::new(list_data[i+2].clone()),
            });
        } else {
            return Err(CompileErr(loc.clone(), format!("output from intermediate module program wasn't in triplets of atom, atom, program {} {} {}", list_data[i], list_data[i+1], list_data[i+2])));
        }
    }

    Ok(result)
}

fn create_hex_output_path(loc: Srcloc, file_path: &str, func: &str) -> Result<String, CompileErr> {
    let mut dir = PathBuf::from(file_path);
    dir.pop();
    let func_dot_hex = &[func.to_string(), "hex".to_string()];
    dir.push(func_dot_hex.join("."));
    dir.into_os_string().into_string().map_err(|_| {
        CompileErr(
            loc,
            format!("could not make os file path for output {func}")
        )
    })
}

#[derive(Debug, Clone)]
pub struct CompileModuleComponent {
    pub shortname: Vec<u8>,
    pub filename: String,
    pub content: Rc<SExp>,
    pub hash: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct CompileModuleOutput {
    pub summary: Rc<SExp>,
    pub components: Vec<CompileModuleComponent>
}

// Exports are returned main programs:
//
// Single main
//
// (export (X) (do-stuff X))
//
// Multiple mains
//
// (export foo)
// (export bar)
pub fn compile_module(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    includes: &[IncludeDesc],
    pre_forms: &[Rc<SExp>]
) -> Result<CompileModuleOutput, CompileErr> {
    let mut other_forms = vec![];
    let mut exports = vec![];
    let mut found_main = false;

    let loc = pre_forms[0].loc().ext(&pre_forms[pre_forms.len()-1].loc());

    for p in pre_forms.iter() {
        if let Some(export) = match_export_form(opts.clone(), p.clone())? {
            if matches!(export, Export::MainProgram(_, _)) {
                if found_main || !exports.is_empty() {
                    return Err(CompileErr(
                        loc.clone(),
                        "Only one main export is allowed, otherwise export functions".to_string()
                    ));
                }

                found_main = true;
            } else if found_main {
                return Err(CompileErr(
                    loc.clone(),
                    "A chialisp module may only export a main or a set of functions".to_string()
                ));
            }

            exports.push(export);
        } else if let Some(helpers) = compile_helperform(opts.clone(), p.clone())? {
            // Macros have been eliminated by this point.
            for helper in helpers.new_helpers.iter() {
                if !matches!(helper, HelperForm::Defmacro(_)) {
                    other_forms.push(helper.clone());
                }
            }
        }
    }

    if exports.is_empty() {
        return Err(CompileErr(
            loc.clone(),
            "A chialisp module should have at least one export".to_string()
        ));
    }

    let mut program = CompileForm {
        loc: loc.clone(),
        include_forms: includes.to_vec(),
        args: Rc::new(SExp::Nil(loc.clone())),
        helpers: other_forms.clone(),
        exp: Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone()))),
        ty: None,
    };

    if exports.len() == 1 {
        if let Export::MainProgram(args, expr) = &exports[0] {
            // Single program.
            program.args = args.clone();
            program.exp = expr.clone();

            program = resolve_namespaces(opts.clone(), &program)?;

            let output = Rc::new(compile_from_compileform(context, opts.clone(), program)?);
            let converted = convert_to_clvm_rs(
                context.allocator(),
                output.clone(),
            )?;

            let mut output_path = PathBuf::from(&opts.filename());
            output_path.set_extension("hex");
            let output_path_str = output_path.into_os_string().to_string_lossy().to_string();
            let mut stream = Stream::new(None);
            stream.write(sexp_as_bin(context.allocator(), converted));
            opts.write_new_file(&output_path_str, stream.get_value().hex().as_bytes())?;
            return Ok(CompileModuleOutput {
                summary: Rc::new(SExp::Nil(loc.clone())),
                components: vec![CompileModuleComponent {
                    shortname: b"program".to_vec(),
                    filename: output_path_str,
                    content: output.clone(),
                    hash: sha256tree(output)
                }]
            });
        }
    }

    // So we can most optimistically know a peer module hash in this
    // way:
    //
    // using a guid placeholder, define an out-of-line function *env-hash*.
    //
    // for each exported function, define a out-of-line function
    // *<fun>-hash* using a guid placeholder.
    //
    // Compile this program.
    //
    // Now each exported function's body has its final representation.
    // The function's final hash is the tree hash of
    //
    // (4 (1 . 2) (4 (4 (1 . 1) n) (4 (4 (1 . 1) (f @)) (4 (1 . 1) ()))))
    //
    // Where n is the path into the environment of the function.
    //
    // For each function, we retrieve its representation from the environment
    // and hash it, replacing the placeholder guid with a program that takes
    // the above wrapping with a sped-up treehash which replaces n in the
    // treehash with the function body's literal hash and 2 with an invocation
    // of *env-hash*.  We place this computation in *<fun>-hash*.
    //
    // Now, the last part is to find the path to *env-hash* and replace its
    // body with a tree hash coimputation that short circuits each left or
    // right branch, computing its own hash via sha256tree on its own
    // env reference.

    // XXX write this the simple way for now

    let mut function_list = program.exp.clone();
    let mut prog_output = SExp::Nil(loc.clone());

    for fun in exports.iter() {
        let fun_name =
            if let Export::Function(name) = fun {
                name.clone()
            } else {
                return Err(CompileErr(loc.clone(), "got program, wanted fun".to_string()));
            };

        let mut found_helper: Vec<Option<HelperForm>> = other_forms.iter().filter(|f| {
            f.name() == &fun_name && matches!(f, HelperForm::Defun(_, _))
        }).cloned().map(Some).collect();

        if found_helper.is_empty() {
            found_helper.push(None);
        }

        if let Some(HelperForm::Defun(_, dd)) = &found_helper[0] {
            let mut new_name = fun_name.clone();
            new_name.extend(b"_hash".to_vec());

            function_list = Rc::new(BodyForm::Call(
                loc.clone(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), b"c".to_vec()))),
                    Rc::new(BodyForm::Quoted(SExp::QuotedString(loc.clone(), b'"', fun_name.clone()))),
                    Rc::new(BodyForm::Call(
                        loc.clone(),
                        vec![
                            Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), b"c".to_vec()))),
                            Rc::new(BodyForm::Call(
                                loc.clone(),
                                vec![
                                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), new_name.clone())))
                                ],
                                None
                            )),
                            Rc::new(BodyForm::Call(
                                loc.clone(),
                                vec![
                                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), b"c".to_vec()))),
                                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), fun_name.clone()))),
                                    function_list
                                ],
                                None
                            ))
                        ],
                        None
                    )),
                ],
                None
            ));

            program.helpers.push(HelperForm::Defun(false, DefunData {
                loc: dd.loc.clone(),
                kw: None,
                nl: dd.nl.clone(),
                name: new_name,
                args: Rc::new(SExp::Nil(dd.loc.clone())),
                orig_args: Rc::new(SExp::Nil(dd.loc.clone())),
                body: Rc::new(BodyForm::Call(
                    dd.loc.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(dd.loc.clone(), b"__chia__sha256tree".to_vec()))),
                        Rc::new(BodyForm::Value(SExp::Atom(dd.loc.clone(), fun_name.clone()))),
                    ],
                    None
                )),
                synthetic: Some(SyntheticType::WantNonInline),
                ty: None,
            }));
        } else {
            return Err(CompileErr(
                loc.clone(),
                format!("exported function {} not found", decode_string(&fun_name))
            ));
        }
    }

    program.exp = function_list;
    program = resolve_namespaces(opts.clone(), &program)?;

    let compiled_result = Rc::new(compile_from_compileform(context, opts.clone(), program)?);
    let result_clvm = convert_to_clvm_rs(context.allocator(), compiled_result)?;
    let nil = context.allocator().null();
    let runner = context.runner();
    let run_result_clvm = runner.run_program(
        context.allocator(),
        result_clvm,
        nil,
        None
    ).map_err(|_| CompileErr(loc.clone(), "failed to run intermediate module program".to_string()))?;
    let run_result = convert_from_clvm_rs(
        context.allocator(),
        loc.clone(),
        run_result_clvm.1,
    )?;

    // Components to use for the CompileModuleOutput, which downstream can be
    // collected for namespacing.
    let mut components = vec![];
    let modules = break_down_module_output(loc.clone(), run_result)?;

    for m in modules.into_iter() {
        prog_output = SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc.clone(), m.name.clone())),
                Rc::new(SExp::QuotedString(loc.clone(), b'x', m.hash.clone()))
            )),
            Rc::new(prog_output)
        );

        let mut stream = Stream::new(None);
        let converted_func = convert_to_clvm_rs(
            context.allocator(),
            m.func.clone()
        )?;
        stream.write(sexp_as_bin(context.allocator(), converted_func));
        let output_path = create_hex_output_path(loc.clone(), &opts.filename(), &decode_string(&m.name))?;
        opts.write_new_file(&output_path, stream.get_value().hex().as_bytes())?;

        eprintln!("make output for {} dialect {:?} opt {} fe_opt {}", decode_string(&m.name), opts.dialect(), opts.optimize(), opts.frontend_opt());

        components.push(CompileModuleComponent {
            shortname: m.name.clone(),
            filename: output_path,
            content: m.func.clone(),
            hash: m.hash
        });
    }

    Ok(CompileModuleOutput {
        summary: Rc::new(prog_output),
        components
    })
}

pub enum CompilerOutput {
    Program(SExp),
    Module(Vec<CompileModuleComponent>, SExp)
}

impl CompilerOutput {
    pub fn to_sexp(&self) -> SExp {
        match self {
            CompilerOutput::Program(x) => x.clone(),
            CompilerOutput::Module(_, x) => x.clone(),
        }
    }

    pub fn loc(&self) -> Srcloc {
        match self {
            CompilerOutput::Program(x) => x.loc(),
            CompilerOutput::Module(_, x) => x.loc(),
        }
    }
}

pub fn compile_pre_forms(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>],
) -> Result<CompilerOutput, CompileErr> {
    let mut includes = Vec::new();
    let output = preprocess(opts.clone(), &mut includes, &pre_forms)?;

    if output.modules {
        let collected_forms = enlist(pre_forms[0].loc(), pre_forms);
        let mut allocator = Allocator::new();
        let classic_version = convert_to_clvm_rs(
            &mut allocator,
            Rc::new(collected_forms)
        )?;
        let dialect = detect_modern(&mut allocator, classic_version);
        let compiled = compile_module(
            context,
            opts.set_dialect(dialect),
            &includes,
            &output.forms
        )?;
        let borrowed_summary: &SExp = compiled.summary.borrow();
        return Ok(CompilerOutput::Module(
            compiled.components.clone(),
            borrowed_summary.clone()
        ));
    }

    let p0 = frontend(opts.clone(), pre_forms)?;
    let program = compile_from_compileform(context, opts, p0)?;
    Ok(CompilerOutput::Program(program))
}

pub fn compile_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    content: &str,
    symbol_table: &mut HashMap<String, String>,
) -> Result<CompilerOutput, CompileErr> {
    let srcloc = Srcloc::start(&opts.filename());
    let pre_forms = parse_sexp(srcloc.clone(), content.bytes())?;

    let mut context_wrapper = CompileContextWrapper::new(
        allocator,
        runner,
        symbol_table,
        get_optimizer(&srcloc, opts.clone())?,
    );

    compile_pre_forms(&mut context_wrapper.context, opts, &pre_forms)
}

impl CompilerOpts for DefaultCompilerOpts {
    fn filename(&self) -> String {
        self.filename.clone()
    }
    fn code_generator(&self) -> Option<PrimaryCodegen> {
        self.code_generator.clone()
    }
    fn dialect(&self) -> AcceptedDialect {
        self.dialect.clone()
    }
    fn in_defun(&self) -> bool {
        self.in_defun
    }
    fn stdenv(&self) -> bool {
        self.stdenv
    }
    fn optimize(&self) -> bool {
        self.optimize
    }
    fn frontend_opt(&self) -> bool {
        self.frontend_opt
    }
    fn frontend_check_live(&self) -> bool {
        self.frontend_check_live
    }
    fn start_env(&self) -> Option<Rc<SExp>> {
        self.start_env.clone()
    }
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
        self.prim_map.clone()
    }
    fn disassembly_ver(&self) -> Option<usize> {
        self.disassembly_ver
    }
    fn get_search_paths(&self) -> Vec<String> {
        self.include_dirs.clone()
    }

    fn set_dialect(&self, dialect: AcceptedDialect) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.dialect = dialect;
        Rc::new(copy)
    }
    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.include_dirs = dirs.to_owned();
        Rc::new(copy)
    }
    fn set_disassembly_ver(&self, ver: Option<usize>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.disassembly_ver = ver;
        Rc::new(copy)
    }
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.in_defun = new_in_defun;
        Rc::new(copy)
    }
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.stdenv = new_stdenv;
        Rc::new(copy)
    }
    fn set_optimize(&self, optimize: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.optimize = optimize;
        Rc::new(copy)
    }
    fn set_frontend_opt(&self, optimize: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.frontend_opt = optimize;
        Rc::new(copy)
    }
    fn set_frontend_check_live(&self, check: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.frontend_check_live = check;
        Rc::new(copy)
    }
    fn set_code_generator(&self, new_code_generator: PrimaryCodegen) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.code_generator = Some(new_code_generator);
        Rc::new(copy)
    }
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.start_env = start_env;
        Rc::new(copy)
    }
    fn set_prim_map(&self, prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.prim_map = prims;
        Rc::new(copy)
    }

    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, Vec<u8>), CompileErr> {
        if filename == "*macros*" {
            if self.dialect().strict {
                return Ok((filename, ADVANCED_MACROS.bytes().collect()));
            } else {
                return Ok((filename, STANDARD_MACROS.bytes().collect()));
            }
        } else if let Some(dialect) = KNOWN_DIALECTS.get(&filename) {
            return Ok((filename, dialect.content.bytes().collect()));
        }

        for dir in self.include_dirs.iter() {
            let mut p = PathBuf::from(dir);
            p.push(filename.clone());
            match fs::read(p.clone()) {
                Err(_e) => {
                    continue;
                }
                Ok(content) => {
                    return Ok((
                        p.to_str().map(|x| x.to_owned()).unwrap_or_else(|| filename),
                        content,
                    ));
                }
            }
        }
        Err(CompileErr(
            Srcloc::start(&inc_from),
            format!("could not find {filename} to include"),
        ))
    }

    fn write_new_file(
        &self,
        target: &str,
        content: &[u8]
    ) -> Result<(), CompileErr> {
        fs::write(target, content).map_err(|_| {
            CompileErr(
                Srcloc::start(&self.filename()),
                format!("could not write output file {} for {}", target, self.filename())
            )
        })?;
        Ok(())
    }

    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr> {
        let me = Rc::new(self.clone());
        let mut context_wrapper = CompileContextWrapper::new(
            allocator,
            runner,
            symbol_table,
            get_optimizer(&sexp.loc(), me.clone())?,
        );
        compile_pre_forms(&mut context_wrapper.context, me, &[sexp]).map(|x| x.to_sexp())
    }
}

impl DefaultCompilerOpts {
    pub fn new(filename: &str) -> DefaultCompilerOpts {
        DefaultCompilerOpts {
            include_dirs: vec![".".to_string()],
            filename: filename.to_string(),
            code_generator: None,
            in_defun: false,
            stdenv: true,
            optimize: false,
            frontend_opt: false,
            frontend_check_live: true,
            start_env: None,
            dialect: AcceptedDialect::default(),
            prim_map: create_prim_map(),
            disassembly_ver: None,
        }
    }
}

fn path_to_function_inner(
    program: Rc<SExp>,
    hash: &[u8],
    path_mask: Number,
    current_path: Number,
) -> Option<Number> {
    let nextpath = path_mask.clone() * 2_i32.to_bigint().unwrap();
    match program.borrow() {
        SExp::Cons(_, a, b) => {
            path_to_function_inner(a.clone(), hash, nextpath.clone(), current_path.clone())
                .map(Some)
                .unwrap_or_else(|| {
                    path_to_function_inner(
                        b.clone(),
                        hash,
                        nextpath.clone(),
                        current_path.clone() + path_mask.clone(),
                    )
                    .map(Some)
                    .unwrap_or_else(|| {
                        let current_hash = sha256tree(program.clone());
                        if current_hash == hash {
                            Some(current_path + path_mask)
                        } else {
                            None
                        }
                    })
                })
        }
        _ => {
            let current_hash = sha256tree(program.clone());
            if current_hash == hash {
                Some(current_path + path_mask)
            } else {
                None
            }
        }
    }
}

pub fn path_to_function(program: Rc<SExp>, hash: &[u8]) -> Option<Number> {
    path_to_function_inner(program, hash, bi_one(), bi_zero())
}

fn op2(op: u32, code: Rc<SExp>, env: Rc<SExp>) -> Rc<SExp> {
    Rc::new(SExp::Cons(
        code.loc(),
        Rc::new(SExp::Integer(env.loc(), op.to_bigint().unwrap())),
        Rc::new(SExp::Cons(
            code.loc(),
            code.clone(),
            Rc::new(SExp::Cons(
                env.loc(),
                env.clone(),
                Rc::new(SExp::Nil(code.loc())),
            )),
        )),
    ))
}

fn quoted(env: Rc<SExp>) -> Rc<SExp> {
    Rc::new(SExp::Cons(
        env.loc(),
        Rc::new(SExp::Integer(env.loc(), bi_one())),
        env.clone(),
    ))
}

fn apply(code: Rc<SExp>, env: Rc<SExp>) -> Rc<SExp> {
    op2(2, code, env)
}

fn cons(f: Rc<SExp>, r: Rc<SExp>) -> Rc<SExp> {
    op2(4, f, r)
}

// compose (a (a path env) (c env 1))
pub fn rewrite_in_program(path: Number, env: Rc<SExp>) -> Rc<SExp> {
    apply(
        apply(
            // Env comes quoted, so divide by 2
            quoted(Rc::new(SExp::Integer(env.loc(), path / 2))),
            env.clone(),
        ),
        cons(env.clone(), Rc::new(SExp::Integer(env.loc(), bi_one()))),
    )
}

pub fn is_operator(op: u32, atom: &SExp) -> bool {
    match atom.to_bigint() {
        Some(n) => n == op.to_bigint().unwrap(),
        None => false,
    }
}

pub fn is_whole_env(atom: &SExp) -> bool {
    is_operator(1, atom)
}
pub fn is_apply(atom: &SExp) -> bool {
    is_operator(2, atom)
}
pub fn is_cons(atom: &SExp) -> bool {
    is_operator(4, atom)
}

// Extracts the environment from a clvm program that contains one.
// The usual form of a program to analyze is:
// (2 main (4 env 1))
pub fn extract_program_and_env(program: Rc<SExp>) -> Option<(Rc<SExp>, Rc<SExp>)> {
    // Most programs have apply as a toplevel form.  If we don't then it's
    // a form we don't understand.
    match program.proper_list() {
        Some(lst) => {
            if lst.len() != 3 {
                return None;
            }

            match (is_apply(&lst[0]), &lst[1], lst[2].proper_list()) {
                (true, real_program, Some(cexp)) => {
                    if cexp.len() != 3 || !is_cons(&cexp[0]) || !is_whole_env(&cexp[2]) {
                        None
                    } else {
                        Some((Rc::new(real_program.clone()), Rc::new(cexp[1].clone())))
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn is_at_capture(head: Rc<SExp>, rest: Rc<SExp>) -> Option<(Vec<u8>, Rc<SExp>)> {
    rest.proper_list().and_then(|l| {
        if l.len() != 2 {
            return None;
        }
        if let (SExp::Atom(_, a), SExp::Atom(_, cap)) = (head.borrow(), &l[0]) {
            if a == &vec![b'@'] {
                return Some((cap.clone(), Rc::new(l[1].clone())));
            }
        }

        None
    })
}
