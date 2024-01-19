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

use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs, run, sha256tree};
use crate::compiler::codegen::{
    codegen, hoist_body_let_binding, process_helper_let_bindings, CONST_EVAL_LIMIT,
};
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompileModuleComponent, CompileModuleOutput, CompilerOpts,
    CompilerOutput, ConstantKind, DefconstData, DefunData, Export, FrontendOutput, HelperForm,
    ImportLongName, IncludeDesc, PrimaryCodegen, SyntheticType,
};
use crate::compiler::dialect::{AcceptedDialect, KNOWN_DIALECTS};
use crate::compiler::frontend::frontend;
use crate::compiler::optimize::get_optimizer;
use crate::compiler::prims;
use crate::compiler::resolve::{find_helper_target, resolve_namespaces};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, parse_sexp, SExp};
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

struct ModuleOutputEntry {
    name: Vec<u8>,
    hash: Vec<u8>,
    func: Rc<SExp>,
}

fn break_down_module_output(
    loc: Srcloc,
    run_result: Rc<SExp>,
) -> Result<Vec<ModuleOutputEntry>, CompileErr> {
    let list_data = if let Some(lst) = run_result.proper_list() {
        lst
    } else {
        return Err(CompileErr(
            loc,
            "output from intermediate module program should have been a proper list".to_string(),
        ));
    };

    if list_data.len() % 2 != 0 {
        return Err(CompileErr(
            loc,
            "output length from intermediate module program should have been divisible by 2"
                .to_string(),
        ));
    }

    let mut result = Vec::new();
    for tuple_idx in 0..(list_data.len() / 2) {
        let i = tuple_idx * 2;
        if let SExp::Atom(_, name) = list_data[i].atomize() {
            result.push(ModuleOutputEntry {
                name: name.clone(),
                hash: sha256tree(Rc::new(list_data[i + 1].clone())),
                func: Rc::new(list_data[i + 1].clone()),
            });
        } else {
            return Err(CompileErr(loc.clone(), format!("output from intermediate module program wasn't in triplets of atom, atom, program {} {} {}", list_data[i], list_data[i+1], list_data[i+2])));
        }
    }

    Ok(result)
}

fn create_hex_output_path(loc: Srcloc, file_path: &str, func: &str) -> Result<String, CompileErr> {
    let mut dir = PathBuf::from(file_path);
    let filename = PathBuf::from(file_path)
        .with_extension("")
        .file_name()
        .map(|f| f.to_string_lossy().to_string())
        .unwrap_or_else(|| "program".to_string());
    dir.pop();
    let func_dot_hex_list = &[func.to_string(), "hex".to_string()];
    let func_dot_hex = func_dot_hex_list.join(".");
    let name_with_func_list = &[filename.to_string(), func_dot_hex];
    dir.push(name_with_func_list.join("_"));
    dir.into_os_string().into_string().map_err(|_| {
        CompileErr(
            loc,
            format!("could not make os file path for output {func}"),
        )
    })
}

pub fn find_exported_helper(
    opts: Rc<dyn CompilerOpts>,
    program: &CompileForm,
    fun_name: &[u8],
) -> Result<Option<HelperForm>, CompileErr> {
    let (_, parsed_name) = ImportLongName::parse(fun_name);
    Ok(find_helper_target(
        opts.clone(),
        &program.helpers,
        None,
        fun_name,
        &parsed_name
    )?.map(|(_,result)| result.clone()))
}

fn form_hash_expression(inner_exp: Rc<BodyForm>) -> Rc<BodyForm> {
    Rc::new(BodyForm::Call(
        inner_exp.loc(),
        vec![
            Rc::new(BodyForm::Value(SExp::Atom(
                inner_exp.loc(),
                b"__chia__sha256tree".to_vec(),
            ))),
            inner_exp,
        ],
        None,
    ))
}

fn get_hash_of_constant(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    name: &[u8],
    program: &CompileForm,
    dc: &DefconstData,
) -> Result<Vec<u8>, CompileErr> {
    let constant_program = CompileForm {
        exp: dc.body.clone(),
        ..program.clone()
    };
    let compiled = compile_from_compileform(context, opts.clone(), constant_program)?;
    let runner = context.runner();
    let evaluated = run(
        context.allocator(),
        runner,
        opts.prim_map(),
        Rc::new(compiled),
        Rc::new(SExp::Nil(program.loc())),
        None,
        Some(CONST_EVAL_LIMIT),
    )
    .map_err(|r| match r {
        RunFailure::RunExn(l, e) => CompileErr(
            l.clone(),
            format!(
                "Error evaluating export constant {}: exception throwing {e}",
                decode_string(name)
            ),
        ),
        RunFailure::RunErr(l, e) => CompileErr(
            l.clone(),
            format!(
                "Error evaluating export constant {}: {e}",
                decode_string(name)
            ),
        ),
    })?;
    Ok(sha256tree(evaluated))
}

/// Exports are returned main programs:
///
/// Single main
///
/// (export (X) (do-stuff X))
///
/// Multiple mains
///
/// (export foo)
/// (export bar)
pub fn compile_module(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    mut program: CompileForm,
    exports: &[Export],
) -> Result<CompileModuleOutput, CompileErr> {
    let loc = program.loc();
    let opts = opts.set_optimize(true);

    if exports.is_empty() {
        return Err(CompileErr(
            loc.clone(),
            "A chialisp module should have at least one export".to_string(),
        ));
    }

    eprintln!("process exports from {}", program.to_sexp());

    if exports.len() == 1 {
        if let Export::MainProgram(args, expr) = &exports[0] {
            // Single program.
            program.args = args.clone();
            program.exp = expr.clone();

            program = resolve_namespaces(opts.clone(), &program)?;

            let output = Rc::new(compile_from_compileform(context, opts.clone(), program)?);
            let converted = convert_to_clvm_rs(context.allocator(), output.clone())?;

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
                    hash: sha256tree(output),
                }],
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
        let (fun_name, export_name) = if let Export::Function(name, as_name) = fun {
            (name.clone(), as_name.as_ref().map(|c| c.clone()).unwrap_or_else(|| name.to_vec()))
        } else {
            return Err(CompileErr(
                loc.clone(),
                "got program, wanted fun".to_string(),
            ));
        };

        let append_to_function_list = |function_list: &mut Rc<BodyForm>, fun_name: &[u8], export_name: &[u8]| {
            *function_list = Rc::new(BodyForm::Call(
                loc.clone(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Integer(
                        loc.clone(),
                        4_u32.to_bigint().unwrap(),
                    ))),
                    Rc::new(BodyForm::Quoted(SExp::QuotedString(
                        loc.clone(),
                        b'"',
                        export_name.to_vec(),
                    ))),
                    Rc::new(BodyForm::Call(
                        loc.clone(),
                        vec![
                            Rc::new(BodyForm::Value(SExp::Integer(
                                loc.clone(),
                                4_u32.to_bigint().unwrap(),
                            ))),
                            Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), fun_name.to_vec()))),
                            function_list.clone(),
                        ],
                        None,
                    )),
                ],
                None,
            ));
        };

        let exported = find_exported_helper(opts.clone(), &program, &fun_name)?;
        if let Some(HelperForm::Defun(_, dd)) = &exported {
            let mut new_name = fun_name.clone();
            new_name.extend(b"_hash".to_vec());

            append_to_function_list(&mut function_list, &fun_name, &export_name);
            let make_hash_of = Rc::new(BodyForm::Value(SExp::Atom(
                dd.loc.clone(),
                fun_name.clone(),
            )));
            program.helpers.push(HelperForm::Defun(
                false,
                DefunData {
                    loc: dd.loc.clone(),
                    kw: None,
                    nl: dd.nl.clone(),
                    name: new_name,
                    args: Rc::new(SExp::Nil(dd.loc.clone())),
                    orig_args: Rc::new(SExp::Nil(dd.loc.clone())),
                    body: form_hash_expression(make_hash_of),
                    synthetic: Some(SyntheticType::WantNonInline),
                    ty: None,
                },
            ));
        } else if let Some(HelperForm::Defconstant(dc)) = &exported {
            let mut new_name = fun_name.clone();
            new_name.extend(b"_hash".to_vec());
            let hash_of_constant =
                get_hash_of_constant(context, opts.clone(), &dc.name, &program, dc)?;

            let mut underscore_name = new_name.clone();
            underscore_name.insert(0, b'_');

            append_to_function_list(&mut function_list, &fun_name, &export_name);

            program.helpers.push(HelperForm::Defconstant(DefconstData {
                kind: ConstantKind::Complex,
                name: underscore_name.clone(),
                body: Rc::new(BodyForm::Quoted(SExp::Atom(
                    dc.loc.clone(),
                    hash_of_constant,
                ))),
                tabled: true,
                ty: None,
                ..dc.clone()
            }));

            program.helpers.push(HelperForm::Defun(
                true,
                DefunData {
                    loc: dc.loc.clone(),
                    nl: dc.nl.clone(),
                    kw: None,
                    name: new_name.clone(),
                    args: Rc::new(SExp::Nil(dc.loc.clone())),
                    orig_args: Rc::new(SExp::Nil(dc.loc.clone())),
                    body: Rc::new(BodyForm::Value(SExp::Atom(dc.loc.clone(), new_name))),
                    synthetic: Some(SyntheticType::NoInlinePreference),
                    ty: None,
                },
            ));
        } else {
            return Err(CompileErr(
                loc.clone(),
                format!("exported function {} not found", decode_string(&fun_name)),
            ));
        }
    }

    program.exp = function_list;
    program = resolve_namespaces(opts.clone(), &program)?;

    let compiled_result = Rc::new(compile_from_compileform(context, opts.clone(), program)?);
    let result_clvm = convert_to_clvm_rs(context.allocator(), compiled_result)?;
    let nil = context.allocator().null();
    let runner = context.runner();
    let run_result_clvm = runner
        .run_program(context.allocator(), result_clvm, nil, None)
        .map_err(|_| {
            CompileErr(
                loc.clone(),
                "failed to run intermediate module program".to_string(),
            )
        })?;
    let run_result = convert_from_clvm_rs(context.allocator(), loc.clone(), run_result_clvm.1)?;

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
                Rc::new(SExp::QuotedString(loc.clone(), b'x', m.hash.clone())),
            )),
            Rc::new(prog_output),
        );

        eprintln!("prog_output {prog_output}");

        let mut stream = Stream::new(None);
        let converted_func = convert_to_clvm_rs(context.allocator(), m.func.clone())?;
        stream.write(sexp_as_bin(context.allocator(), converted_func));
        let output_path =
            create_hex_output_path(loc.clone(), &opts.filename(), &decode_string(&m.name))?;
        eprintln!("output_path {output_path}");
        opts.write_new_file(&output_path, stream.get_value().hex().as_bytes())?;

        components.push(CompileModuleComponent {
            shortname: m.name.clone(),
            filename: output_path,
            content: m.func.clone(),
            hash: m.hash,
        });
    }

    Ok(CompileModuleOutput {
        summary: Rc::new(prog_output),
        components,
    })
}

pub fn compile_pre_forms(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>],
) -> Result<CompilerOutput, CompileErr> {
    let p0 = frontend(opts.clone(), pre_forms)?;

    match p0 {
        FrontendOutput::CompileForm(p0) => Ok(CompilerOutput::Program(compile_from_compileform(
            context, opts, p0,
        )?)),
        FrontendOutput::Module(cf, exports) => {
            // cl23 always reflects optimization.
            let dialect = opts.dialect();
            let opts = if let Some(stepping) = dialect.stepping.as_ref() {
                opts.set_optimize(*stepping > 21)
            } else {
                opts
            };

            Ok(CompilerOutput::Module(compile_module(
                context, opts, cf, &exports,
            )?))
        }
    }
}

pub fn compile_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    content: &str,
    symbol_table: &mut HashMap<String, String>,
    includes: &mut Vec<IncludeDesc>,
) -> Result<CompilerOutput, CompileErr> {
    let srcloc = Srcloc::start(&opts.filename());
    let pre_forms = parse_sexp(srcloc.clone(), content.bytes())?;
    let mut context_wrapper = CompileContextWrapper::new(
        allocator,
        runner,
        symbol_table,
        get_optimizer(&srcloc, opts.clone())?,
        includes,
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

    fn write_new_file(&self, target: &str, content: &[u8]) -> Result<(), CompileErr> {
        fs::write(target, content).map_err(|_| {
            CompileErr(
                Srcloc::start(&self.filename()),
                format!(
                    "could not write output file {} for {}",
                    target,
                    self.filename()
                ),
            )
        })?;
        Ok(())
    }

    fn compile_program(
        &self,
        context: &mut BasicCompileContext,
        sexp: Rc<SExp>,
    ) -> Result<CompilerOutput, CompileErr> {
        let me = Rc::new(self.clone());
        compile_pre_forms(context, me, &[sexp])
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
