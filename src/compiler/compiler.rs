use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::UNIX_EPOCH;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero, Stream};
use crate::classic::clvm::sexp::sexp_as_bin;
use crate::classic::clvm_tools::binutils::disassemble;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::cldb::hex_to_modern_sexp;
use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs, run, sha256tree};
use crate::compiler::codegen::{
    codegen, hoist_body_let_binding, process_helper_let_bindings};
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompileModuleComponent, CompileModuleOutput, CompilerOpts,
    CompilerOutput, ConstantKind, DefconstData, DefunData, Export, FrontendOutput, HelperForm,
    ImportLongName, IncludeDesc, ModulePhase, PrimaryCodegen, SyntheticType,
};
use crate::compiler::dialect::{AcceptedDialect, KNOWN_DIALECTS};
use crate::compiler::frontend::frontend;
use crate::compiler::optimize::depgraph::{FunctionDependencyGraph, DepgraphOptions};
use crate::compiler::optimize::get_optimizer;
use crate::compiler::prims;
use crate::compiler::resolve::{find_helper_target, resolve_namespaces};
use crate::compiler::sexp::{decode_string, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::{BasicCompileContext, CompileContextWrapper};
use crate::util::Number;

pub const SHA256TREE_PROGRAM_CLVM: &'static str = "(2 (1 2 (3 (7 5) (1 11 (1 . 2) (2 2 (4 2 (4 9 ()))) (2 2 (4 2 (4 13 ())))) (1 11 (1 . 1) 5)) 1) (4 (1 2 (3 (7 5) (1 11 (1 . 2) (2 2 (4 2 (4 9 ()))) (2 2 (4 2 (4 13 ())))) (1 11 (1 . 1) 5)) 1) 1))";


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
    pub module_phase: Option<ModulePhase>,
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
    Ok(
        find_helper_target(opts.clone(), &program.helpers, None, fun_name, &parsed_name)?
            .map(|(_, result)| result.clone()),
    )
}

fn form_hash_expression(inner_exp: Rc<BodyForm>) -> Rc<BodyForm> {
    let shloc = Srcloc::start("*sha256tree*");
    let parsed =
        parse_sexp(shloc.clone(), SHA256TREE_PROGRAM_CLVM.bytes()).expect("should have parsed");
    let p0_borrowed: &SExp = parsed[0].borrow();

    Rc::new(BodyForm::Call(
        inner_exp.loc(),
        vec![
            Rc::new(BodyForm::Value(SExp::Integer(
                inner_exp.loc(),
                2_u32.to_bigint().unwrap(),
            ))),
            Rc::new(BodyForm::Quoted(p0_borrowed.clone())),
            Rc::new(BodyForm::Call(
                inner_exp.loc(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Integer(
                        inner_exp.loc(),
                        4_u32.to_bigint().unwrap(),
                    ))),
                    inner_exp.clone(),
                    Rc::new(BodyForm::Quoted(SExp::Nil(inner_exp.loc()))),
                ],
                None,
            )),
        ],
        None,
    ))
}

fn modernize_constants(helpers: &mut [HelperForm], standalone_constants: &HashSet<Vec<u8>>) {
    for h in helpers.iter_mut() {
        match h {
            HelperForm::Defconstant(d) => {
                // Ensure that we upgrade the constant type.
                if standalone_constants.contains(&d.name) {
                    d.kind = ConstantKind::Module(false);
                    d.tabled = false;
                }
            }
            HelperForm::Defnamespace(ns) => {
                modernize_constants(&mut ns.helpers, standalone_constants);
            }
            _ => {}
        }
    }
}

fn capture_standalone_constants(
    standalone_constants: &mut HashSet<Vec<u8>>,
    depgraph: &FunctionDependencyGraph,
    helpers: &[HelperForm],
    exports: &[Export],
) {
    // Find constants on which nothing depends (they're only output).
    for h in helpers.iter() {
        let mut constant_is_depended = HashSet::new();
        if let HelperForm::Defconstant(dc) = h {
            let match_exports = exports.iter().any(|e| match e {
                Export::MainProgram(_, _) => false,
                Export::Function(name, _) => name == h.name()
            });

            // It isn't exported so it isn't standalone.
            if !match_exports {
                continue;
            }

            depgraph.get_full_depended_on_by(&mut constant_is_depended, h.name());
            let depended_list: Vec<String> = constant_is_depended.iter().map(|d| decode_string(d)).collect();
            if constant_is_depended.is_empty() {
                standalone_constants.insert(h.name().to_vec());
            }
        } else if let HelperForm::Defnamespace(ns) = h {
            capture_standalone_constants(
                standalone_constants,
                depgraph,
                &ns.helpers,
                exports,
            )
        }
    }
}

fn form_module_program_common_body(
    standalone_constants: &HashSet<Vec<u8>>,
    mut program: CompileForm,
    exports: &[Export]
) -> Result<CompileForm, CompileErr> {
    program.helpers = program.helpers.iter().filter(|h| {
        !standalone_constants.contains(h.name())
    }).cloned().collect();

    // The body should contain anything that is in the exports but not standalone
    // constants.
    let mut body = Rc::new(BodyForm::Quoted(SExp::Nil(program.loc())));

    // Ensure that __chia__extras gets injected.
    program.helpers.push(HelperForm::Defconstant(DefconstData {
        loc: program.loc.clone(),
        kw: None,
        name: b"__chia__extras".to_vec(),
        nl: program.loc.clone(),
        body: body.clone(),
        kind: ConstantKind::Simple,
        tabled: false,
        ty: None,
    }));

    let cons = Rc::new(BodyForm::Value(SExp::Integer(program.loc(), 4_u32.to_bigint().unwrap())));

    let add_export = |body: &mut Rc<BodyForm>, e: &[u8]| {
        *body = Rc::new(BodyForm::Call(
            program.loc(),
            vec![
                cons.clone(),
                Rc::new(BodyForm::Call(
                    program.loc(),
                    vec![
                        cons.clone(),
                        Rc::new(BodyForm::Value(SExp::QuotedString(program.loc(), b'"', e.to_vec()))),
                        Rc::new(BodyForm::Value(SExp::Atom(program.loc(), e.to_vec()))),
                    ],
                    None
                )),
                body.clone(),
            ],
            None
        ));
    };

    for e in exports.iter().filter_map(|e| {
        if let Export::Function(name, _) = e {
            if !standalone_constants.contains(name) {
                return Some(name);
            }
        }

        None
    }) {
        add_export(&mut body, e);
    }

    add_export(&mut body, b"__chia__extras");

    Ok(program)
}

fn populate_export_map(
    context: &mut BasicCompileContext,
    export_map: &mut BTreeMap<Vec<u8>, Rc<SExp>>,
    opts: Rc<dyn CompilerOpts>,
    code: Rc<SExp>
) -> Result<(), CompileErr> {
    let runner = context.runner.clone();
    let mut result = run(
        context.allocator(),
        runner,
        opts.prim_map(),
        code.clone(),
        Rc::new(SExp::Nil(code.loc())),
        None,
        None
    )?;

    while let SExp::Cons(_, first, rest) = result.borrow() {
        if let SExp::Cons(_, name, value) = first.borrow() {
            if let SExp::Atom(_, name) = name.atomize().borrow() {
                export_map.insert(name.clone(), value.clone());
                result = rest.clone();
                continue;
            }
        };

        todo!();
    }

    Ok(())
}

/*
        if let Some(HelperForm::Defun(_, dd)) = &exported {
            let mut new_name = fun_name.clone();
            new_name.extend(b"_hash".to_vec());

            append_to_function_list(&mut function_list, &fun_name, &export_name);
            let make_hash_of = Rc::new(BodyForm::Value(SExp::Atom(
                dd.loc.clone(),
                fun_name.clone(),
            )));
            program.helpers.push(HelperForm::Defun(
                true,
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
            let make_hash_of = Rc::new(BodyForm::Value(SExp::Atom(
                dc.loc.clone(),
                fun_name.clone(),
            )));

            let mut underscore_name = new_name.clone();
            underscore_name.insert(0, b'_');

            append_to_function_list(&mut function_list, &fun_name, &export_name);

            program.helpers.push(HelperForm::Defconstant(DefconstData {
                kind: ConstantKind::Module(true),
                name: underscore_name.clone(),
                body: form_hash_expression(make_hash_of),
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
                    body: Rc::new(BodyForm::Value(SExp::Atom(dc.loc.clone(), underscore_name))),
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
*/

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
    mut opts: Rc<dyn CompilerOpts>,
    standalone_constants: &HashSet<Vec<u8>>,
    mut program: CompileForm,
    exports: &[Export],
) -> Result<CompileModuleOutput, CompileErr> {
    let loc = program.loc();
    opts = opts.set_optimize(true);

    if exports.is_empty() {
        return Err(CompileErr(
            loc.clone(),
            "A chialisp module should have at least one export".to_string(),
        ));
    }

    if exports.len() == 1 {
        if let Export::MainProgram(args, expr) = &exports[0] {
            // Single program.
            program.args = args.clone();
            program.exp = expr.clone();

            program = resolve_namespaces(opts.clone(), &program)?;

            let output = Rc::new(compile_from_compileform(context, opts.clone(), program.clone())?);
            let converted = convert_to_clvm_rs(context.allocator(), output.clone())?;

            let mut output_path = PathBuf::from(&opts.filename());
            output_path.set_extension("hex");
            let output_path_str = output_path.into_os_string().to_string_lossy().to_string();
            let mut stream = Stream::new(None);
            stream.write(sexp_as_bin(context.allocator(), converted));
            opts.write_new_file(&output_path_str, stream.get_value().hex().as_bytes())?;
            return Ok(CompileModuleOutput {
                summary: Rc::new(SExp::Nil(loc.clone())),
                includes: program.include_forms.clone(),
                components: vec![CompileModuleComponent {
                    shortname: b"program".to_vec(),
                    filename: output_path_str,
                    content: output.clone(),
                    hash: sha256tree(output),
                }],
            });
        }
    }

    // First pass compilation: remove standalone constant helpers and produce
    // a body which contains all the non-standalone exports.
    let common_opts = opts.set_module_phase(Some(ModulePhase::CommonPhase));
    let common_program = form_module_program_common_body(
        &standalone_constants,
        program.clone(),
        exports
    )?;
    eprintln!("common program {}", common_program.to_sexp());
    let common_output = compile_from_compileform(
        context,
        common_opts,
        common_program.clone()
    )?;
    eprintln!("common_output {}", common_output);

    let mut captured_export_map: BTreeMap<Vec<u8>, Rc<SExp>> = BTreeMap::new();
    // Capture exports that are members of the common set.
    // We get a triple of output: (env_shape env code)
    let (env_shape, env, code) = (|| {
        if let Some(lst) = common_output.proper_list() {
            if lst.len() == 3 {
                return (Rc::new(lst[0].clone()), Rc::new(lst[1].clone()), Rc::new(lst[2].clone()));
            }
        }

        todo!();
    })();

    populate_export_map(
        context,
        &mut captured_export_map,
        opts.clone(),
        code
    )?;

    let keys_strings: Vec<String> = captured_export_map.keys().map(|k| decode_string(k)).collect();
    eprintln!("have common export keys {keys_strings:?}");

    // Second pass compilation: for each export in standalone constants
    let second_stage_opts = opts.set_module_phase(Some(ModulePhase::StandalonePhase(env_shape, env)));
    for fun in exports.iter() {
        let (fun_name, export_name) = if let Export::Function(name, as_name) = fun {
            // We've already processed non-standalone (common) constants in the
            // common environment, so skip those.
            if captured_export_map.contains_key(name) {
                continue;
            }

            // Otherwise, capture it to produce to the output.
            (
                name.clone(),
                as_name.as_ref().cloned().unwrap_or_else(|| name.to_vec()),
            )
        } else {
            return Err(CompileErr(
                loc.clone(),
                "got program, wanted fun".to_string(),
            ));
        };

        let second_stage_program =
            match find_exported_helper(opts.clone(), &program, &fun_name)? {
                Some(HelperForm::Defun(_, dd)) => {
                    // Second stage program is the function applied to the env.
                    CompileForm {
                        exp: Rc::new(BodyForm::Value(SExp::Atom(dd.loc.clone(), fun_name.to_vec()))),
                        .. common_program.clone()
                    }
                }
                Some(HelperForm::Defconstant(dc)) => {
                    // Second stage program generates the constant.
                    CompileForm {
                        exp: dc.body.clone(),
                        .. common_program.clone()
                    }
                }
                _ => {
                    todo!();
                }
            };

        let compiled_result = Rc::new(compile_from_compileform(
            context,
            second_stage_opts.clone(),
            second_stage_program
        )?);

        eprintln!("export_output {compiled_result}");

        let result_clvm = convert_to_clvm_rs(context.allocator(), compiled_result)?;
        let nil = context.allocator().null();
        let runner = context.runner();
        let run_result_clvm = runner
            .run_program(context.allocator(), result_clvm, nil, None)
            .map_err(|e| {
                let dis = disassemble(context.allocator(), e.0, None);
                CompileErr(
                    loc.clone(),
                    "failed to run intermediate module program".to_string(),
                )
            })?;
        let run_result = convert_from_clvm_rs(context.allocator(), loc.clone(), run_result_clvm.1)?;
        captured_export_map.insert(export_name.clone(), run_result);
    }

    // Components to use for the CompileModuleOutput, which downstream can be
    // collected for namespacing.
    let mut components = vec![];
    let mut prog_output = SExp::Nil(program.loc());

    for (export_name, export_value) in captured_export_map.iter() {
        let output_path =
            create_hex_output_path(loc.clone(), &opts.filename(), &decode_string(&export_name))?;

        let m = CompileModuleComponent {
            shortname: export_name.to_vec(),
            filename: output_path.clone(),
            content: export_value.clone(),
            hash: sha256tree(export_value.clone()),
        };

        prog_output = SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc.clone(), m.shortname.clone())),
                Rc::new(SExp::QuotedString(loc.clone(), b'x', m.hash.clone())),
            )),
            Rc::new(prog_output),
        );

        let mut stream = Stream::new(None);
        let converted_func = convert_to_clvm_rs(context.allocator(), m.content.clone())?;
        stream.write(sexp_as_bin(context.allocator(), converted_func));
        opts.write_new_file(&output_path, stream.get_value().hex().as_bytes())?;

        components.push(m);
    }

    Ok(CompileModuleOutput {
        summary: Rc::new(prog_output),
        includes: program.include_forms.clone(),
        components,
    })
}

fn get_hex_name_of_export(
    opts: Rc<dyn CompilerOpts>,
    loc: &Srcloc,
    export: &Export
) -> Result<String, CompileErr> {
    match export {
        Export::MainProgram(_, _) => {
            let mut output_path = PathBuf::from(&opts.filename());
            output_path.set_extension("hex");
            Ok(output_path.into_os_string().to_string_lossy().to_string())
        }
        Export::Function(name, as_name) => {
            let use_name = decode_string(as_name.as_ref().unwrap_or_else(|| &name));
            create_hex_output_path(loc.clone(), &opts.filename(), &use_name)
        }
    }
}

fn determine_hex_file_names(
    opts: Rc<dyn CompilerOpts>,
    loc: &Srcloc,
    exports: &[Export]
) -> Result<Vec<String>, CompileErr> {
    let mut result = Vec::new();
    for e in exports.iter() {
        result.push(get_hex_name_of_export(opts.clone(), loc, e)?);
    }
    Ok(result)
}

pub fn try_to_use_existing_hex_outputs(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    cf: &CompileForm,
    exports: &[Export]
) -> Result<Option<CompilerOutput>, CompileErr> {
    let mut imports: Vec<String> = cf.include_forms.iter().map(|i| decode_string(&i.name)).collect();
    imports.push(opts.filename());

    // Get earliest date of any hex file.
    let hex_files = determine_hex_file_names(opts.clone(), &cf.loc, exports)?;
    let mut earliest_hex_date: Option<u64> = None;
    for file in hex_files.iter() {
        if let Ok(mod_date) = opts.get_file_mod_date(&cf.loc, &file) {
            let should_set =
                if let Some(hex_date) = earliest_hex_date.as_ref() {
                    *hex_date > mod_date
                } else {
                    true
                };

            if should_set {
                earliest_hex_date = Some(mod_date);
            }
        } else {
            // One of them doesn't exist so we must build.
            break;
        }
    }

    let mut latest_file_date: Option<u64> = None;
    for file in imports.iter() {
        if let Ok(mod_date) = opts.get_file_mod_date(&cf.loc, &file) {
            let should_set =
                if let Some(input_date) = latest_file_date.as_ref() {
                    *input_date < mod_date
                } else {
                    true
                };

            if should_set {
                latest_file_date = Some(mod_date);
            }
        } else {
            // Could not get the mod date of an input.
            break;
        }
    }

    if let (Some(earliest_hex_date), Some(latest_file_date)) = (earliest_hex_date, latest_file_date) {
        if earliest_hex_date > latest_file_date {
            let mut summary = Rc::new(SExp::Nil(cf.loc.clone()));
            let mut components = Vec::new();

            for e in exports.iter() {
                let hex_file_name = get_hex_name_of_export(opts.clone(), &cf.loc, e)?;
                let (_, hex_data) = opts.read_new_file(opts.filename(), hex_file_name.clone())?;
                let loaded_hex_data = hex_to_modern_sexp(
                    context.allocator(),
                    &HashMap::new(),
                    cf.loc.clone(),
                    &decode_string(&hex_data)
                )?;
                let shortname =
                    if let Export::Function(name, _) = e {
                        name.clone()
                    } else {
                        b"program".to_vec()
                    };

                let hash = sha256tree(loaded_hex_data.clone());
                summary = Rc::new(SExp::Cons(
                    cf.loc.clone(),
                    Rc::new(SExp::Cons(
                        cf.loc.clone(),
                        Rc::new(SExp::QuotedString(cf.loc.clone(), b'"', shortname.clone())),
                        Rc::new(SExp::QuotedString(cf.loc.clone(), b'x', hash.clone()))
                    )),
                    summary,
                ));

                components.push(CompileModuleComponent {
                    shortname,
                    filename: hex_file_name,
                    content: loaded_hex_data,
                    hash,
                });
            }

            return Ok(Some(CompilerOutput::Module(CompileModuleOutput {
                summary,
                components,
                includes: cf.include_forms.clone(),
            })));
        }
    }

    Ok(None)
}

pub fn compile_pre_forms(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>],
) -> Result<CompilerOutput, CompileErr> {
    let p0 = frontend(opts.clone(), pre_forms)?;

    match p0 {
        FrontendOutput::CompileForm(p0) => Ok(CompilerOutput::Program(p0.include_forms.clone(), compile_from_compileform(
            context, opts, p0,
        )?)),
        FrontendOutput::Module(mut cf, exports) => {
            if let Some(result) = try_to_use_existing_hex_outputs(
                context,
                opts.clone(),
                &cf,
                &exports
            )? {
                return Ok(result);
            }

            // cl23 always reflects optimization.
            let dialect = opts.dialect();
            let opts = if let Some(stepping) = dialect.stepping.as_ref() {
                opts.set_optimize(*stepping > 21)
            } else {
                opts
            };

            // We make a dependency graph of constants and functions.  There must
            // be a solveable hierarchy for constants, that is some must be top
            // level constants that are not depended on.  Thse will not be tabled
            // with the rest, but computed once.  Practially, these will be
            // constants that are computed only for export and no other constants
            // or functions depend on them.  Specifically, any constant that is
            // not used by a constant or function is forced to be inline.  We will
            // expand it when generating the constant output.
            let depgraph = FunctionDependencyGraph::new_with_options(
                &cf, DepgraphOptions {
                    with_constants: true
                }
            );

            let all_constants: HashSet<Vec<u8>> = cf.helpers.iter().filter(|h| matches!(h, HelperForm::Defconstant(_))).map(|h| h.name().to_vec()).collect();
            let mut standalone_constants = HashSet::new();

            capture_standalone_constants(
                &mut standalone_constants,
                &depgraph,
                &cf.helpers,
                &exports,
            );
            modernize_constants(&mut cf.helpers, &standalone_constants);
            Ok(CompilerOutput::Module(compile_module(
                context, opts, &standalone_constants, cf, &exports,
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
    fn module_phase(&self) -> Option<ModulePhase> {
        self.module_phase.clone()
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

    fn set_filename(&self, filename: &str) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.filename = filename.to_string();
        Rc::new(copy)
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
    fn set_module_phase(&self, module_phase: Option<ModulePhase>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        eprintln!("set module_phase {module_phase:?}");
        copy.module_phase = module_phase;
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

    fn get_file_mod_date(&self, loc: &Srcloc, filename: &str) -> Result<u64, CompileErr> {
        fs::metadata(&filename)
            .map_err(|e| format!("could not get metadata for {filename}: {e:?}"))
            .and_then(|m| {
                m.modified()
                    .map_err(|e| format!("could not get modified time for {filename}: {e:?}"))
            })
            .and_then(|m| {
                m.duration_since(UNIX_EPOCH)
                    .map_err(|e| format!("Could not convert modified time of {filename} to seconds since unix epoch: {e:?}"))
            })
            .map(|m| m.as_secs())
            .map_err(|e| CompileErr(loc.clone(), e))
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
        assert!(self.module_phase().is_none());
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
            module_phase: None,
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
