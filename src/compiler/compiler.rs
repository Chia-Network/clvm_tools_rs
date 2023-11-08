use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::sha256tree;
use crate::compiler::codegen::{codegen, hoist_body_let_binding, process_helper_let_bindings};
use crate::compiler::comptypes::{Alias, BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, NamespaceCollection, PrimaryCodegen, SyntheticType};
use crate::compiler::dialect::{AcceptedDialect, KNOWN_DIALECTS};
use crate::compiler::frontend::{compile_bodyform, compile_helperform, frontend, recognize_defalias};
use crate::compiler::optimize::get_optimizer;
use crate::compiler::preprocessor::preprocess;
use crate::compiler::prims;
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

fn detect_chialisp_module(
    pre_forms: &[Rc<SExp>],
) -> bool {
    if pre_forms.is_empty() {
        return false;
    }

    if pre_forms.len() > 1 {
        return true;
    }

    if let Some(lst) = pre_forms[0].proper_list() {
        eprintln!("checking whether {} is an element of a module", lst[0]);
        return matches!(lst[0].borrow(), SExp::Cons(_, _, _));
    }

    true
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
        if let SExp::Atom(kw, export_name) = lst[0].borrow() {
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

        if let SExp::Atom(fun_kw, fun_name) = lst[1].borrow() {
            return Ok(Some(Export::Function(fun_name.clone())));
        }

        return Err(CompileErr(form.loc(), format!("Malformed export {form}")));
    }

    Ok(None)
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
fn compile_module(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>]
) -> Result<SExp, CompileErr> {
    let mut other_forms = vec![];
    let mut exports = vec![];
    let mut found_main = false;
    let mut includes = vec![];

    if pre_forms.is_empty() {
        return Err(CompileErr(Srcloc::start(&opts.filename()), "We don't yet allow empty programs".to_string()));
    }

    let loc = pre_forms[0].loc().ext(&pre_forms[pre_forms.len()-1].loc());
    let preprocess_source = Rc::new(enlist(loc.clone(), pre_forms));
    let output_forms = preprocess(
        opts.clone(),
        &mut includes,
        preprocess_source
    )?;

    let mut namespace_collection = NamespaceCollection::default();

    for p in output_forms.iter() {
        if let Some(alias) = recognize_defalias(opts.clone(), p.clone())? {
            match alias {
                Alias::End(namespace_id) => {
                    namespace_collection.remove(namespace_id.clone());
                },
                _ => {
                    namespace_collection.add(alias.clone());
                }
            }
        } else if let Some(export) = match_export_form(opts.clone(), p.clone())? {
            if matches!(export, Export::MainProgram(_, _)) {
                if found_main || !exports.is_empty() {
                    return Err(CompileErr(
                        loc.clone(),
                        "Only one main export is allowed, otherwise export functions".to_string()
                    ));
                }

                found_main = true;
            }

            if found_main {
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
        include_forms: includes.clone(),
        args: Rc::new(SExp::Nil(loc.clone())),
        helpers: other_forms.clone(),
        exp: Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone()))),
        ty: None,
    };

    if exports.len() == 1 {
        if let Export::MainProgram(args, expr) = &exports[0] {
            // Single program.
            eprintln!("basic program {}", program.to_sexp());
            program.args = args.clone();
            program.exp = expr.clone();

            return compile_from_compileform(context, opts, program);
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
    compile_from_compileform(context, opts, program)
}

pub fn compile_pre_forms(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    pre_forms: &[Rc<SExp>],
) -> Result<SExp, CompileErr> {
    let p0 = frontend(opts.clone(), pre_forms)?;

    compile_from_compileform(context, opts, p0)
}

pub fn compile_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    content: &str,
    symbol_table: &mut HashMap<String, String>,
) -> Result<SExp, CompileErr> {
    let srcloc = Srcloc::start(&opts.filename());
    let pre_forms = parse_sexp(srcloc.clone(), content.bytes())?;
    let mut context_wrapper = CompileContextWrapper::new(
        allocator,
        runner,
        symbol_table,
        get_optimizer(&srcloc, opts.clone())?,
    );

    if detect_chialisp_module(&pre_forms) && opts.dialect().strict {
        return compile_module(&mut context_wrapper.context, opts, &pre_forms);
    }

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
        compile_pre_forms(&mut context_wrapper.context, me, &[sexp])
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
