use num_bigint::ToBigInt;

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::classic::clvm_tools::stages::stage_2::optimize::optimize_sexp;

use crate::compiler::clvm::{
    choose_path, convert_from_clvm_rs, convert_to_clvm_rs, extract_program_and_env,
    path_to_function, rewrite_in_program,
};
use crate::compiler::codegen::codegen;
use crate::compiler::comptypes::{CompileErr, CompilerOpts, PrimaryCodegen};
use crate::compiler::frontend::frontend;
use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Clone, Debug)]
pub struct DefaultCompilerOpts {
    pub include_dirs: Vec<String>,
    pub filename: String,
    pub compiler: Option<PrimaryCodegen>,
    pub in_defun: bool,
    pub stdenv: bool,
    pub optimize: bool,
    pub start_env: Option<Rc<SExp>>,
    pub prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
}

pub fn compile_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    content: &String,
) -> Result<SExp, CompileErr> {
    let pre_forms =
        parse_sexp(Srcloc::start(&opts.filename()), content).map_err(|e| CompileErr(e.0, e.1))?;

    frontend(opts.clone(), pre_forms).and_then(|g| codegen(allocator, runner, opts.clone(), &g))
}

pub fn run_optimizer(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    r: Rc<SExp>,
) -> Result<Rc<SExp>, CompileErr> {
    let to_clvm_rs = convert_to_clvm_rs(allocator, r.clone())
        .map(|x| (r.loc(), x))
        .map_err(|e| match e {
            RunFailure::RunErr(l, e) => CompileErr(l, e),
            RunFailure::RunExn(s, e) => CompileErr(s, format!("exception {}\n", e.to_string())),
        })?;

    let optimized = optimize_sexp(allocator, to_clvm_rs.1, runner)
        .map_err(|e| CompileErr(to_clvm_rs.0.clone(), e.1))
        .map(|x| (to_clvm_rs.0, x))?;

    convert_from_clvm_rs(allocator, optimized.0, optimized.1).map_err(|e| match e {
        RunFailure::RunErr(l, e) => CompileErr(l, e),
        RunFailure::RunExn(s, e) => CompileErr(s, format!("exception {}\n", e.to_string())),
    })
}

impl CompilerOpts for DefaultCompilerOpts {
    fn filename(&self) -> String {
        self.filename.clone()
    }
    fn compiler(&self) -> Option<PrimaryCodegen> {
        self.compiler.clone()
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
    fn start_env(&self) -> Option<Rc<SExp>> {
        self.start_env.clone()
    }
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
        self.prim_map.clone()
    }

    fn set_search_paths(&self, dirs: &Vec<String>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.include_dirs = dirs.clone();
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
    fn set_compiler(&self, new_compiler: PrimaryCodegen) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.compiler = Some(new_compiler);
        Rc::new(copy)
    }
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.start_env = start_env;
        Rc::new(copy)
    }

    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, String), CompileErr> {
        if filename == "*macros*" {
            let macros = indoc! {"(
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
            )"};
            return Ok((filename, macros.to_string()));
        } else if filename == "*standard-cl-21*" {
            let content = indoc! {"(
                (defconstant *chialisp-version* 21)
            )"};
            return Ok((filename, content.to_string()));
        }

        for dir in self.include_dirs.iter() {
            let mut p = PathBuf::from(dir);
            p.push(filename.clone());
            match fs::read_to_string(p) {
                Err(e) => {
                    continue;
                }
                Ok(content) => {
                    return Ok((filename, content));
                }
            }
        }
        return Err(CompileErr(
            Srcloc::start(&inc_from),
            format!("could not find {} to include", filename),
        ));
    }
    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
    ) -> Result<SExp, CompileErr> {
        let me = Rc::new(self.clone());
        frontend(me.clone(), vec![sexp]).and_then(|g| codegen(allocator, runner, me.clone(), &g))
    }
}

impl DefaultCompilerOpts {
    pub fn new(filename: &String) -> DefaultCompilerOpts {
        let mut prim_map = HashMap::new();

        for p in prims::prims() {
            prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
        }

        DefaultCompilerOpts {
            include_dirs: vec![".".to_string()],
            filename: filename.clone(),
            compiler: None,
            in_defun: false,
            stdenv: true,
            optimize: false,
            start_env: None,
            prim_map: Rc::new(prim_map),
        }
    }
}

// Given a function expecting (c env args) yield a function expecing (c _ args)
// and using a separately supplied menv.
pub fn harden_mock_function(mfunc: Rc<SExp>, menv: Rc<SExp>) -> Rc<SExp> {
    // (a mfunc (c menv (r 1)))
    Rc::new(enlist(
        mfunc.loc(),
        vec![
            Rc::new(SExp::Integer(mfunc.loc(), 2_u32.to_bigint().unwrap())),
            mfunc.clone(),
            Rc::new(enlist(
                mfunc.loc(),
                vec![
                    Rc::new(SExp::Integer(mfunc.loc(), 4_u32.to_bigint().unwrap())),
                    menv.clone(),
                    Rc::new(enlist(
                        mfunc.loc(),
                        vec![
                            Rc::new(SExp::Integer(mfunc.loc(), 6_u32.to_bigint().unwrap())),
                            Rc::new(SExp::Integer(mfunc.loc(), bi_one())),
                        ],
                    )),
                ],
            )),
        ],
    ))
}

// Given program, psymbols and mocks, msymbols, optional new main
// extract program and env from both yielding pmain, penv, menv
// collect paths to functions(F) in menv, produce a standalone program based on
// mocks which replaces its main expression with (a F (c menv (r 1)))
// for each item in menv, if psymbols contains the same name, then rewrite
// the path ppath in penv with the corresponding hardened mock program (fenv)
// let args be (c program 1)
// if new main, compile the new main expression with starting_env = fenv to
// (q . fprogram) else let fprogram be the path 10 (f (r (f args))) = final_main
// compose the resulting program:
// (a fprogram (c fenv (r args)))
pub fn mock_program(
    program: Rc<SExp>,
    psymbols: HashMap<String, String>,
    mocks: Rc<SExp>,
    msymbols: HashMap<String, String>,
    to_run: Option<String>,
) -> Result<Rc<SExp>, CompileErr> {
    let pres = extract_program_and_env(program.clone());
    if pres == None {
        return Err(CompileErr(
            program.loc(),
            "program isn't an understandable clvm program or doesn't have an env".to_string(),
        ));
    }
    let (pprogram, mut penv): (Rc<SExp>, Rc<SExp>) = pres.unwrap();

    let mres = extract_program_and_env(mocks.clone());
    if mres == None {
        return Err(CompileErr(
            mocks.loc(),
            "mocks isn't an understandable clvm program or doesn't have an env".to_string(),
        ));
    }
    let (mprogram, menv) = mres.unwrap();

    let mut known_mock_functions = HashMap::new();

    for (mk, mv) in msymbols.iter() {
        let decoded_hash = Bytes::new(Some(BytesFromType::Hex(mv.clone())));
        let path_in_mock_env = path_to_function(menv.clone(), decoded_hash.data());
        match path_in_mock_env {
            Some(p) => {
                known_mock_functions.insert(mk.clone(), p.clone());
            }
            None => {}
        }
    }

    for (pk, pv) in psymbols.iter() {
        let decoded_hash = Bytes::new(Some(BytesFromType::Hex(pv.clone())));
        let path_in_prog_env = path_to_function(penv.clone(), decoded_hash.data());
        let fenv: Rc<SExp> = known_mock_functions
            .get(pk)
            .and_then(|mf| path_in_prog_env.map(|p| (mf, p)))
            .and_then(|(mf, p)| {
                choose_path(
                    mprogram.loc(),
                    mf.clone(),
                    mf.clone(),
                    menv.clone(),
                    menv.clone(),
                )
                .map(|mprog| (mprog, p))
                .ok()
            })
            .and_then(|(mprog, p)| {
                rewrite_in_program(penv.clone(), p, harden_mock_function(mprog, menv.clone()))
            })
            .unwrap_or_else(|| penv.clone());
        penv = fenv;
    }

    let args = Rc::new(enlist(
        mprogram.loc(),
        vec![
            Rc::new(SExp::Integer(mprogram.loc(), 4_u32.to_bigint().unwrap())),
            program.clone(),
            Rc::new(SExp::Integer(mprogram.loc(), bi_one())),
        ],
    ));

    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = DefaultCompilerOpts::new(&mprogram.loc().file).set_start_env(Some(penv.clone()));
    let final_main = match to_run {
        Some(r) => Ok(r)
            .and_then(|trp| compile_file(&mut allocator, runner, opts, &trp))
            .map(|cr| {
                Rc::new(SExp::Cons(
                    mprogram.loc(),
                    Rc::new(SExp::Integer(mprogram.loc(), bi_one())),
                    Rc::new(cr),
                ))
            }),
        _ => Ok(Rc::new(SExp::Integer(
            mprogram.loc(),
            10_u32.to_bigint().unwrap(),
        ))),
    }?;
    Ok(Rc::new(enlist(
        mprogram.loc(),
        vec![
            Rc::new(SExp::Integer(mprogram.loc(), 2_u32.to_bigint().unwrap())),
            final_main,
            Rc::new(enlist(
                mprogram.loc(),
                vec![
                    Rc::new(SExp::Integer(mprogram.loc(), 4_u32.to_bigint().unwrap())),
                    penv,
                    Rc::new(enlist(
                        mprogram.loc(),
                        vec![
                            Rc::new(SExp::Integer(mprogram.loc(), 6_u32.to_bigint().unwrap())),
                            args,
                        ],
                    )),
                ],
            )),
        ],
    )))
}
