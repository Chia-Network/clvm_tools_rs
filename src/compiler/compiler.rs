use std::borrow::Borrow;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use num_bigint::ToBigInt;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::clvm_tools::stages::stage_2::optimize::optimize_sexp;

use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs, sha256tree};
use crate::compiler::codegen::codegen;
use crate::compiler::comptypes::{CompileErr, CompilerOpts, PrimaryCodegen};
use crate::compiler::frontend::frontend;
use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

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
    symbol_table: &mut HashMap<String, String>,
) -> Result<SExp, CompileErr> {
    let pre_forms =
        parse_sexp(Srcloc::start(&opts.filename()), content).map_err(|e| CompileErr(e.0, e.1))?;

    frontend(opts.clone(), pre_forms).and_then(|g| codegen(allocator, runner, opts.clone(), &g, symbol_table))
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
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr> {
        let me = Rc::new(self.clone());
        frontend(me.clone(), vec![sexp]).and_then(|g| codegen(allocator, runner, me.clone(), &g, symbol_table))
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

fn path_to_function_inner(
    program: Rc<SExp>,
    hash: &Vec<u8>,
    path_mask: Number,
    current_path: Number,
) -> Option<Number> {
    let nextpath = path_mask.clone() * 2_i32.to_bigint().unwrap();
    match program.borrow() {
        SExp::Cons(_, a, b) => {
            path_to_function_inner(a.clone(), hash, nextpath.clone(), current_path.clone())
                .map(|x| Some(x))
                .unwrap_or_else(|| {
                    path_to_function_inner(
                        b.clone(),
                        hash,
                        nextpath.clone(),
                        current_path.clone() + path_mask.clone(),
                    )
                    .map(|x| Some(x))
                    .unwrap_or_else(|| {
                        let current_hash = sha256tree(program.clone());
                        if &current_hash == hash {
                            Some(current_path + path_mask)
                        } else {
                            None
                        }
                    })
                })
        }
        any => {
            let current_hash = sha256tree(program.clone());
            if &current_hash == hash {
                Some(current_path + path_mask)
            } else {
                None
            }
        }
    }
}

pub fn path_to_function(program: Rc<SExp>, hash: &Vec<u8>) -> Option<Number> {
    path_to_function_inner(program, hash, bi_one(), bi_zero())
}

// compose (a (* (q . 2) path) (c env args))
pub fn rewrite_in_program(
    path: Number,
    env: Rc<SExp>,
    args: Rc<SExp>
) -> Rc<SExp> {
    Rc::new(SExp::Cons(
        env.loc(),
        Rc::new(SExp::Integer(env.loc(), 2_u32.to_bigint().unwrap())),
        Rc::new(SExp::Cons(
            env.loc(),
            Rc::new(SExp::Integer(
                env.loc(),
                path * 2_u32.to_bigint().unwrap()
            )),
            Rc::new(SExp::Cons(
                env.loc(),
                Rc::new(SExp::Cons(
                    env.loc(),
                    Rc::new(SExp::Integer(env.loc(), 4_u32.to_bigint().unwrap())),
                    Rc::new(SExp::Cons(
                        env.loc(),
                        Rc::new(SExp::Cons(
                            env.loc(),
                            Rc::new(SExp::Integer(env.loc(), bi_one())),
                            env.clone()
                        )),
                        Rc::new(SExp::Cons(
                            args.loc(),
                            Rc::new(SExp::Cons(
                                args.loc(),
                                Rc::new(SExp::Integer(args.loc(), bi_one())),
                                args.clone()
                            )),
                            Rc::new(SExp::Nil(args.loc()))
                        ))
                    ))
                )),
                Rc::new(SExp::Nil(env.loc()))
            ))
        ))
    ))
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

            match (is_apply(&lst[0]), lst[1].borrow(), lst[2].proper_list()) {
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
