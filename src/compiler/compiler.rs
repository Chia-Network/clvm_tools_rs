use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator
};

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType
};
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};

use crate::compiler::comptypes::{
    CompileErr,
    CompilerOpts,
    PrimaryCodegen
};
use crate::compiler::prims;
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::frontend::frontend;
use crate::compiler::codegen::codegen;

#[derive(Clone)]
#[derive(Debug)]
pub struct DefaultCompilerOpts {
    pub include_dirs: Vec<String>,
    pub filename: String,
    pub compiler: Option<PrimaryCodegen>,
    pub in_defun: bool,
    pub assemble: bool,
    pub stdenv: bool,
    pub start_env: Option<Rc<SExp>>,
    pub prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>
}

pub fn compile_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    content: &String
) -> Result<String, CompileErr> {
    let pre_forms =
        parse_sexp(Srcloc::start(&opts.filename()), content).map_err(|e| {
            CompileErr(e.0, e.1)
        })?;

    frontend(opts.clone(), pre_forms).
        and_then(|g| codegen(allocator, runner, opts.clone(), &g)).
        map(|result| {
            if opts.assemble() {
                Bytes::new(Some(BytesFromType::Raw(result.encode()))).hex()
            } else {
                result.to_string()
            }
        })
}

impl CompilerOpts for DefaultCompilerOpts {
    fn filename(&self) -> String { self.filename.clone() }
    fn compiler(&self) -> Option<PrimaryCodegen> { self.compiler.clone() }
    fn in_defun(&self) -> bool { self.in_defun }
    fn assemble(&self) -> bool { self.assemble }
    fn stdenv(&self) -> bool { self.stdenv }
    fn start_env(&self) -> Option<Rc<SExp>> { self.start_env.clone() }
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>> { self.prim_map.clone() }

    fn set_search_paths(&self, dirs: &Vec<String>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.include_dirs = dirs.clone();
        return Rc::new(copy);
    }
    fn set_assemble(&self, new_assemble: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.assemble = new_assemble;
        return Rc::new(copy);
    }
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.in_defun = new_in_defun;
        return Rc::new(copy);
    }
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.stdenv = new_stdenv;
        return Rc::new(copy);
    }
    fn set_compiler(&self, new_compiler: PrimaryCodegen) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.compiler = Some(new_compiler);
        return Rc::new(copy);
    }
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts> {
        let mut copy = self.clone();
        copy.start_env = start_env;
        return Rc::new(copy);
    }

    fn read_new_file(&self, inc_from: String, filename: String) -> Result<(String,String), CompileErr> {
        if filename == "*macros*" {
            let macros = indoc! {"(
                (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @)))
                (defmacro list args (defun makelist (args) (if args (c (q . c) (c (f args) (c (makelist (r args)) (q . ())))) (q . ()))) (makelist args))
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
                Err(e) => { continue; },
                Ok(content) => { return Ok((filename, content)); }
            }
        }
        return Err(CompileErr(Srcloc::start(&inc_from), format!("could not find {} to include", filename)));
    }
    fn compile_program(&self, allocator: &mut Allocator, runner: Rc<dyn TRunProgram>, sexp: Rc<SExp>) -> Result<SExp, CompileErr> {
        let me = Rc::new(self.clone());
        frontend(me.clone(), vec!(sexp)).
            and_then(|g| codegen(allocator, runner, me.clone(), &g))
    }
}

impl DefaultCompilerOpts {
    pub fn new(filename: &String) -> DefaultCompilerOpts {
        let mut prim_map = HashMap::new();

        for p in prims::prims() {
            prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
        }

        DefaultCompilerOpts {
            include_dirs: vec!(".".to_string()),
            filename: filename.clone(),
            compiler: None,
            in_defun: false,
            assemble: false,
            stdenv: true,
            start_env: None,
            prim_map: Rc::new(prim_map)
        }
    }

}
