use rand_chacha::ChaCha8Rng;
use rand::{Rng, SeedableRng};
use std::borrow::Borrow;
use std::fmt::{Debug, Display};
use std::rc::Rc;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;

use clvmr::Allocator;

use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::compiler::BasicCompileContext;
use crate::compiler::clvm::{convert_to_clvm_rs, run};
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::{CompileErr, CompilerOpts, PrimaryCodegen};
use crate::compiler::dialect::{AcceptedDialect, detect_modern};
use crate::compiler::fuzz::{ExprModifier, FuzzGenerator, FuzzTypeParams, Rule};
use crate::compiler::sexp::{enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Debug)]
pub struct GenError { message: String }
impl From<&str> for GenError {
    fn from(m: &str) -> GenError { GenError { message: m.to_string() } }
}

pub fn compose_sexp(loc: Srcloc, s: &str) -> Rc<SExp> {
    parse_sexp(loc, s.bytes()).expect("should parse")[0].clone()
}

#[derive(Clone)]
pub struct TestModuleCompilerOpts {
    opts: Rc<dyn CompilerOpts>,
    written_files: Rc<RefCell<HashMap<String, Vec<u8>>>>,
}

impl TestModuleCompilerOpts {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        TestModuleCompilerOpts {
            opts: opts,
            written_files: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn new_opts(&self, opts: Rc<dyn CompilerOpts>) -> Rc<dyn CompilerOpts> {
        Rc::new(TestModuleCompilerOpts {
            opts,
            written_files: self.written_files.clone(),
        })
    }

    pub fn get_written_file<'a>(&'a self, name: &str) -> Option<Vec<u8>> {
        let files_ref: &RefCell<HashMap<String, Vec<u8>>> = self.written_files.borrow();
        let files: &HashMap<String, Vec<u8>> = &files_ref.borrow();
        files.get(name).map(|f| f.to_vec())
    }
}

impl CompilerOpts for TestModuleCompilerOpts {
    fn filename(&self) -> String {
        self.opts.filename()
    }

    fn code_generator(&self) -> Option<PrimaryCodegen> {
        self.opts.code_generator()
    }
    fn dialect(&self) -> AcceptedDialect {
        self.opts.dialect()
    }
    fn in_defun(&self) -> bool {
        self.opts.in_defun()
    }
    fn stdenv(&self) -> bool {
        self.opts.stdenv()
    }
    fn optimize(&self) -> bool {
        self.opts.optimize()
    }
    fn frontend_opt(&self) -> bool {
        self.opts.frontend_opt()
    }
    fn frontend_check_live(&self) -> bool {
        self.opts.frontend_check_live()
    }
    fn start_env(&self) -> Option<Rc<SExp>> {
        self.opts.start_env()
    }
    fn disassembly_ver(&self) -> Option<usize> {
        self.opts.disassembly_ver()
    }
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
        self.opts.prim_map()
    }
    fn get_search_paths(&self) -> Vec<String> {
        self.opts.get_search_paths()
    }
    fn set_dialect(&self, dialect: AcceptedDialect) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_dialect(dialect))
    }
    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_search_paths(dirs))
    }
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_in_defun(new_in_defun))
    }
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_stdenv(new_stdenv))
    }
    fn set_optimize(&self, opt: bool) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_optimize(opt))
    }
    fn set_frontend_opt(&self, opt: bool) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_frontend_opt(opt))
    }
    fn set_frontend_check_live(&self, check: bool) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_frontend_check_live(check))
    }
    fn set_code_generator(&self, new_compiler: PrimaryCodegen) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_code_generator(new_compiler))
    }
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_start_env(start_env))
    }
    fn set_prim_map(&self, prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_prim_map(prims))
    }
    fn set_disassembly_ver(&self, ver: Option<usize>) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_disassembly_ver(ver))
    }
    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, Vec<u8>), CompileErr> {
        self.opts.read_new_file(inc_from, filename)
    }
    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr> {
        self.opts.compile_program(allocator, runner, sexp, symbol_table)
    }
}

pub struct PerformCompileResult {
    pub compiled: Rc<SExp>,
    pub source_opts: TestModuleCompilerOpts,
}

pub fn perform_compile_of_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    filename: &str,
    content: &str,
) -> Result<PerformCompileResult, CompileErr> {
    let loc = Srcloc::start(filename);
    let parsed: Vec<Rc<SExp>> = parse_sexp(loc.clone(), content.bytes()).expect("should parse");
    let listed = Rc::new(enlist(loc.clone(), &parsed));
    let nodeptr = convert_to_clvm_rs(allocator, listed.clone()).expect("should convert");
    let dialect = detect_modern(allocator, nodeptr);
    let orig_opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(filename))
        .set_optimize(true)
        .set_frontend_opt(false)
        .set_dialect(dialect)
        .set_search_paths(&["resources/tests/module".to_string()]);
    let source_opts = TestModuleCompilerOpts::new(orig_opts);
    let opts: Rc<dyn CompilerOpts> = Rc::new(source_opts.clone());
    let mut symbol_table = HashMap::new();
    let compiled = compile_file(
        allocator,
        runner.clone(),
        opts,
        &content,
        &mut symbol_table,
    )?;
    Ok(PerformCompileResult {
        compiled: Rc::new(compiled),
        source_opts,
    })
}

pub fn simple_run(opts: Rc<dyn CompilerOpts>, expr: Rc<SExp>, env: Rc<SExp>) -> Result<Rc<SExp>, CompileErr> {
    let mut allocator = Allocator::new();
    let runner: Rc<dyn TRunProgram> = Rc::new(DefaultProgramRunner::new());
    Ok(run(
        &mut allocator,
        runner,
        opts.prim_map(),
        expr,
        env,
        None,
        None
    )?)
}

pub fn simple_seeded_rng(seed: u32) -> ChaCha8Rng {
    ChaCha8Rng::from_seed([
        1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,
        2,2,2,2,2,2,2,2,
        2,2,2,2,
        ((seed >> 24) & 0xff) as u8,
        ((seed >> 16) & 0xff) as u8,
        ((seed >> 8) & 0xff) as u8,
        (seed & 0xff) as u8,
    ])

}

pub trait PropertyTestState {
    fn new_state<R: Rng>(rng: &mut R) -> Self;
    fn run_args(&self) -> String;
    fn check(&self, run_result: Rc<SExp>);
}

pub struct PropertyTest<FT: FuzzTypeParams> {
    pub run_times: usize,
    pub run_cutoff: usize,
    pub run_expansion: usize,

    pub top_node: FT::Expr,
    pub rules: Vec<Rc<dyn Rule<FT>>>,
}

impl<FT: FuzzTypeParams> PropertyTest<FT> {
    pub fn run<R>(
        &self,
        rng: &mut R,
    )
    where
        R: Rng + Sized,
        FT::State: PropertyTestState,
        FT::Error: Debug,
        FT::Expr: ToString + Display,
    {
        let srcloc = Srcloc::start("*value*");
        let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*test*"));

        for i in 0..self.run_times {
            let mut idx = 0;
            let mut fuzzgen = FuzzGenerator::new(self.top_node.clone(), &self.rules);
            let mut mc = FT::State::new_state(rng);
            while fuzzgen.expand(&mut mc, idx > self.run_expansion, rng).expect("should expand") {
                idx += 1;
                assert!(idx < self.run_cutoff);
            }

            let mut allocator = Allocator::new();
            let runner = Rc::new(DefaultProgramRunner::new());
            let program_text = fuzzgen.result().to_string();
            eprintln!("program_text {program_text}");
            let compiled = perform_compile_of_file(
                &mut allocator,
                runner.clone(),
                "test.clsp",
                &program_text,
            ).expect("should compile");

            // Collect output values from compiled.
            let run_args = mc.run_args();
            let arg = compose_sexp(srcloc.clone(), &run_args);
            let run_result = simple_run(opts.clone(), compiled.compiled.clone(), arg).expect("should run");
            mc.check(run_result);
        }

        // We've checked all predicted values.
    }
}
