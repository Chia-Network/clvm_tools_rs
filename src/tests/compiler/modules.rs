use std::cell::{RefCell, Ref, RefMut};
use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

use clvmr::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, Stream, UnvalidatedBytesFromType};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm_tools::binutils::{assemble, disassemble};
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::compiler::clvm::convert_to_clvm_rs;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::{CompileErr, CompilerOpts, PrimaryCodegen};
use crate::compiler::dialect::{AcceptedDialect, detect_modern};
use crate::compiler::sexp::{decode_string, enlist, SExp, parse_sexp};
use crate::compiler::srcloc::Srcloc;

#[derive(Clone)]
struct TestModuleCompilerOpts {
    opts: Rc<dyn CompilerOpts>,
    written_files: Rc<RefCell<HashMap<String, Vec<u8>>>>
}

impl TestModuleCompilerOpts {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        TestModuleCompilerOpts {
            opts: opts,
            written_files: Rc::new(RefCell::new(HashMap::new()))
        }
    }

    fn new_opts(&self, opts: Rc<dyn CompilerOpts>) -> Rc<dyn CompilerOpts> {
        Rc::new(TestModuleCompilerOpts {
            opts,
            written_files: self.written_files.clone()
        })
    }

    pub fn get_written_file<'a>(&'a self, name: &str) -> Option<Vec<u8>> {
        let files: Ref<'_, HashMap<String, Vec<u8>>> = self.written_files.borrow();
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
    fn write_new_file(
        &self,
        target: &str,
        content: &[u8]
    ) -> Result<(), CompileErr> {
        let mut wf: RefMut<'_, HashMap<String, Vec<u8>>> = self.written_files.borrow_mut();
        wf.insert(target.to_string(), content.to_vec());
        Ok(())
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


#[test]
fn test_simple_module_compliation() {
    let filename = "resources/tests/module/modtest1.clsp";

    let content = fs::read_to_string(filename).expect("file should exist");
    let loc = Srcloc::start(filename);
    let parsed: Vec<Rc<SExp>> = parse_sexp(loc.clone(), content.bytes()).expect("should parse");
    let listed = Rc::new(enlist(loc.clone(), &parsed));
    let mut allocator = Allocator::new();
    let nodeptr = convert_to_clvm_rs(&mut allocator, listed.clone()).expect("should convert");
    let dialect = detect_modern(&mut allocator, nodeptr);
    let orig_opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(filename)).set_dialect(dialect).set_search_paths(&[
        "resources/tests/module".to_string()
    ]);
    let source_opts = TestModuleCompilerOpts::new(orig_opts);
    let opts: Rc<dyn CompilerOpts> = Rc::new(source_opts.clone());
    let mut symbol_table = HashMap::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let compiled = compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &content,
        &mut symbol_table
    ).expect("should compile");
    let hex_filename = "resources/tests/module/modtest1.hex";
    let hex_data = source_opts.get_written_file(hex_filename).expect("should have written hex data beside the source file");
    let mut hex_stream = Stream::new(Some(Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(decode_string(&hex_data)))).expect("should be valid hex")));
    let compiled_node = sexp_from_stream(&mut allocator, &mut hex_stream, Box::new(SimpleCreateCLVMObject {})).expect("hex data should decode as sexp").1;

    let env_3 = assemble(&mut allocator, "(3)").expect("should assemble");
    let run_result_3 = runner.run_program(
        &mut allocator,
        compiled_node,
        env_3,
        None
    ).expect("should run");
    assert_eq!(disassemble(&mut allocator, run_result_3.1, None), "3");

    let env_13 = assemble(&mut allocator, "(13)").expect("should assemble");
    let run_result = runner.run_program(
        &mut allocator,
        compiled_node,
        env_13,
        None
    );
    assert!(run_result.is_err());
}
