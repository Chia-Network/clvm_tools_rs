use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::borrow::Borrow;
use std::cell::{Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::rc::Rc;

use clvmr::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, Stream, UnvalidatedBytesFromType};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm_tools::binutils::{assemble, disassemble};
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};

use crate::compiler::clvm::convert_to_clvm_rs;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::{CompileErr, CompilerOpts, CompilerOutput, PrimaryCodegen};
use crate::compiler::dialect::{detect_modern, AcceptedDialect};
use crate::compiler::fuzz::{FuzzGenerator, Rule};
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::BasicCompileContext;

enum DesiredOutcome<'a> {
    Error,
    ContentEquals,
    Run(&'a str),
}

use DesiredOutcome::{ContentEquals, Error, Run};

#[derive(Clone)]
struct TestModuleCompilerOpts {
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
    fn set_filename(&self, filename: &str) -> Rc<dyn CompilerOpts> {
        self.new_opts(self.opts.set_filename(filename))
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
    fn write_new_file(&self, target: &str, content: &[u8]) -> Result<(), CompileErr> {
        let mut wf: RefMut<'_, HashMap<String, Vec<u8>>> = self.written_files.borrow_mut();
        wf.insert(target.to_string(), content.to_vec());
        Ok(())
    }
    fn compile_program(
        &self,
        context: &mut BasicCompileContext,
        sexp: Rc<SExp>,
    ) -> Result<CompilerOutput, CompileErr> {
        self.opts.compile_program(context, sexp)
    }
}

struct HexArgumentOutcome<'a> {
    hexfile: &'a str,
    argument: &'a str,
    outcome: DesiredOutcome<'a>,
}

struct PerformCompileResult {
    compiled: CompilerOutput,
    source_opts: TestModuleCompilerOpts,
}

fn perform_compile_of_file(
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
        .set_dialect(dialect)
        .set_search_paths(&["resources/tests/module".to_string()]);
    let source_opts = TestModuleCompilerOpts::new(orig_opts);
    let opts: Rc<dyn CompilerOpts> = Rc::new(source_opts.clone());
    let mut symbol_table = HashMap::new();
    let mut includes = Vec::new();
    let compiled = compile_file(
        allocator,
        runner.clone(),
        opts,
        &content,
        &mut symbol_table,
        &mut includes,
    )?;
    Ok(PerformCompileResult {
        compiled,
        source_opts,
    })
}

fn test_compile_and_run_program_with_modules(
    filename: &str,
    content: &str,
    runs: &[HexArgumentOutcome],
) {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let compile_result = perform_compile_of_file(
        &mut allocator,
        runner.clone(),
        filename,
        content
    );

    let compile_result =
        if runs.is_empty() {
            assert!(compile_result.is_err());
            return;
        } else {
            compile_result.expect("Was expected to compile")
        };

    for run in runs.iter() {
        let hex_data = compile_result.source_opts
            .get_written_file(run.hexfile)
            .expect("should have written hex data beside the source file");
        let mut hex_stream = Stream::new(Some(
            Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(decode_string(
                &hex_data,
            ))))
            .expect("should be valid hex"),
        ));
        let compiled_node = sexp_from_stream(
            &mut allocator,
            &mut hex_stream,
            Box::new(SimpleCreateCLVMObject {}),
        )
        .expect("hex data should decode as sexp")
        .1;

        if matches!(&run.outcome, ContentEquals) {
            let disassembled = disassemble(&allocator, compiled_node, None);
            assert_eq!(run.argument, disassembled);
            continue;
        }

        let assembled_env = assemble(&mut allocator, run.argument).expect("should assemble");
        let run_result = runner.run_program(&mut allocator, compiled_node, assembled_env, None);
        if let Run(res) = &run.outcome {
            let have_outcome = run_result.expect("expected success").1;
            assert_eq!(&disassemble(&mut allocator, have_outcome, None), res);
        } else {
            assert!(run_result.is_err());
        }
    }
}

#[test]
fn test_simple_module_compilation() {
    let filename = "resources/tests/module/modtest1.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest1.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(3)",
                outcome: Run("3"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13)",
                outcome: Error,
            },
        ],
    );
}

#[test]
fn test_simple_module_compilation_assign_rewrite() {
    let filename = "resources/tests/module/modtest1_assign.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest1_assign.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(3)",
                outcome: Run("3"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13)",
                outcome: Error,
            },
        ],
    );
}

#[test]
fn test_simple_module_compilation_lambda_rewrite() {
    let filename = "resources/tests/module/modtest1_lambda.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest1_lambda.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(3 13)",
                outcome: Run("16"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13 3)",
                outcome: Error,
            },
        ],
    );
}

#[test]
fn test_simple_module_compilation_lambda_rewrite_with_body() {
    let filename = "resources/tests/module/modtest2_lambda.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest2_lambda.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(3 13)",
                outcome: Run("(+ 39)"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13 3)",
                outcome: Error,
            },
        ],
    );
}

#[test]
fn test_simple_module_compilation_import_program_0() {
    let filename = "resources/tests/module/basic_program_import.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/basic_program_import.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "()",
                outcome: Run("(0x9df8d4d222276747372a532a1cd736cdd5c6800c39906c9695489d36286ed215 (+ 2 (q . 1)))")
            }
        ]
    );
}

#[test]
fn test_simple_module_compilation_import_program_1() {
    let filename = "resources/tests/module/two_program_import.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/two_program_import.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13 73)",
                outcome: Run("(0xd85eec1bed9af4d6d161663e846857ae27010ad2a80b3ab8ccbb9fbd2c3bfa46 14 (a (q 16 5 (q . 1)) (c (q (+ 5 (q . 1)) 18 5 (q . 2)) 1)) 0x91a9f6736103e339a1d3b25e9d1dbc57de2bf643494c00f82b462ddf4912b11c 146 (a (q 18 5 (q . 2)) (c (q (+ 5 (q . 1)) 18 5 (q . 2)) 1)))")
            }
        ]
    );
}

#[test]
fn test_simple_module_compilation_import_classic_program() {
    let filename = "resources/tests/module/classic_program_import.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/classic_program_import.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "()",
                outcome: Run("(0x27a343d6617931e67a7eb27a41f7c4650b5fa79d8b5132af1b4eae959bdf2272 (* 2 (q . 13)))")
            }
        ]
    );
}

#[test]
fn test_simple_module_compilation_simple_type_1() {
    let filename = "resources/tests/module/modtest1_current_module_type.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest1_current_module_type.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(13 17)",
            outcome: Run("13"),
        }],
    );
}

#[test]
fn test_simple_module_compilation_simple_type_2() {
    let filename = "resources/tests/module/modtest1_other_module_type.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/modtest1_other_module_type.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(13 17)",
            outcome: Run("13"),
        }],
    );
}

#[test]
fn test_function_with_argument_names_overlapping_primitives() {
    let filename = "resources/tests/module/test_prepend.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test_prepend.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "((1 2 3) (4 5 6))",
            outcome: Run("(q 2 3 4 5 6)"),
        }],
    );
}

#[test]
fn test_handcalc() {
    let filename = "resources/tests/module/test_handcalc.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test_handcalc.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "()",
            outcome: Run("()"),
        }],
    );
}

#[test]
fn test_factorial() {
    let filename = "resources/tests/module/test_factorial.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test_factorial.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(4)",
            outcome: Run("24"),
        }],
    );
}

#[test]
fn test_deep_compare() {
    let filename = "resources/tests/module/test_deep_compare.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test_deep_compare.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(() 1)",
                outcome: Run("-1"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(1 ())",
                outcome: Run("1"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "((1 2 3) (1 2 3))",
                outcome: Run("()"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "((1 2 3) (1 2 4))",
                outcome: Run("-1"),
            },
        ],
    );
}

#[test]
fn test_import_constant() {
    let filename = "resources/tests/module/test-import-constant.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test-import-constant.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(5)",
            outcome: Run("6"),
        }],
    );
}

#[test]
fn test_export_constant() {
    let filename = "resources/tests/module/test-export-constant.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test-export-constant_add-5-and-9.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "()",
            outcome: Run("14"),
        }],
    );
}

#[test]
fn test_export_foreign_function() {
    let filename = "resources/tests/module/test-export-foreign-function.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test-export-foreign-function_factorial.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(4)",
            outcome: Run("24"),
        }],
    );
}

#[test]
fn test_export_foreign_constant() {
    let filename = "resources/tests/module/test-export-foreign-constant.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test-export-foreign-constant_ONE.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "()",
            outcome: Run("1"),
        }],
    );
}

#[test]
fn test_import_renamed() {
    let filename = "resources/tests/module/test_factorial_renamed.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_filename = "resources/tests/module/test_factorial_renamed.hex";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[HexArgumentOutcome {
            hexfile: hex_filename,
            argument: "(5)",
            outcome: Run("120"),
        }],
    );
}

#[test]
fn test_program_exporting_constant_from_program() {
    let filename = "resources/tests/module/test-export-constant-from-program.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let c_hex_filename = "resources/tests/module/test-export-constant-from-program_C.hex";
    let c_program_hex_filename = "resources/tests/module/programs/single-constant_C.hex";
    let c_value = "10197";

    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: c_hex_filename,
                argument: c_value,
                outcome: ContentEquals,
            },
            HexArgumentOutcome {
                hexfile: c_program_hex_filename,
                argument: c_value,
                outcome: ContentEquals,
            }
        ]
    );
}

#[test]
fn test_program_export_constant_and_function() {
    let filename = "resources/tests/module/test-export-constant-and-function.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let d_hex_filename = "resources/tests/module/test-export-constant-and-function_D.hex";
    let f_hex_filename = "resources/tests/module/test-export-constant-and-function_F.hex";
    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: d_hex_filename,
                argument: "(19191 (a (q 16 12 5) (c (q (() . 19191) (+ 12 5) . 0x3e6c399d8b10babad835468467a4b837036357ddfb8c320ba39a914c63152967) 1)) 0x3e6c399d8b10babad835468467a4b837036357ddfb8c320ba39a914c63152967 0x4d97c7350789cf972b8496c4393bfeae09f0e36d051ed0daa9fd1cfae9456e72)",
                outcome: ContentEquals,
            },
            HexArgumentOutcome {
                hexfile: f_hex_filename,
                argument: "(a (q 16 12 5) (c (q (() . 19191) (+ 12 5) . 0x3e6c399d8b10babad835468467a4b837036357ddfb8c320ba39a914c63152967) 1))",
                outcome: ContentEquals,
            },
        ]
    );
}

#[test]
fn test_detect_illegal_constant_arrangement() {
    let filename = "resources/tests/module/illegal-constant-arrangement-1.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
        ]
    );
}

#[test]
fn test_legal_all_tabled() {
    let filename = "resources/tests/module/legal-all-tabled.clsp";
    let content = fs::read_to_string(filename).expect("file should exist");
    let hex_file = "resources/tests/module/legal-all-tabled_F.hex";
    test_compile_and_run_program_with_modules(
        filename,
        &content,
        &[
            HexArgumentOutcome {
                hexfile: hex_file,
                argument: "(3)",
                outcome: Run("6")
            },
        ]
    );
}

// Property test of sorts:
//
// Make 1-5 constants with any of these expression types:
//   let or assign form
//   lambda (and a corresponding constant applying it either directly or via map
//   or filter)?
//   a few basic operators
// Constants generated one at a time, depending on each other in tiers.
// Constants generated all at once, depending on any arrangement of the others.
//
// Do the above arrangement but adding 1 or 2 functions that depend on the
// constants and each other.
//
// Maybe put some more thought into fuzzing infra?
struct ModuleConstantExpectation {
    constants_and_values: HashMap<Vec<u8>, Rc<SExp>>,
    exports: HashSet<Vec<u8>>,
}
impl ModuleConstantExpectation {
    fn new() -> Self {
        ModuleConstantExpectation {
            exports: HashSet::new(),
            constants_and_values: HashMap::new()
        }
    }
}

struct TestModuleConstantFuzzTopRule { another_constant: bool }
impl TestModuleConstantFuzzTopRule {
    fn new(c: bool) -> Self {
        TestModuleConstantFuzzTopRule { another_constant: c }
    }
}
impl Rule<ModuleConstantExpectation> for TestModuleConstantFuzzTopRule {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        eprintln!("T rule check {} {idx} term {terminate} {heritage_list:?}", decode_string(tag));
        if tag == b"top" {
            if self.another_constant {
                let start_program = parse_sexp(Srcloc::start("*top*"), format!("( (include *standard-cl-23*) ${{{idx}:constant}} . ${{{}:constant-program-tail}})", idx + 1).bytes()).expect("should parse");
                return Some(start_program[0].clone());
            } else {
                let start_program = parse_sexp(Srcloc::start("*top*"), format!("( (include *standard-cl-23*) (defconstant A ${{{idx}:constant-body}}) (export A))").bytes()).expect("should parse");
                state.exports.insert(b"A".to_vec());
                return Some(start_program[0].clone());
            }
        }

        None
    }
}

struct TestModuleConstantFuzzConstantBodyRule { }
impl TestModuleConstantFuzzConstantBodyRule {
    fn new() -> Self { TestModuleConstantFuzzConstantBodyRule { } }
}

fn get_constant_id(heritage: &[Rc<SExp>]) -> Option<Vec<u8>> {
    if heritage.len() < 2 {
        return None;
    }

    if let SExp::Cons(_, c, _) = heritage[heritage.len() - 2].borrow() {
        if let SExp::Atom(_, a) = c.borrow() {
            return Some(a.to_vec());
        }
    }

    None
}

impl Rule<ModuleConstantExpectation> for TestModuleConstantFuzzConstantBodyRule {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        eprintln!("C rule check {} {idx} term {terminate} {heritage_list:?}", decode_string(tag));

        if tag == b"constant-body" {
            let body = parse_sexp(Srcloc::start("*constant-body*"), format!("1").bytes()).expect("should parse");
            let constant_id =
                if let Some(constant_id) = get_constant_id(heritage) {
                    constant_id
                } else {
                    todo!();
                };

            state.constants_and_values.insert(constant_id, body[0].clone());
            return Some(body[0].clone());
        }

        None
    }
}

#[test]
fn test_property_fuzz_stable_constants() {
    let mut rng = ChaCha8Rng::from_seed([
        1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,
        2,2,2,2,2,2,2,2,
        2,2,2,2,2,2,2,2,
    ]);
    let mut fuzzgen = FuzzGenerator::new(&[
        Rc::new(TestModuleConstantFuzzTopRule::new(false)),
        Rc::new(TestModuleConstantFuzzTopRule::new(true)),
        Rc::new(TestModuleConstantFuzzConstantBodyRule::new()),
    ]);

    let mut idx = 0;
    let mut mc = ModuleConstantExpectation::new();
    while fuzzgen.expand(&mut mc, idx < 100, &mut rng).expect("should expand") {
        idx += 1;
    }

    let forms =
        if let Some(flist) = fuzzgen.result().proper_list() {
            flist
        } else {
            todo!();
        };

    let program_text = forms.iter().map(|f| f.to_string()).collect::<Vec<String>>().join("\n");
    eprintln!("program_text\n{program_text}");
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let compiled = perform_compile_of_file(
        &mut allocator,
        runner.clone(),
        "test.clsp",
        &program_text,
    ).expect("should compile");
    for cname in mc.exports.iter() {
        if let Some(cval) = mc.constants_and_values.get(cname) {
            eprintln!("{} = {cval}", decode_string(cname));
        } else {
            todo!();
        }
    }
    todo!();
}
