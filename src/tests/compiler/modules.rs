use std::cell::{Ref, RefCell, RefMut};
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
use crate::compiler::comptypes::{CompileErr, CompilerOpts, HasCompilerOptsDelegation};
use crate::compiler::dialect::detect_modern;
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Clone)]
struct TestModuleCompilerOpts {
    opts: Rc<dyn CompilerOpts>,
    written_files: Rc<RefCell<HashMap<String, Vec<u8>>>>,
}

impl TestModuleCompilerOpts {
    pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        TestModuleCompilerOpts {
            opts,
            written_files: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn get_written_file<'a>(&'a self, name: &str) -> Option<Vec<u8>> {
        let files: Ref<'_, HashMap<String, Vec<u8>>> = self.written_files.borrow();
        files.get(name).map(|f| f.to_vec())
    }
}

impl HasCompilerOptsDelegation for TestModuleCompilerOpts {
    fn compiler_opts(&self) -> Rc<dyn CompilerOpts> {
        self.opts.clone()
    }
    fn update_compiler_opts<F: FnOnce(Rc<dyn CompilerOpts>) -> Rc<dyn CompilerOpts>>(
        &self,
        f: F,
    ) -> Rc<dyn CompilerOpts> {
        Rc::new(TestModuleCompilerOpts {
            opts: f(self.opts.clone()),
            ..self.clone()
        })
    }
    fn override_write_new_file(&self, target: &str, content: &[u8]) -> Result<(), CompileErr> {
        let mut wf: RefMut<'_, HashMap<String, Vec<u8>>> = self.written_files.borrow_mut();
        wf.insert(target.to_string(), content.to_vec());
        Ok(())
    }
}

struct HexArgumentOutcome<'a> {
    hexfile: &'a str,
    argument: &'a str,
    outcome: Option<&'a str>,
}

fn test_compile_and_run_program_with_modules(
    filename: &str,
    content: &str,
    runs: &[HexArgumentOutcome],
) {
    let loc = Srcloc::start(filename);
    let parsed: Vec<Rc<SExp>> = parse_sexp(loc.clone(), content.bytes()).expect("should parse");
    let listed = Rc::new(enlist(loc.clone(), &parsed));
    let mut allocator = Allocator::new();
    let nodeptr = convert_to_clvm_rs(&mut allocator, listed.clone()).expect("should convert");
    let dialect = detect_modern(&mut allocator, nodeptr);
    let orig_opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(filename))
        .set_dialect(dialect)
        .set_search_paths(&["resources/tests/module".to_string()]);
    let source_opts = TestModuleCompilerOpts::new(orig_opts);
    let opts: Rc<dyn CompilerOpts> = Rc::new(source_opts.clone());
    let mut symbol_table = HashMap::new();
    let mut includes = Vec::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let _ = compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &content,
        &mut symbol_table,
        &mut includes,
    )
    .expect("should compile");

    for run in runs.iter() {
        let hex_data = source_opts
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

        let assembled_env = assemble(&mut allocator, run.argument).expect("should assemble");
        let run_result = runner.run_program(&mut allocator, compiled_node, assembled_env, None);
        if let Some(res) = &run.outcome {
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
                outcome: Some("3"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13)",
                outcome: None,
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
                outcome: Some("3"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13)",
                outcome: None,
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
                outcome: Some("16"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13 3)",
                outcome: None,
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
                outcome: Some("(+ 39)"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(13 3)",
                outcome: None,
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
                outcome: Some("(0x9df8d4d222276747372a532a1cd736cdd5c6800c39906c9695489d36286ed215 (+ 2 (q . 1)))")
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
                outcome: Some("(0xd85eec1bed9af4d6d161663e846857ae27010ad2a80b3ab8ccbb9fbd2c3bfa46 14 (a (q 16 5 (q . 1)) (c (q (+ 5 (q . 1)) 18 5 (q . 2)) 1)) 0x91a9f6736103e339a1d3b25e9d1dbc57de2bf643494c00f82b462ddf4912b11c 146 (a (q 18 5 (q . 2)) (c (q (+ 5 (q . 1)) 18 5 (q . 2)) 1)))")
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
                outcome: Some("(0x27a343d6617931e67a7eb27a41f7c4650b5fa79d8b5132af1b4eae959bdf2272 (* 2 (q . 13)))")
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
            outcome: Some("13"),
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
            outcome: Some("13"),
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
            outcome: Some("(q 2 3 4 5 6)"),
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
            outcome: Some("()"),
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
            outcome: Some("24"),
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
                outcome: Some("-1"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "(1 ())",
                outcome: Some("1"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "((1 2 3) (1 2 3))",
                outcome: Some("()"),
            },
            HexArgumentOutcome {
                hexfile: hex_filename,
                argument: "((1 2 3) (1 2 4))",
                outcome: Some("-1"),
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
            outcome: Some("6"),
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
            outcome: Some("14"),
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
            outcome: Some("24"),
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
            outcome: Some("1"),
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
            outcome: Some("120"),
        }],
    );
}
