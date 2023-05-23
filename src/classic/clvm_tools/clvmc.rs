use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::rc::Rc;

use tempfile::NamedTempFile;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::Stream;
use crate::classic::clvm::serialize::sexp_to_stream;
use crate::classic::clvm::sexp::proper_list;
use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages::run;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;

use crate::classic::platform::distutils::dep_util::newer;

use crate::compiler::clvm::convert_to_clvm_rs;
use crate::compiler::compiler::compile_file;
use crate::compiler::compiler::{run_optimizer, DefaultCompilerOpts};
use crate::compiler::comptypes::{AcceptedDialect, CompileErr, CompilerOpts};
use crate::compiler::runtypes::RunFailure;

fn include_dialect(
    allocator: &mut Allocator,
    dialects: &HashMap<Vec<u8>, i32>,
    e: &[NodePtr],
) -> Option<i32> {
    if let (SExp::Atom(inc), SExp::Atom(name)) = (allocator.sexp(e[0]), allocator.sexp(e[1])) {
        if allocator.buf(&inc) == "include".as_bytes().to_vec() {
            if let Some(dialect) = dialects.get(allocator.buf(&name)) {
                return Some(*dialect);
            }
        }
    }

    None
}

pub fn write_sym_output(
    compiled_lookup: &HashMap<String, String>,
    path: &str,
) -> Result<(), String> {
    let output = serde_json::to_string(compiled_lookup)
        .map_err(|_| "failed to serialize to json".to_string())?;

    fs::write(path, output)
        .map_err(|_| format!("failed to write {path}"))
        .map(|_| ())
}

pub fn detect_modern(allocator: &mut Allocator, sexp: NodePtr) -> AcceptedDialect {
    let mut dialects = HashMap::new();
    dialects.insert("*standard-cl-21*".as_bytes().to_vec(), 21);
    dialects.insert("*standard-cl-22*".as_bytes().to_vec(), 22);
    dialects.insert("*standard-cl-23*".as_bytes().to_vec(), 23);

    let mut result = Default::default();

    if let Some(l) = proper_list(allocator, sexp, true) {
        for elt in l.iter() {
            let detect_modern_result = detect_modern(allocator, *elt);
            if detect_modern_result.stepping.is_some() {
                result = detect_modern_result;
                break;
            }

            match proper_list(allocator, *elt, true) {
                None => {
                    continue;
                }

                Some(e) => {
                    if e.len() != 2 {
                        continue;
                    }

                    if let Some(dialect) = include_dialect(allocator, &dialects, &e) {
                        result.stepping = Some(dialect);
                        break;
                    }
                }
            }
        }
    }

    result
}

pub fn compile_clvm_text_maybe_opt(
    allocator: &mut Allocator,
    do_optimize: bool,
    opts: Rc<dyn CompilerOpts>,
    symbol_table: &mut HashMap<String, String>,
    text: &str,
    input_path: &str,
    classic_with_opts: bool,
) -> Result<NodePtr, EvalErr> {
    let ir_src = read_ir(text).map_err(|s| EvalErr(allocator.null(), s.to_string()))?;
    let assembled_sexp = assemble_from_ir(allocator, Rc::new(ir_src))?;
    let dialect = detect_modern(allocator, assembled_sexp);
    if let Some(dialect) = dialect.stepping {
        let runner = Rc::new(DefaultProgramRunner::new());
        let opts = opts
            .set_optimize(do_optimize)
            .set_frontend_opt(dialect > 21);

        let unopt_res = compile_file(allocator, runner.clone(), opts, text, symbol_table);
        let res = if do_optimize {
            unopt_res.and_then(|x| run_optimizer(allocator, runner, Rc::new(x)))
        } else {
            unopt_res.map(Rc::new)
        };

        res.and_then(|x| {
            convert_to_clvm_rs(allocator, x).map_err(|r| match r {
                RunFailure::RunErr(l, x) => CompileErr(l, x),
                RunFailure::RunExn(l, x) => CompileErr(l, x.to_string()),
            })
        })
        .map_err(|s| EvalErr(allocator.null(), s.1))
    } else {
        let compile_invoke_code = run(allocator);
        let input_sexp = allocator.new_pair(assembled_sexp, allocator.null())?;
        let run_program = run_program_for_search_paths(input_path, &opts.get_search_paths(), false);
        if classic_with_opts {
            run_program.set_compiler_opts(Some(opts));
        }
        let run_program_output =
            run_program.run_program(allocator, compile_invoke_code, input_sexp, None)?;
        Ok(run_program_output.1)
    }
}

pub fn compile_clvm_text(
    allocator: &mut Allocator,
    opts: Rc<dyn CompilerOpts>,
    symbol_table: &mut HashMap<String, String>,
    text: &str,
    input_path: &str,
    classic_with_opts: bool,
) -> Result<NodePtr, EvalErr> {
    compile_clvm_text_maybe_opt(
        allocator,
        true,
        opts,
        symbol_table,
        text,
        input_path,
        classic_with_opts,
    )
}

pub fn compile_clvm_inner(
    allocator: &mut Allocator,
    opts: Rc<dyn CompilerOpts>,
    symbol_table: &mut HashMap<String, String>,
    filename: &str,
    text: &str,
    result_stream: &mut Stream,
    classic_with_opts: bool,
) -> Result<(), String> {
    let result = compile_clvm_text(
        allocator,
        opts,
        symbol_table,
        text,
        filename,
        classic_with_opts,
    )
    .map_err(|x| format!("error {} compiling {}", x.1, disassemble(allocator, x.0)))?;
    sexp_to_stream(allocator, result, result_stream);
    Ok(())
}

pub fn compile_clvm(
    input_path: &str,
    output_path: &str,
    search_paths: &[String],
    symbol_table: &mut HashMap<String, String>,
) -> Result<String, String> {
    let mut allocator = Allocator::new();

    let compile = newer(input_path, output_path).unwrap_or(true);
    let mut result_stream = Stream::new(None);

    if compile {
        let text = fs::read_to_string(input_path)
            .map_err(|x| format!("error reading {input_path}: {x:?}"))?;
        let opts = Rc::new(DefaultCompilerOpts::new(input_path)).set_search_paths(search_paths);

        compile_clvm_inner(
            &mut allocator,
            opts,
            symbol_table,
            input_path,
            &text,
            &mut result_stream,
            false,
        )?;

        let output_path_obj = Path::new(output_path);
        let output_dir = output_path_obj
            .parent()
            .map(Ok)
            .unwrap_or_else(|| Err("could not get parent of output path"))?;

        let target_data = result_stream.get_value().hex();

        // Try to detect whether we'd put the same output in the output file.
        // Don't proceed if true.
        if let Ok(prev_content) = fs::read_to_string(output_path) {
            let prev_trimmed = prev_content.trim();
            let trimmed = target_data.trim();
            if prev_trimmed == trimmed {
                // It's the same program, bail regardless.
                return Ok(output_path.to_string());
            }
        }

        // Make the contents appear atomically so that other test processes
        // won't mistake an empty file for intended output.
        let mut temp_output_file = NamedTempFile::new_in(output_dir).map_err(|e| {
            format!("error creating temporary compiler output for {input_path}: {e:?}")
        })?;

        temp_output_file
            .write_all(target_data.as_bytes())
            .map_err(|_| format!("failed to write to {:?}", temp_output_file.path()))?;

        temp_output_file.persist(output_path).map_err(|e| {
            format!("error persisting temporary compiler output {output_path}: {e:?}")
        })?;
    }

    Ok(output_path.to_string())
}

// export function find_files(path: str = ""){
//   const r: string[] = [];
//   for(const {dirpath, filenames} of os_walk(path)){
//     for(const filename of filenames){
//       if(filename.endsWith(".clvm")){
//         const full_path = path_join(dirpath, filename);
//         const target = `${full_path}.hex}`;
//         compile_clvm(full_path, target);
//         r.push(target);
//       }
//     }
//   }
//   return r;
// }
