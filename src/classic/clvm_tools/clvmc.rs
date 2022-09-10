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
use crate::compiler::compiler::run_optimizer;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompileErr;
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::runtypes::RunFailure;

fn include_dialect(
    allocator: &mut Allocator,
    dialects: &HashMap<Vec<u8>, i32>,
    e: &Vec<NodePtr>,
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

pub fn detect_modern(allocator: &mut Allocator, sexp: NodePtr) -> Option<i32> {
    let mut dialects = HashMap::new();
    dialects.insert("*standard-cl-21*".as_bytes().to_vec(), 21);
    dialects.insert("*standard-cl-22*".as_bytes().to_vec(), 22);

    proper_list(allocator, sexp, true).and_then(|l| {
        for elt in l.iter() {
            if let Some(dialect) = detect_modern(allocator, *elt) {
                return Some(dialect);
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
                        return Some(dialect);
                    }
                }
            }
        }

        None
    })
}

fn compile_clvm_text(
    allocator: &mut Allocator,
    search_paths: &Vec<String>,
    symbol_table: &mut HashMap<String, String>,
    text: &String,
    input_path: &String,
) -> Result<NodePtr, EvalErr> {
    let ir_src = read_ir(&text).map_err(|s| EvalErr(allocator.null(), s))?;
    let assembled_sexp = assemble_from_ir(allocator, Rc::new(ir_src))?;

    if let Some(dialect) = detect_modern(allocator, assembled_sexp) {
        let runner = Rc::new(DefaultProgramRunner::new());
        let opts = Rc::new(DefaultCompilerOpts::new(&input_path))
            .set_optimize(true)
            .set_frontend_opt(dialect > 21)
            .set_search_paths(&search_paths);

        let unopt_res = compile_file(allocator, runner.clone(), opts.clone(), &text, symbol_table);
        let res = unopt_res.and_then(|x| run_optimizer(allocator, runner, Rc::new(x)));

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
        let run_program = run_program_for_search_paths(search_paths);
        let run_program_output =
            run_program.run_program(allocator, compile_invoke_code, input_sexp, None)?;
        Ok(run_program_output.1)
    }
}

pub fn compile_clvm_inner(
    allocator: &mut Allocator,
    search_paths: &Vec<String>,
    symbol_table: &mut HashMap<String, String>,
    filename: &String,
    text: &String,
    result_stream: &mut Stream,
) -> Result<(), String> {
    let result = compile_clvm_text(allocator, search_paths, symbol_table, text, filename)
        .map_err(|x| format!("error {} compiling {}", x.1, disassemble(allocator, x.0)))?;
    sexp_to_stream(allocator, result, result_stream);
    Ok(())
}

pub fn compile_clvm(
    input_path: &String,
    output_path: &String,
    search_paths: &Vec<String>,
    symbol_table: &mut HashMap<String, String>,
) -> Result<String, String> {
    let mut allocator = Allocator::new();

    let compile = newer(input_path, output_path).unwrap_or_else(|_| true);
    let mut result_stream = Stream::new(None);

    if compile {
        let text = fs::read_to_string(input_path)
            .map_err(|x| format!("error reading {}: {:?}", input_path, x))?;

        let _ = compile_clvm_inner(
            &mut allocator,
            search_paths,
            symbol_table,
            input_path,
            &text,
            &mut result_stream,
        )?;

        let output_path_obj = Path::new(output_path);
        let output_dir = output_path_obj
            .parent()
            .map(|p| Ok(p))
            .unwrap_or_else(|| Err("could not get parent of output path"))?;

        let target_data = result_stream.get_value().hex();

        // Try to detect whether we'd put the same output in the output file.
        // Don't proceed if true.
        if let Ok(prev_content) = fs::read_to_string(output_path.clone()) {
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
            format!(
                "error creating temporary compiler output for {}: {:?}",
                input_path, e
            )
        })?;

        let _ = temp_output_file
            .write_all(&target_data.as_bytes())
            .map_err(|_| format!("failed to write to {:?}", temp_output_file.path()))?;

        temp_output_file.persist(output_path.clone()).map_err(|e| {
            format!(
                "error persisting temporary compiler output {}: {:?}",
                output_path, e
            )
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
