use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{Bytes, Stream, BytesFromType};
use crate::classic::clvm::serialize::sexp_to_stream;
use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages::run;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;

use crate::classic::platform::distutils::dep_util::newer;

use crate::compiler::clvm::convert_to_clvm_rs;
use crate::compiler::compiler::compile_file;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::dialect::detect_modern;
use crate::compiler::optimize::maybe_finalize_program_via_classic_optimizer;
use crate::compiler::runtypes::RunFailure;
use crate::util::gentle_overwrite;

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
    // Now the stepping is optional (None for classic) but we may communicate
    // other information in dialect as well.
    //
    // I think stepping is a good name for the number below as dialect is going
    // to get more members that are somewhat independent.
    if let Some(stepping) = dialect.stepping {
        let runner = Rc::new(DefaultProgramRunner::new());
        let opts = opts
            .set_dialect(dialect)
            .set_optimize(do_optimize || stepping > 22) // Would apply to cl23
            .set_frontend_opt(stepping == 22);

        let unopt_res = compile_file(allocator, runner.clone(), opts.clone(), text, symbol_table);
        let res = unopt_res.and_then(|x| {
            maybe_finalize_program_via_classic_optimizer(allocator, runner, opts, do_optimize, &x)
        });

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
        opts.clone(),
        symbol_table,
        text,
        filename,
        classic_with_opts,
    )
    .map_err(|x| {
        format!(
            "error {} compiling {}",
            x.1,
            disassemble(allocator, x.0, opts.disassembly_ver())
        )
    })?;
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

        result_stream.write(Bytes::new(Some(BytesFromType::Raw(b"\n".to_vec()))));
        let target_data = result_stream.get_value().hex();

        // Try to detect whether we'd put the same output in the output file.
        // Don't proceed if true.
        gentle_overwrite(input_path, output_path, &target_data)?;
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
