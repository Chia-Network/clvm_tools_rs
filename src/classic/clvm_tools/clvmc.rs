use std::fs;
use std::fs::File;
use std::io::Write;
use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::Stream;
use crate::classic::clvm::serialize::sexp_to_stream;
use crate::classic::clvm_tools::binutils::{
    assemble_from_ir,
    disassemble
};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;
use crate::classic::clvm_tools::stages::run;

use crate::classic::platform::distutils::log;
use crate::classic::platform::distutils::dep_util::newer;

fn compile_clvm_text(
    allocator: &mut Allocator,
    text: String,
    search_paths: &Vec<String>
) -> Result<NodePtr, EvalErr> {
    m! {
        ir_src <- read_ir(&text).map_err(|s| EvalErr(allocator.null(), s));
        assembled_sexp <- assemble_from_ir(allocator, Rc::new(ir_src));

        let compile_invoke_code = run(allocator);
        input_sexp <- allocator.new_pair(assembled_sexp, allocator.null());
        let run_program = run_program_for_search_paths(search_paths);
        run_program_output <- run_program.run_program(
            allocator, compile_invoke_code, input_sexp, None
        );
        Ok(run_program_output.1)
    }
}

pub fn compile_clvm(input_path: &String, output_path: &String, search_paths: &Vec<String>) -> Result<String, String> {
    let mut allocator = Allocator::new();

    newer(input_path, output_path).and_then(
        |is_newer| if is_newer {
            m! {
                let _ = log::info(format!("clvmcc {} -o {}", input_path, output_path));
                text <- fs::read_to_string(input_path).map_err(
                    |x| format!("error reading {}: {:?}", input_path, x)
                );

                result <- compile_clvm_text(&mut allocator, text, search_paths).map_err(
                    |x| format!("error {} compiling {}", x.1, disassemble(&mut allocator, x.0))
                );
                let mut result_stream = Stream::new(None);
                let _ = sexp_to_stream(&mut allocator, result, &mut result_stream);

                f_ <- File::create(output_path).map_err(|x| {
                    format!("Error writing {}: {:?}", input_path, x)
                });
                let mut f = f_;
                _ <- f.write_all(&result_stream.get_value().hex().as_bytes()).map_err(
                    |_| format!("failed to write to {}", output_path)
                );
                Ok(output_path.to_string())
            }
        } else {
            log::info(format!("skipping {}, compiled recently", input_path));
            Ok(output_path.to_string())
        }
    )
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
