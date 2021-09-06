// import {log, dep_util} from "../platform/distutils";
// import {FileStream, fs_read, os_walk, path_join} from "../platform/io";
// import * as reader from "../ir/reader";
// import * as binutils from "./binutils";
// import * as stage_2 from "../stages/stage_2";
// import {SExp, str, t} from "clvm";

// export function compile_clvm_text(text: str, search_paths: str[]){
//   const ir_src = reader.read_ir(text);
//   const assembled_sexp = binutils.assemble_from_ir(ir_src);
  
//   const input_sexp = SExp.to(t(assembled_sexp, []));
//   const run_program = stage_2.run_program_for_search_paths(search_paths);
//   const run_program_output = run_program(stage_2.run, input_sexp);
//   return run_program_output[1] as SExp;
// }

// export function compile_clvm(input_path: str, output_path: str, search_paths: str[] = []){
//   if(dep_util.newer(input_path, output_path)){
//     log.info(`clvmcc ${input_path} -o ${output_path}`);
//     const text = fs_read(input_path);
//     const result = compile_clvm_text(text, search_paths);
//     const hex = result.as_bin().hex();
    
//     const f = new FileStream(output_path);
//     f.write(hex);
//     f.write("\n");
//     f.flush();
//   }
//   else{
//     log.info(`skipping ${input_path}, compiled recently`);
//   }
  
//   return output_path;
// }

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
