// import {
//   Bytes,
//   CLVMObject,
//   EvalError,
//   OPERATOR_LOOKUP as ORIGINAL_OPERATOR_LOOKUP,
//   OperatorDict,
//   SExp,
//   str,
//   t,
//   b,
// } from "clvm";
// import {read_ir} from "../../ir/reader";
// import {write_ir_to_stream} from "../../ir/writer";
// import {assemble_from_ir, disassemble_to_ir} from "../../clvm_tools/binutils";
// import {
//   run_program as run_program_0, RunProgramOption,
// } from "../stage_0";
// import {make_do_com} from "./compile";
// import {make_do_opt} from "./optimize";
// import {FileStream, fs_read, Path} from "../../platform/io";

// export function do_read(args: SExp){
//   const filename = args.first().atom as Bytes;
//   const s = fs_read(filename.decode());
//   const ir_sexp = SExp.to(read_ir(s));
//   const sexp = assemble_from_ir(ir_sexp);
//   return t(1, sexp);
// }

// export function do_write(args: SExp){
//   const filename = args.first().atom as Bytes;
//   const data = args.rest().first();
//   const f = new FileStream(filename.decode());
//   write_ir_to_stream(disassemble_to_ir(data, {}), f);
//   f.flush();
//   return t(1, SExp.to(0));
// }

// export function run_program_for_search_paths(search_paths: str[]){
//   const do_full_path_for_name = (args: SExp) => {
//     const filename = args.first().atom as Bytes;
//     for(const path of search_paths){
//       const f_path = Path.join(path, filename.decode());
//       if(f_path.is_file()){
//         return t(1, SExp.to(b(f_path.toString())));
//       }
//     }
//     throw new EvalError(`can't open ${filename}`, args);
//   };
  
//   const _operator_lookup = OperatorDict(ORIGINAL_OPERATOR_LOOKUP as any);
  
//   const run_program = (
//     program: SExp,
//     args: CLVMObject,
//     option?: RunProgramOption,
//   ) => {
//     const operator_lookup = (option && option.operator_lookup) || _operator_lookup;
//     option = option ? {...option, operator_lookup} : {operator_lookup};
//     return run_program_0(program, args, option);
//   };
  
//   const BINDINGS = {
//     [b("com").hex()]: make_do_com(run_program),
//     [b("opt").hex()]: make_do_opt(run_program),
//     [b("_full_path_for_name").hex()]: do_full_path_for_name,
//     [b("_read").hex()]: do_read,
//     [b("_write").hex()]: do_write,
//   };
  
//   Object.entries(BINDINGS).forEach(([key, value]) => {
//     (_operator_lookup as Record<str, unknown>)[key] = value;
//   });
  
//   return run_program;
// }
