// import {
//   run_program as default_run_program,
//   OPERATOR_LOOKUP,
//   OperatorDict,
//   EvalError,
//   None,
//   SExp,
//   CLVMObject,
//   TOperatorDict,
//   int,
//   TPreEvalF,
//   Bytes,
// } from "clvm";
// import * as binutils from "../clvm_tools/binutils";

// export const run = binutils.assemble("(a 2 3)");
// export const brun = run;

// export type RunProgramOption = Partial<{
//   operator_lookup: TOperatorDict;
//   max_cost: int|None;
//   pre_eval_f: TPreEvalF|None;
//   strict: boolean;
// }>;

// export function run_program(
//   program: SExp,
//   args: CLVMObject,
//   option?: RunProgramOption,
// ){
//   let operator_lookup = (option && option.operator_lookup) || OPERATOR_LOOKUP;
//   const strict = (option && option.strict) || false;
//   const max_cost = (option && typeof option.max_cost === "number") ? option.max_cost : None;
//   const pre_eval_f = (option && option.pre_eval_f) ? option.pre_eval_f : None;

//   if(strict){
//     const fatal_error = (op: Bytes, args: SExp) => {
//       throw new EvalError("unimplemented operator", SExp.to(op));
//     }
//     operator_lookup = OperatorDict(operator_lookup as any, undefined, undefined, fatal_error);
//   }

//   return default_run_program(program, args, operator_lookup, max_cost, pre_eval_f);
// }

// export type TRunProgram = typeof run_program;
