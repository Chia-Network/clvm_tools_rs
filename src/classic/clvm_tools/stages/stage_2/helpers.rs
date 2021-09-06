// import {CastableType, KEYWORD_TO_ATOM, SExp, t, b, h} from "clvm";
// import {TOP} from "../../clvm_tools/NodePath";

// export const QUOTE_ATOM = KEYWORD_TO_ATOM["q"];
// export const APPLY_ATOM = KEYWORD_TO_ATOM["a"];

// export function quote(sexp: CastableType){
//   // quoted list as a python list, not as an sexp
//   return t(h(QUOTE_ATOM), sexp);
// }

// // In original python code, the name of this function is `eval`,
// // but since the name `eval` cannot be used in typescript context, change the name to `evaluate`.
// export function evaluate(prog: SExp, args: CastableType){
//   return SExp.to([h(APPLY_ATOM), prog, args]);
// }

// export function run(prog: SExp, macro_lookup: CastableType){
//   /*
//     PROG => (e (com (q . PROG) (mac)) ARGS)
    
//     The result can be evaluated with the stage_com eval
//     function.
//    */
//   const args = TOP.as_path();
//   const mac = quote(macro_lookup);
//   return evaluate(SExp.to([b("com"), prog, mac]), args);
// }

// export function brun(prog: SExp, args: CastableType){
//   return evaluate(SExp.to(quote(prog)), quote(args));
// }
