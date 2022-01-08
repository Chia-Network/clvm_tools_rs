// import {assemble} from "./binutils";
// import {run_program} from "../stages/stage_0";
// import {match} from "./pattern_match";
// import {Bytes, h, None, SExp, t} from "clvm";

// /*
// # CURRY_OBJ_CODE contains compiled code from the output of the following:
// # run -i clvm_runtime '(mod (F . args) (include curry.clvm) (curry_args F args))'
// # the text below has been hand-optimized to replace `((c (q X) Y))` with `(a (q X) Y)`
// # and `(q 0)` with `0`
//  */
// export const CURRY_OBJ_CODE = assemble(
//   // eslint-disable-next-line max-len
//   "(a (q #a 4 (c 2 (c 5 (c 7 0)))) (c (q (c (q . 2) (c (c (q . 1) 5) (c (a 6 (c 2 (c 11 (q 1)))) 0))) #a (i 5 (q 4 (q . 4) (c (c (q . 1) 9) (c (a 6 (c 2 (c 13 (c 11 0)))) 0))) (q . 11)) 1) 1))"
// );

// export function curry(program: SExp, args: SExp){
//   /*
//     ;; A "curry" binds values to a function, making them constant,
//     ;; and returning a new function that returns fewer arguments (since the
//     ;; arguments are now fixed).
//     ;; Example: (defun add2 (V1 V2) (+ V1 V2))  ; add two values
//     ;; (curry add2 15) ; this yields a function that accepts ONE argument, and adds 15 to it
//     `program`: an SExp
//     `args`: an SExp that is a list of constants to be bound to `program`
//    */
//   args = SExp.to(t(program, args));
//   return run_program(CURRY_OBJ_CODE, args);
// }

// export const UNCURRY_PATTERN_FUNCTION = assemble("(a (q . (: . function)) (: . core))");
// export const UNCURRY_PATTERN_CORE = assemble("(c (q . (: . parm)) (: . core))");

// export function uncurry(curried_program: SExp){
//   let r = match(UNCURRY_PATTERN_FUNCTION, curried_program);
//   if(!r){
//     return r;
//   }

//   const f = r["function"];
//   let core = r["core"];

//   const args: SExp[] = [];
//   // eslint-disable-next-line no-constant-condition
//   while(true){
//     r = match(UNCURRY_PATTERN_CORE, core);
//     if(!r){
//       break;
//     }
//     args.push(r["parm"]);
//     core = r["core"];
//   }

//   if((core.as_javascript() as Bytes).equal_to(h("0x01"))){
//     return t(f, SExp.to(args));
//   }
//   return None;
// }
