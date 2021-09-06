// import {None, SExp, t, to_sexp_f} from "clvm";
// import * as binutils from "../../clvm_tools/binutils";
// import {TRunProgram} from "../stage_0";

// /*
// "function" is used in front of a constant uncompiled
// program to indicate we want this program literal to be
// compiled and quoted, so it can be passed as an argument
// to a compiled clvm program.
// EG: (function (+ 20 @)) should return (+ (q . 20) 1) when run.
// Thus (opt (com (q . (function (+ 20 @)))))
// should return (q . (+ (q . 20) 1))
// (function PROG) => (opt (com (q . PROG) (q . MACROS)))
// We have to use "opt" as (com PROG) might leave
// some partial "com" operators in there and our
// goals is to compile PROG as much as possible.
//  */

// export const DEFAULT_MACROS_SRC = [
//   `
//     ; we have to compile this externally, since it uses itself
//     ;(defmacro defmacro (name params body)
//     ;    (qq (list (unquote name) (mod (unquote params) (unquote body))))
//     ;)
//     (q . ("defmacro"
//        (c (q . "list")
//           (c (f 1)
//              (c (c (q . "mod")
//                    (c (f (r 1))
//                       (c (f (r (r 1)))
//                          (q . ()))))
//                 (q . ()))))))
//     `,
//   `
//     ;(defmacro list ARGS
//     ;    ((c (mod args
//     ;        (defun compile-list
//     ;               (args)
//     ;               (if args
//     ;                   (qq (c (unquote (f args))
//     ;                         (unquote (compile-list (r args)))))
//     ;                   ()))
//     ;            (compile-list args)
//     ;        )
//     ;        ARGS
//     ;    ))
//     ;)
//     (q "list"
//         (a (q #a (q #a 2 (c 2 (c 3 (q))))
//                  (c (q #a (i 5
//                              (q #c (q . 4)
//                                    (c 9 (c (a 2 (c 2 (c 13 (q))))
//                                            (q)))
//                              )
//                              (q 1))
//                            1)
//                     1))
//             1))
//     `,
//   `
//     (defmacro function (BODY)
//         (qq (opt (com (q . (unquote BODY))
//                  (qq (unquote (macros)))
//                  (qq (unquote (symbols)))))))
//     `,
//   `
//     (defmacro if (A B C)
//       (qq (a
//           (i (unquote A)
//              (function (unquote B))
//              (function (unquote C)))
//           @)))`,
// ];

// let DEFAULT_MACRO_LOOKUP: SExp|None = None;

// export function build_default_macro_lookup(eval_f: TRunProgram){
//   const run = binutils.assemble("(a (com 2 3) 1)");
//   for(const macro_src of DEFAULT_MACROS_SRC){
//     const macro_sexp = binutils.assemble(macro_src);
//     const env = SExp.to(t(macro_sexp, DEFAULT_MACRO_LOOKUP));
//     const new_macro = eval_f(run, env)[1];
//     DEFAULT_MACRO_LOOKUP = new_macro.cons(DEFAULT_MACRO_LOOKUP);
//   }
//   return DEFAULT_MACRO_LOOKUP;
// }

// export function default_macro_lookup(eval_f: TRunProgram){
//   if(DEFAULT_MACRO_LOOKUP === None){
//     DEFAULT_MACRO_LOOKUP = to_sexp_f([]);
//     DEFAULT_MACRO_LOOKUP = build_default_macro_lookup(eval_f);
//   }
//   return DEFAULT_MACRO_LOOKUP;
// }
