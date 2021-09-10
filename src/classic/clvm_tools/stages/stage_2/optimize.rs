use std::rc::Rc;
use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::Response;
use clvm_rs::run_program::OperatorHandler;

use crate::classic::clvm::{
    non_nil,
    rest
};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

// import {h, Bytes, KEYWORD_TO_ATOM, None, SExp, t} from "clvm";
// import {match} from "../../clvm_tools/pattern_match";
// import {assemble} from "../../clvm_tools/binutils";
// import {NodePath, LEFT, RIGHT} from "../../clvm_tools/NodePath";
// import {quote} from "./helpers";
// import {TRunProgram} from "../stage_0";
// import {print} from "../../platform/print";

// export const QUOTE_ATOM = KEYWORD_TO_ATOM["q"];
// export const APPLY_ATOM = KEYWORD_TO_ATOM["a"];
// export const FIRST_ATOM = KEYWORD_TO_ATOM["f"];
// export const REST_ATOM = KEYWORD_TO_ATOM["r"];
// export const CONS_ATOM = KEYWORD_TO_ATOM["c"];
// export const RAISE_ATOM = KEYWORD_TO_ATOM["x"];

pub struct DoOptProg<'a> {
    runner: Rc<dyn TRunProgram<'a>>
}

// const DEBUG_OPTIMIZATIONS = 0;

pub fn seems_constant_tail(allocator: &'a mut Allocator, sexp_: NodePtr) -> bool {
    let mut sexp = sexp_;

    loop {
        match allocator.sexp(sexp) {
            SExp::Pair(l,r) => {
                if !seems_constant(allocator, l) {
                    return false;
                }

                sexp = r;
            },
            _ => { return true; }
        }
    }
}

pub fn seems_constant(allocator: &'a mut Allocator, sexp: NodePtr) -> bool {
    match allocator.sexp(sexp) {
        SExp::Atom(b) => { return !non_nil(sexp); },
        SExp::Pair(operator,r) => {
            match allocator.sexp(operator) {
                SExp::Atom(b) => {
                    let atom = allocator.buf(b);
                    if atom.len() == 1 && atom[0] == 1 {
                        return true;
                    } else if atom.len() == 1 && atom[0] == 8 {
                        return false;
                    } else {
                        return true;
                    }
                },
                SExp::Pair(l,r) => {
                    if (!seems_constant(allocator, operator)) {
                        return false;
                    }

                    if !seems_constant_tail(allocator, r).
                        unwrap_or_else(|| false)
                    {
                        return false;
                    }
                }
            }
        }
    }

    return true;
}


struct ConstantOptimizer {
    runner: Rc<dyn TRunProgram>
}

impl<'a> OperatorHandler for ConstantOptimizer {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, r: NodePtr, max_cost: Cost) -> Response {
        /*
         * If the expression does not depend upon @ anywhere,
         * it's a constant. So we can simply evaluate it and
         * return the quoted result.
         */
        if seems_constant(r) && non_nil(r) {
            return self.runner.run_program(allocator, r, max_cost, None).
                map(|res| res.1).and_then(|r1| quote(allocator, r1));
        }

        return Reduction(1, r);
    }
}

pub fn is_args_call(allocator: &'a mut Allocator, r: NodePtr) -> bool {
    match allocator.sexp(r) {
        SExp::Atom(b) => {
            let buf = allocator.buf(b);
            return buf.len() == 1 && buf[0] == 1;
        },
        _ => { return false; }
    }
}

pub fn CONS_Q_A_OPTIMIZER_PATTERN<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(allocator, "(a (q . (: . sexp)) (: . args))").unwrap();
}

pub fn cons_q_a_optimizer(
    allocator: &'a mut Allocator,
    r: NodePtr,
    eval_f: TRunProgram
) -> NodePtr {
    /*
     * This applies the transform
     * (a (q . SEXP) @) => SEXP
     */
    
    const t1 = match(CONS_Q_A_OPTIMIZER_PATTERN, r);
    if(t1 && is_args_call(t1["args"])){
        return t1["sexp"];
    }
    return r;
}

// export const CONS_PATTERN = assemble("(c (: . first) (: . rest)))");

// export function cons_f(args: SExp){
//   const t = match(CONS_PATTERN, args);
//   if(t){
//     return t["first"];
//   }
//   return SExp.to([h(FIRST_ATOM), args]);
// }

// export function cons_r(args: SExp){
//   const t = match(CONS_PATTERN, args);
//   if(t){
//     return t["rest"];
//   }
//   return SExp.to([h(REST_ATOM), args]);
// }

// export function path_from_args(sexp: SExp, new_args: SExp): SExp {
//   const v = sexp.as_int();
//   if(v <= 1){
//     return new_args;
//   }
//   sexp = SExp.to(v >> 1);
//   if(v & 1){
//     return path_from_args(sexp, cons_r(new_args));
//   }
//   return path_from_args(sexp, cons_f(new_args));
// }

// export function sub_args(sexp: SExp, new_args: SExp): SExp {
//   if(sexp.nullp() || !sexp.listp()){
//     return path_from_args(sexp, new_args);
//   }
  
//   let first = sexp.first();
//   if(first.listp()){
//     first = sub_args(first, new_args);
//   }
//   else{
//     const op = first.atom as Bytes;
//     if(op.hex() === QUOTE_ATOM){
//       return sexp;
//     }
//   }
  
//   const args = [first];
//   for(const _ of sexp.rest().as_iter()){
//     args.push(sub_args(_, new_args));
//   }
  
//   return SExp.to(args);
// }

// export const VAR_CHANGE_OPTIMIZER_CONS_EVAL_PATTERN = assemble("(a (q . (: . sexp)) (: . args))");

// export function var_change_optimizer_cons_eval(r: SExp, eval_f: TRunProgram){
//   /*
//     This applies the transform
//     (a (q . (op SEXP1...)) (ARGS)) => (q . RET_VAL) where ARGS != @
//     via
//     (op (a SEXP1 (ARGS)) ...) (ARGS)) and then "children_optimizer" of this.
//     In some cases, this can result in a constant in some of the children.

//     If we end up needing to push the "change of variables" to only one child, keep
//     the optimization. Otherwise discard it.
//    */
  
//   const t1 = match(VAR_CHANGE_OPTIMIZER_CONS_EVAL_PATTERN, r);
  
//   if(t1 === None){
//     return r;
//   }
  
//   const original_args = t1["args"];
//   const original_call = t1["sexp"];
  
//   const new_eval_sexp_args = sub_args(original_call, original_args);
  
//   // Do not iterate into a quoted value as if it were a list
//   if(seems_constant(new_eval_sexp_args)){
//     const opt_operands = optimize_sexp(new_eval_sexp_args, eval_f);
//     return SExp.to(opt_operands);
//   }
  
//   const new_operands: SExp[] = [];
//   for(const item of new_eval_sexp_args.as_iter()){
//     new_operands.push(item);
//   }
//   const opt_operands: SExp[] = new_operands.map(_ => optimize_sexp(_, eval_f));
//   const non_constant_count = opt_operands.reduce((acc, val) => {
//     return acc + (val.listp() && !val.first().equal_to(h(QUOTE_ATOM)) ? 1 : 0);
//   }, 0);
//   if(non_constant_count < 1){
//     return SExp.to(opt_operands);
//   }
//   return r;
// }

// export function children_optimizer(r: SExp, eval_f: TRunProgram){
//   // Recursively apply optimizations to all non-quoted child nodes.
//   if(!r.listp()){
//     return r;
//   }
//   const operator = r.first();
//   if(!operator.listp()){
//     const op = operator.atom as Bytes;
//     if(op.hex() === QUOTE_ATOM){
//       return r;
//     }
//   }
//   const optimized: SExp[] = [];
//   for(const _ of r.as_iter()){
//     optimized.push(optimize_sexp(_, eval_f));
//   }
//   return SExp.to(optimized);
// }

// export const CONS_OPTIMIZER_PATTERN_FIRST = assemble("(f (c (: . first) (: . rest)))")
// export const CONS_OPTIMIZER_PATTERN_REST = assemble("(r (c (: . first) (: . rest)))")

// export function cons_optimizer(r: SExp, eval_f: TRunProgram){
//   /*
//     This applies the transform
//     (f (c A B)) => A
//     and
//     (r (c A B)) => B
//    */
//   let t1 = match(CONS_OPTIMIZER_PATTERN_FIRST, r);
//   if(t1){
//     return t1["first"];
//   }
//   t1 = match(CONS_OPTIMIZER_PATTERN_REST, r);
//   if(t1){
//     return t1["rest"];
//   }
//   return r;
// }

// export const FIRST_ATOM_PATTERN = assemble("(f ($ . atom))")
// export const REST_ATOM_PATTERN = assemble("(r ($ . atom))")

// export function path_optimizer(r: SExp, eval_f: TRunProgram){
//   /*
//     This applies the transform
//     (f N) => A
//     and
//     (r N) => B
//    */
//   let t1 = match(FIRST_ATOM_PATTERN, r);
//   if(t1 && non_nil(t1["atom"])){
//     let node = new NodePath(t1["atom"].as_int());
//     node = node.add(LEFT);
//     return SExp.to(node.as_short_path());
//   }
  
//   t1 = match(REST_ATOM_PATTERN, r);
//   if(t1 && non_nil(t1["atom"])){
//     let node = new NodePath(t1["atom"].as_int());
//     node = node.add(RIGHT);
//     return SExp.to(node.as_short_path());
//   }
//   return r;
// }

// export const QUOTE_PATTERN_1 = assemble("(q . 0)");

// export function quote_null_optimizer(r: SExp, eval_f: TRunProgram){
//   // This applies the transform `(q . 0)` => `0`
//   const t1 = match(QUOTE_PATTERN_1, r);
//   if(t1){
//     return SExp.to(0);
//   }
//   return r;
// }

// export const APPLY_NULL_PATTERN_1 = assemble("(a 0 . (: . rest))");

// export function apply_null_optimizer(r: SExp, eval_f: TRunProgram){
//   // This applies the transform `(a 0 ARGS)` => `0`
//   const t1 = match(APPLY_NULL_PATTERN_1, r);
//   if(t1){
//     return SExp.to(0);
//   }
//   return r;
// }

impl<'a> OperatorHandler for DoOptProg<'a> {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, r: NodePtr, max_cost: Cost) -> Response {
        /*
         * Optimize an s-expression R written for clvm to R_opt where
         * (a R args) == (a R_opt args) for ANY args.
         */
        match allocator.sexp(sexp) {
            SExp::Atom(_) => { return Response(1, r); }
            _ => { }
        }

        const OPTIMIZERS = vec!(
            cons_optimizer,
            constant_optimizer,
            cons_q_a_optimizer,
            var_change_optimizer_cons_eval,
            children_optimizer,
            path_optimizer,
            quote_null_optimizer,
            apply_null_optimizer,
        );

        while(r.listp()){
            const start_r = r as SExp;
            let opt: typeof OPTIMIZERS extends Array<infer T> ? T : never = OPTIMIZERS[0];
            for(opt of OPTIMIZERS){
                r = opt(r, eval_f);
                if(!start_r.equal_to(r)){
                    break;
                }
            }
            if(start_r.equal_to(r)){
                return r;
            }
            if(DEBUG_OPTIMIZATIONS){
                print(`OPT-${opt.name}[${start_r}] => ${r}`);
            }
        }

        return r;
    }
}

pub fn make_do_opt(runner: Rc<dyn TRunProgram>) -> DoOptProg {
    return DoOptProg::new(runner);
}
