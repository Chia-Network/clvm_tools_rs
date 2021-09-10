use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm_tools::NodePath::TOP;

lazy_static! {
    pub static ref QUOTE_ATOM : Vec<u8> = vec!(1);
    pub static ref APPLY_ATOM : Vec<u8> = vec!(2);
    pub static ref com_atom : Vec<u8> = vec!('c' as u8, 'o' as u8, 'm' as u8);
}

pub fn quote<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> Result<NodePtr,EvalErr> {
    return allocator.new_atom(&QUOTE_ATOM).
        and_then(|q| allocator.new_pair(q,sexp));
}

// In original python code, the name of this function is `eval`,
// but since the name `eval` cannot be used in typescript context, change the name to `evaluate`.
pub fn evaluate<'a>(allocator: &'a mut Allocator, prog: NodePtr, args: NodePtr) -> Result<NodePtr, EvalErr> {
    return allocator.new_atom(&APPLY_ATOM).and_then(|a| {
        return allocator.new_pair(args, allocator.null()).and_then(|args_tail| {
            return allocator.new_pair(prog, args_tail).and_then(|all_args| {
                return allocator.new_pair(a, all_args);
            });
        });
    });
}

pub fn run<'a>(allocator: &'a mut Allocator, prog: NodePtr, macro_lookup: NodePtr) -> Result<NodePtr, EvalErr> {
    /*
     * PROG => (e (com (q . PROG) (mac)) ARGS)
     *
     * The result can be evaluated with the stage_com eval
     * function.
     */
    let args = TOP.as_path();
    return quote(allocator, macro_lookup).and_then(|mac| {
        return allocator.new_atom(&com_atom).and_then(|com_sexp| {
            return allocator.new_pair(mac, allocator.null()).and_then(|env| {
                return allocator.new_pair(prog, env).and_then(|prog_env| {
                    return allocator.new_pair(com_sexp, prog_env).and_then(|to_eval| {
                        return allocator.new_atom(&args.data()).and_then(|arg_sexp| {
                            return evaluate(allocator, to_eval, arg_sexp);
                        });
                    });
                });
            })
        });
    });
}

pub fn brun<'a>(allocator: &'a mut Allocator, prog: NodePtr, args: NodePtr) -> Result<NodePtr, EvalErr> {
    return evaluate(allocator, prog, args);
}
