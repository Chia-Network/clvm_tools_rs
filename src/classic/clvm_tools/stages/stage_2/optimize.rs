use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::cost::Cost;
use clvm_rs::operator_handler::OperatorHandler;
use clvm_rs::reduction::{
    EvalErr,
    Reduction,
    Response
};

use crate::classic::clvm::__type_compatibility__::{
    bi_zero,
    bi_one
};
use crate::classic::clvm::sexp::{
    atom,
    enlist,
    first,
    foldM,
    mapM,
    non_nil,
    proper_list
};
use crate::classic::clvm_tools::NodePath::NodePath;
use crate::classic::clvm_tools::pattern_match::match_sexp;
use crate::classic::clvm_tools::stages::assemble;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};
use crate::classic::clvm_tools::stages::stage_2::helpers::quote;

use crate::util::{
    number_from_u8,
    u8_from_number
};

#[derive(Clone)]
pub struct DoOptProg {
    runner: Rc<dyn TRunProgram>
}

const DEBUG_OPTIMIZATIONS : u32 = 0;

pub fn seems_constant_tail<'a>(allocator: &'a mut Allocator, sexp_: NodePtr) -> bool {
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

pub fn seems_constant<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> bool {
    match allocator.sexp(sexp) {
        SExp::Atom(_b) => { return !non_nil(allocator, sexp); },
        SExp::Pair(operator,_r) => {
            match allocator.sexp(operator) {
                SExp::Atom(b) => {
                    let atom = allocator.buf(&b);
                    if atom.len() == 1 && atom[0] == 1 {
                        return true;
                    } else if atom.len() == 1 && atom[0] == 8 {
                        return false;
                    } else {
                        return true;
                    }
                },
                SExp::Pair(_,r) => {
                    if !seems_constant(allocator, operator) {
                        return false;
                    }

                    if !seems_constant_tail(allocator, r) {
                        return false;
                    }
                }
            }
        }
    }

    return true;
}

fn constant_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _max_cost: Cost,
    runner: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    /*
     * If the expression does not depend upon @ anywhere,
     * it's a constant. So we can simply evaluate it and
     * return the quoted result.
     */
    if seems_constant(allocator, r) && non_nil(allocator, r) {
        return m! {
            res <- runner.run_program(
                allocator,
                r,
                allocator.null(),
                None
            );
            let r1 = res.1;
            quoted <- quote(allocator, r1);
            Ok(quoted)
        };
    }

    return Ok(r);
}

pub fn is_args_call<'a>(allocator: &'a mut Allocator, r: NodePtr) -> bool {
    match allocator.sexp(r) {
        SExp::Atom(b) => {
            let buf = allocator.buf(&b);
            return buf.len() == 1 && buf[0] == 1;
        },
        _ => { return false; }
    }
}

pub fn cons_q_a_optimizer_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(a (q . (: . sexp)) (: . args))".to_string()
    ).unwrap();
}

pub fn cons_q_a_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    let CONS_Q_A_OPTIMIZER_PATTERN = cons_q_a_optimizer_pattern(allocator);

    /*
     * This applies the transform
     * (a (q . SEXP) @) => SEXP
     */

    return match match_sexp(allocator, CONS_Q_A_OPTIMIZER_PATTERN, r, HashMap::new()).and_then(|t1| t1.get("args").map(|i| *i)) {
        Some(args) => {
            if is_args_call(allocator, args) {
                Ok(args)
            } else {
                Ok(r)
            }
        },
        _ => Ok(r)
    };
}

fn cons_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(allocator, &"(c (: . first) (: . rest)))".to_string()).unwrap();
}

fn cons_f<'a>(allocator: &'a mut Allocator, args: NodePtr) -> Result<NodePtr, EvalErr> {
    return m! {
        let CONS_PATTERN = cons_pattern(allocator);
        match match_sexp(allocator, CONS_PATTERN, args, HashMap::new()).and_then(|t| t.get("first").map(|i| *i)) {
            Some(first) => Ok(first),
            _ => {
                m! {
                    first_atom <- allocator.new_atom(&vec!(5));
                    tail <- allocator.new_pair(args, allocator.null());
                    allocator.new_pair(first_atom, tail)
                }
            }
        }
    };
}

fn cons_r<'a>(allocator: &'a mut Allocator, args: NodePtr) -> Result<NodePtr, EvalErr> {
    return m! {
        let CONS_PATTERN = cons_pattern(allocator);
        match match_sexp(allocator, CONS_PATTERN, args, HashMap::new()).and_then(|t| t.get("rest").map(|i| *i)) {
            Some(rest) => Ok(rest),
            _ => {
                m! {
                    rest_atom <- allocator.new_atom(&vec!(6));
                    tail <- allocator.new_pair(args, allocator.null());
                    allocator.new_pair(rest_atom, tail)
                }
            }
        }
    };
}

fn path_from_args<'a>(allocator: &'a mut Allocator, sexp: NodePtr, new_args: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Atom(v_buf) => {
            let v = number_from_u8(allocator.buf(&v_buf));
            if v.clone() <= bi_one() {
                return Ok(new_args);
            }

            return m! {
                sexp <- allocator.new_atom(&u8_from_number(v.clone() >> 1).to_vec());
                if (v & 1_u32.to_bigint().unwrap()) != bi_zero() {
                    m! {
                        cons_r_res <- cons_r(allocator, new_args);
                        path_from_args(allocator, sexp, cons_r_res)
                    }
                } else {
                    m! {
                        cons_f_res <- cons_f(allocator, new_args);
                        path_from_args(allocator, sexp, cons_f_res)
                    }
                }
            };
        },
        _ => { return Ok(new_args); }
    }
}

fn sub_args<'a>(allocator: &'a mut Allocator, sexp: NodePtr, new_args: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Atom(_) => { return path_from_args(allocator, sexp, new_args); },
        SExp::Pair(_,_) => {
            return m! {
                first_pre <- first(allocator, sexp);
                first <-
                    match allocator.sexp(first_pre) {
                        SExp::Pair(_,_) => {
                            sub_args(allocator, first_pre, new_args)
                        },
                        _ => { Ok(first_pre) }
                    };

                match proper_list(allocator, first, true) {
                    Some(args) => { enlist(allocator, &args) },
                    None => { path_from_args(allocator, sexp, new_args) },
                }
            }
        }
    }
}

fn var_change_optimizer_cons_eval_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(allocator, &"(a (q . (: . sexp)) (: . args))".to_string()).unwrap();
}

fn var_change_optimizer_cons_eval(
    allocator: &mut Allocator,
    r: NodePtr,
    eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    /*
     * This applies the transform
     * (a (q . (op SEXP1...)) (ARGS)) => (q . RET_VAL) where ARGS != @
     * via
     * (op (a SEXP1 (ARGS)) ...) (ARGS)) and then "children_optimizer" of this.
     * In some cases, this can result in a constant in some of the children.
     *
     * If we end up needing to push the "change of variables" to only one child, keep
     * the optimization. Otherwise discard it.
     */

    let VAR_CHANGE_OPTIMIZER_CONS_EVAL_PATTERN =
        var_change_optimizer_cons_eval_pattern(allocator);

    return m! {
        let t1 =
            match_sexp(
                allocator,
                VAR_CHANGE_OPTIMIZER_CONS_EVAL_PATTERN,
                r,
                HashMap::new()
            );

        let original_args =
            match t1.clone().and_then(|t1| t1.get("args").map(|i| *i)) {
                Some(v) => v,
                _ => allocator.null()
            };
        let original_call =
            match t1.and_then(|t1| t1.get("sexp").map(|i| *i)) {
                Some(v) => v,
                _ => allocator.null()
            };

        new_eval_sexp_args <- sub_args(allocator, original_call, original_args);

        // Do not iterate into a quoted value as if it were a list
        if seems_constant(allocator, new_eval_sexp_args) {
            optimize_sexp(allocator, new_eval_sexp_args, eval_f)
        } else {
            match proper_list(allocator, new_eval_sexp_args, true) {
                Some(new_operands) => {
                    m! {
                        opt_operands <-
                            mapM(allocator, &mut new_operands.into_iter(), &|allocator, o| {
                                optimize_sexp(allocator, o, eval_f.clone())
                            });

                        non_constant_count <-
                            foldM(allocator, &|allocator, acc, val| {
                                match allocator.sexp(val) {
                                    SExp::Atom(_v) => { return Ok(acc); },
                                    SExp::Pair(f,_r) => {
                                        match allocator.sexp(f) {
                                            SExp::Atom(q) => {
                                                if allocator.buf(&q) == vec!(1) {
                                                    return Ok(acc);
                                                } else {
                                                    return Ok(acc + 1);
                                                }
                                            },
                                            _ => {
                                                if proper_list(allocator, val, false).is_none() {
                                                    return Ok(acc);
                                                } else {
                                                    return Ok(acc + 1);
                                                }
                                            }
                                        }
                                    }
                                }
                            }, 0, &mut opt_operands.iter().map(|x| *x));

                        if non_constant_count < 1 {
                            enlist(allocator, &opt_operands)
                        } else {
                            Ok(r)
                        }
                    }
                },
                None => Ok(r)
            }
        }
    };
}

fn children_optimizer(
    allocator: &mut Allocator,
    r: NodePtr,
    eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    // Recursively apply optimizations to all non-quoted child nodes.
    match proper_list(allocator, r, true) {
        None => Ok(r),
        Some(list) => {
            if list.len() == 0 { return Ok(r); }
            match allocator.sexp(list[0]) {
                SExp::Atom(op_buf) => {
                    if allocator.buf(&op_buf).to_vec() == vec!(1) {
                        return Ok(r);
                    }
                },
                _ => {}
            }

            m! {
                optimized <- mapM(
                    allocator,
                    &mut list.into_iter(),
                    &|allocator, v| optimize_sexp(allocator, v, eval_f.clone())
                );
                enlist(allocator, &optimized)
            }
        }
    }
}

fn cons_optimizer_pattern_first<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(f (c (: . first) (: . rest)))".to_string()
    ).unwrap();
}

fn cons_optimizer_pattern_rest<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(r (c (: . first) (: . rest)))".to_string()
    ).unwrap();
}

fn cons_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    /*
     * This applies the transform
     *  (f (c A B)) => A
     *  and
     *  (r (c A B)) => B
     */
    let CONS_OPTIMIZER_PATTERN_FIRST = cons_optimizer_pattern_first(allocator);
    let CONS_OPTIMIZER_PATTERN_REST = cons_optimizer_pattern_rest(allocator);

    return m! {
        let t1 = match_sexp(
            allocator, CONS_OPTIMIZER_PATTERN_FIRST, r, HashMap::new()
        );
        match t1.and_then(|t| t.get("first").map(|i| *i)) {
            Some(first) => Ok(first),
            _ => {
                m! {
                    let t2 = match_sexp(
                        allocator, CONS_OPTIMIZER_PATTERN_REST, r, HashMap::new()
                    );
                    match t2.and_then(|t| t.get("rest").map(|i| *i)) {
                        Some(rest) => Ok(rest),
                        _ => Ok(r)
                    }
                }
            }
        }
    };
}

fn first_atom_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(f ($ . atom))".to_string()
    ).unwrap();
}

fn rest_atom_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(r ($ . atom))".to_string()
    ).unwrap();
}

fn path_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    let FIRST_ATOM_PATTERN = first_atom_pattern(allocator);
    let REST_ATOM_PATTERN = rest_atom_pattern(allocator);

    /*
     * This applies the transform
     *   (f N) => A
     * and
     *   (r N) => B
     */

    let first_match = match_sexp(allocator, FIRST_ATOM_PATTERN, r, HashMap::new());
    let rest_match = match_sexp(allocator, REST_ATOM_PATTERN, r, HashMap::new());

    return m! {
        match (first_match, rest_match) {
            (Some(first), _) => {
                match first.
                    get("atom").
                    and_then(|a| atom(allocator, *a).ok()).
                    map(|atom| number_from_u8(allocator.buf(&atom)))
                {
                    Some(atom) => {
                        let node =
                            NodePath::new(Some(atom)).
                            add(NodePath::new(None).first());
                        allocator.new_atom(node.as_path().data())
                    },
                    _ => { Ok(r) }
                }
            },
            (_, Some(rest)) => {
                match rest.
                    get("atom").
                    and_then(|a| atom(allocator, *a).ok()).
                    map(|atom| number_from_u8(allocator.buf(&atom)))
                {
                    Some(atom) => {
                        let node =
                            NodePath::new(Some(atom)).
                            add(NodePath::new(None).first());
                        allocator.new_atom(node.as_path().data())
                    },
                    _ => { Ok(r) }
                }
            },
            _ => Ok(r)
        }
    };
}

fn quote_pattern_1(
    allocator: &mut Allocator
) -> NodePtr {
    return assemble(allocator, &"(q . 0)".to_string()).unwrap();
}

fn quote_null_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    let QUOTE_PATTERN_1 = quote_pattern_1(allocator);

    // This applies the transform `(q . 0)` => `0`
    let t1 = match_sexp(allocator, QUOTE_PATTERN_1, r, HashMap::new());
    return Ok(t1.map(|_| allocator.null()).unwrap_or_else(|| r));
}

fn apply_null_pattern_1(allocator: &mut Allocator) -> NodePtr {
    return assemble(allocator, &"(a 0 . (: . rest))".to_string()).unwrap();
}

fn apply_null_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    let APPLY_NULL_PATTERN_1 = apply_null_pattern_1(allocator);

    // This applies the transform `(a 0 ARGS)` => `0`
    let t1 = match_sexp(allocator, APPLY_NULL_PATTERN_1, r, HashMap::new());
    return Ok(t1.map(|_| allocator.null()).unwrap_or_else(|| r));
}

struct OptimizerRunner<'a> {
    pub name: String,
    to_run: &'a dyn Fn(&mut Allocator, NodePtr, Rc<dyn TRunProgram>) -> Result<NodePtr, EvalErr>
}

impl<'a> OptimizerRunner<'a> {
    pub fn invoke(
        &self,
        allocator: &mut Allocator,
        r: NodePtr,
        eval_f: Rc<dyn TRunProgram>
    ) -> Result<NodePtr, EvalErr> {
        return (self.to_run)(allocator, r, eval_f);
    }

    pub fn new(
        name: &str,
        to_run: &'a dyn Fn(
            &mut Allocator,
            NodePtr,
            Rc<dyn TRunProgram>
        ) -> Result<NodePtr, EvalErr>
    ) -> Self {
        return OptimizerRunner { name: name.to_string(), to_run: to_run };
    }
}

pub fn optimize_sexp<'a>(allocator: &mut Allocator, r_: NodePtr, eval_f: Rc<dyn TRunProgram>) -> Result<NodePtr, EvalErr> {
    let mut r = r_;

    /*
     * Optimize an s-expression R written for clvm to R_opt where
     * (a R args) == (a R_opt args) for ANY args.
     */
    match allocator.sexp(r) {
        SExp::Atom(_) => { return Ok(r); }
        _ => { }
    }

    let OPTIMIZERS : Vec<OptimizerRunner> = vec!(
        OptimizerRunner::new("cons_optimizer", &cons_optimizer),
        OptimizerRunner::new("constant_optimizer", &|allocator, r, eval_f| constant_optimizer(allocator, r, 0, eval_f.clone())),
        OptimizerRunner::new("cons_q_a_optimizer", &cons_q_a_optimizer),
        OptimizerRunner::new(
            "var_change_optimizer_cons_eval",
            &var_change_optimizer_cons_eval
        ),
        OptimizerRunner::new("children_optimizer", &children_optimizer),
        OptimizerRunner::new("path_optimizer", &path_optimizer),
        OptimizerRunner::new("quote_null_optimizer", &quote_null_optimizer),
        OptimizerRunner::new("apply_null_optimizer", &apply_null_optimizer)
    );

    while !proper_list(allocator, r, false).is_none() {
        let start_r = r;

        for opt in OPTIMIZERS.iter() {
            match opt.invoke(allocator, r, eval_f.clone()) {
                Err(e) => { return Err(e); },
                Ok(res) => {
                    if start_r != r {
                        break;
                    }
                    r = res;
                }
            }

            if start_r == r {
                return Ok(r);
            }

            if DEBUG_OPTIMIZATIONS > 0 {
                print!("OPT-{:?}[{:?}] => {:?}", &opt.name, &start_r, &r);
            }
        }
    }

    return Ok(r);
}

impl DoOptProg {
    pub fn new() -> Self {
        return DoOptProg { runner: Rc::new(DefaultProgramRunner::new()) };
    }

    pub fn set_runner(&mut self, runner: Rc<dyn TRunProgram>) {
        self.runner = runner;
    }
}

impl OperatorHandler for DoOptProg {
    fn op(
        &self,
        allocator: &mut Allocator,
        _op: NodePtr,
        r: NodePtr,
        _max_cost: Cost
    ) -> Response {
        return optimize_sexp(allocator, r, self.runner.clone()).
            map(|optimized| Reduction(1, optimized));
    }
}
