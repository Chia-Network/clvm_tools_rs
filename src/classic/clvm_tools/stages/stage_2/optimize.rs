use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::{EvalErr, Reduction, Response};

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm::sexp::{
    atom, enlist, equal_to, first, foldM, mapM, non_nil, proper_list,
};
use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::pattern_match::match_sexp;
use crate::classic::clvm_tools::stages::assemble;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::clvm_tools::stages::stage_2::helpers::quote;
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;
use crate::classic::clvm_tools::NodePath::NodePath;

use crate::util::{number_from_u8, u8_from_number};

#[derive(Clone)]
pub struct DoOptProg {
    runner: Rc<dyn TRunProgram>,
}

const DEBUG_OPTIMIZATIONS: bool = false;
const DIAG_OPTIMIZATIONS: bool = false;

pub fn seems_constant_tail<'a>(allocator: &'a mut Allocator, sexp_: NodePtr) -> bool {
    let mut sexp = sexp_;

    loop {
        match allocator.sexp(sexp) {
            SExp::Pair(l, r) => {
                if !seems_constant(allocator, l) {
                    return false;
                }

                sexp = r;
            }
            SExp::Atom(_) => {
                return sexp == allocator.null();
            }
        }
    }
}

pub fn seems_constant<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> bool {
    match allocator.sexp(sexp) {
        SExp::Atom(_b) => {
            return sexp == allocator.null();
        }
        SExp::Pair(operator, r) => {
            match allocator.sexp(operator) {
                SExp::Atom(b) => {
                    let atom = allocator.buf(&b);
                    if atom.len() == 1 && atom[0] == 1 {
                        return true;
                    } else if atom.len() == 1 && atom[0] == 8 {
                        return false;
                    }
                }
                SExp::Pair(_, _) => {
                    if !seems_constant(allocator, operator) {
                        return false;
                    }
                }
            }

            if !seems_constant_tail(allocator, r) {
                return false;
            }
        }
    }
    true
}

fn constant_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _max_cost: Cost,
    runner: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    /*
     * If the expression does not depend upon @ anywhere,
     * it's a constant. So we can simply evaluate it and
     * return the quoted result.
     */
    let sc_r = seems_constant(allocator, r);
    let nn_r = non_nil(allocator, r);
    if DIAG_OPTIMIZATIONS {
        println!(
            "COPT {} SC_R {} NN_R {}",
            disassemble(allocator, r),
            sc_r,
            nn_r
        );
    }
    if sc_r && nn_r {
        return m! {
            res <- runner.run_program(
                allocator,
                r,
                allocator.null(),
                None
            );
            let r1 = res.1;
            let _ = if DIAG_OPTIMIZATIONS {
                print!(
                    "CONSTANT_OPTIMIZER {} TO {}\n",
                    disassemble(allocator, r),
                    disassemble(allocator, r1)
                );
            };
            quoted <- quote(allocator, r1);
            Ok(quoted)
        };
    }

    Ok(r)
}

pub fn is_args_call<'a>(allocator: &'a mut Allocator, r: NodePtr) -> bool {
    match allocator.sexp(r) {
        SExp::Atom(b) => {
            let buf = allocator.buf(&b);
            buf.len() == 1 && buf[0] == 1
        }
        _ => false,
    }
}

pub fn cons_q_a_optimizer_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(a (q . (: . sexp)) (: . args))".to_string()).unwrap()
}

pub fn cons_q_a_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    let CONS_Q_A_OPTIMIZER_PATTERN = cons_q_a_optimizer_pattern(allocator);

    /*
     * This applies the transform
     * (a (q . SEXP) @) => SEXP
     */

    let matched = match_sexp(allocator, CONS_Q_A_OPTIMIZER_PATTERN, r, HashMap::new());

    return match (
        matched.as_ref().and_then(|t1| t1.get("args").map(|i| *i)),
        matched.as_ref().and_then(|t1| t1.get("sexp").map(|i| *i)),
    ) {
        (Some(args), Some(sexp)) => {
            if is_args_call(allocator, args) {
                Ok(sexp)
            } else {
                Ok(r)
            }
        }
        _ => Ok(r),
    };
}

fn cons_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(c (: . first) (: . rest)))".to_string()).unwrap()
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

fn path_from_args<'a>(
    allocator: &'a mut Allocator,
    sexp: NodePtr,
    new_args: NodePtr,
) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Atom(v_buf) => {
            let v = number_from_u8(allocator.buf(&v_buf));
            if v.clone() <= bi_one() {
                Ok(new_args)
            } else {
                let sexp = allocator.new_atom(&u8_from_number(v.clone() >> 1).to_vec())?;
                if (v & 1_u32.to_bigint().unwrap()) != bi_zero() {
                    let cons_r_res = cons_r(allocator, new_args)?;
                    path_from_args(allocator, sexp, cons_r_res)
                } else {
                    let cons_f_res = cons_f(allocator, new_args)?;
                    path_from_args(allocator, sexp, cons_f_res)
                }
            }
        }
        _ => Ok(new_args),
    }
}

fn sub_args<'a>(
    allocator: &'a mut Allocator,
    sexp: NodePtr,
    new_args: NodePtr,
) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Atom(_) => path_from_args(allocator, sexp, new_args),
        SExp::Pair(first_pre, rest) => {
            let mut first = sexp;

            match allocator.sexp(first_pre) {
                SExp::Pair(_, _) => {
                    first = sub_args(allocator, first_pre, new_args)?;
                }
                SExp::Atom(b) => {
                    let atom = allocator.buf(&b);
                    if atom.len() == 1 && atom[0] == 1 {
                        return Ok(sexp);
                    } else {
                        first = first_pre;
                    }
                }
            }

            match proper_list(allocator, rest, true) {
                Some(tail_args) => m! {
                    res <- mapM(
                        allocator,
                        &mut tail_args.iter(),
                        &|allocator, elt| {
                            sub_args(allocator, *elt, new_args)
                        }
                    );
                    tail_list <- enlist(allocator, &res);
                    allocator.new_pair(first, tail_list)
                },
                None => path_from_args(allocator, sexp, new_args),
            }
        }
    }
}

fn var_change_optimizer_cons_eval_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(a (q . (: . sexp)) (: . args))".to_string()).unwrap()
}

fn var_change_optimizer_cons_eval(
    allocator: &mut Allocator,
    r: NodePtr,
    eval_f: Rc<dyn TRunProgram>,
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

    let pattern = var_change_optimizer_cons_eval_pattern(allocator);
    match match_sexp(allocator, pattern, r, HashMap::new()).as_ref() {
        None => Ok(r),
        Some(t1) => {
            m! {
                original_args <- t1.get("args").
                    ok_or(EvalErr(r, "bad pattern match on args".to_string()));

                let _ = if DIAG_OPTIMIZATIONS {
                    print!(
                        "XXX ORIGINAL_ARGS {}\n",
                        disassemble(allocator, *original_args)
                    );
                };
                original_call <- t1.get("sexp").
                    ok_or(EvalErr(r, "bad pattern match on sexp".to_string()));
                let _ = if DIAG_OPTIMIZATIONS {
                    print!(
                        "XXX ORIGINAL_CALL {}\n",
                        disassemble(allocator, *original_call)
                    );
                };

                new_eval_sexp_args <- sub_args(
                    allocator,
                    *original_call,
                    *original_args
                );
                let _ = if DIAG_OPTIMIZATIONS {
                    print!(
                        "XXX new_eval_sexp_args {} ORIG {}\n",
                        disassemble(allocator, new_eval_sexp_args),
                        disassemble(allocator, *original_args)
                    );
                };

                // Do not iterate into a quoted value as if it were a list
                if seems_constant(allocator, new_eval_sexp_args) {
                    if DIAG_OPTIMIZATIONS {
                        print!("XXX seems_constant\n");
                    }
                    optimize_sexp(
                        allocator,
                        new_eval_sexp_args,
                        eval_f
                    )
                } else { m! {
                    let _ = if DIAG_OPTIMIZATIONS {
                        print!("XXX does not seems_constant\n");
                    };

                    new_operands <-
                        proper_list(
                            allocator,
                            new_eval_sexp_args,
                            true).ok_or(
                            EvalErr(
                                new_eval_sexp_args,
                                "Must be a proper list".to_string()
                            )
                        );

                    opt_operands <-
                        mapM(
                            allocator,
                            &mut new_operands.iter(),
                            &|allocator, item| {
                                optimize_sexp(allocator, *item, eval_f.clone())
                            }
                        );

                    non_constant_count <- foldM(
                        allocator,
                        &|allocator, acc, val| {
                            if DIAG_OPTIMIZATIONS {
                                print!(
                                    "XXX opt_operands {} {}\n",
                                    acc,
                                    disassemble(allocator, val)
                                );
                            }
                            let increment =
                                match allocator.sexp(val) {
                                    SExp::Pair(val_first,_) => {
                                        match allocator.sexp(val_first) {
                                            SExp::Atom(b) => {
                                                let vf_buf = allocator.buf(&b);
                                                if vf_buf.len() != 1 || vf_buf[0] != 1 {
                                                    1
                                                } else {
                                                    0
                                                }
                                            },
                                            _ => 0
                                        }
                                    },
                                    _ => 0
                                };

                            Ok(acc + increment)
                        },
                        0,
                        &mut opt_operands.iter().map(|x| *x)
                    );

                    let _ = if DIAG_OPTIMIZATIONS {
                        print!(
                            "XXX non_constant_count {}\n",
                            non_constant_count
                        );
                    };

                    if non_constant_count < 1 {
                        enlist(allocator, &opt_operands)
                    } else {
                        Ok(r)
                    }
                } }
            }
        }
    }
}

fn children_optimizer(
    allocator: &mut Allocator,
    r: NodePtr,
    eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    // Recursively apply optimizations to all non-quoted child nodes.
    match proper_list(allocator, r, true) {
        None => Ok(r),
        Some(list) => {
            if list.len() == 0 {
                return Ok(r);
            }
            match allocator.sexp(list[0]) {
                SExp::Atom(op_buf) => {
                    if allocator.buf(&op_buf).to_vec() == vec![1] {
                        return Ok(r);
                    }
                }
                _ => {}
            }

            m! {
                optimized <- mapM(
                    allocator,
                    &mut list.into_iter(),
                    &|allocator, v| {
                        optimize_sexp(allocator, v, eval_f.clone())
                    }
                );
                enlist(allocator, &optimized)
            }
        }
    }
}

fn cons_optimizer_pattern_first<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(f (c (: . first) (: . rest)))".to_string()).unwrap()
}

fn cons_optimizer_pattern_rest<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(r (c (: . first) (: . rest)))".to_string()).unwrap()
}

fn cons_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>,
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
    assemble(allocator, &"(f ($ . atom))".to_string()).unwrap()
}

fn rest_atom_pattern<'a>(allocator: &'a mut Allocator) -> NodePtr {
    assemble(allocator, &"(r ($ . atom))".to_string()).unwrap()
}

fn path_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>,
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
                            add(NodePath::new(None).rest());
                        allocator.new_atom(node.as_path().data())
                    },
                    _ => { Ok(r) }
                }
            },
            _ => Ok(r)
        }
    };
}

fn quote_pattern_1(allocator: &mut Allocator) -> NodePtr {
    assemble(allocator, &"(q . 0)".to_string()).unwrap()
}

fn quote_null_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    let QUOTE_PATTERN_1 = quote_pattern_1(allocator);

    // This applies the transform `(q . 0)` => `0`
    let t1 = match_sexp(allocator, QUOTE_PATTERN_1, r, HashMap::new());
    Ok(t1.map(|_| allocator.null()).unwrap_or_else(|| r))
}

fn apply_null_pattern_1(allocator: &mut Allocator) -> NodePtr {
    assemble(allocator, &"(a 0 . (: . rest))".to_string()).unwrap()
}

fn apply_null_optimizer<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    _eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    let APPLY_NULL_PATTERN_1 = apply_null_pattern_1(allocator);

    // This applies the transform `(a 0 ARGS)` => `0`
    let t1 = match_sexp(allocator, APPLY_NULL_PATTERN_1, r, HashMap::new());
    Ok(t1.map(|_| allocator.null()).unwrap_or_else(|| r))
}

struct OptimizerRunner<'a> {
    pub name: String,
    to_run: &'a dyn Fn(&mut Allocator, NodePtr, Rc<dyn TRunProgram>) -> Result<NodePtr, EvalErr>,
}

impl<'a> OptimizerRunner<'a> {
    pub fn invoke(
        &self,
        allocator: &mut Allocator,
        r: NodePtr,
        eval_f: Rc<dyn TRunProgram>,
    ) -> Result<NodePtr, EvalErr> {
        (self.to_run)(allocator, r, eval_f)
    }

    pub fn new(
        name: &str,
        to_run: &'a dyn Fn(
            &mut Allocator,
            NodePtr,
            Rc<dyn TRunProgram>,
        ) -> Result<NodePtr, EvalErr>,
    ) -> Self {
        OptimizerRunner {
            name: name.to_string(),
            to_run,
        }
    }
}

pub fn optimize_sexp_<'a>(
    allocator: &mut Allocator,
    r_: NodePtr,
    eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    let mut r = r_;

    /*
     * Optimize an s-expression R written for clvm to R_opt where
     * (a R args) == (a R_opt args) for ANY args.
     */
    let OPTIMIZERS: Vec<OptimizerRunner> = vec![
        OptimizerRunner::new("cons_optimizer", &cons_optimizer),
        OptimizerRunner::new("constant_optimizer", &|allocator, r, eval_f| {
            constant_optimizer(allocator, r, 0, eval_f.clone())
        }),
        OptimizerRunner::new("cons_q_a_optimizer", &cons_q_a_optimizer),
        OptimizerRunner::new(
            "var_change_optimizer_cons_eval",
            &var_change_optimizer_cons_eval,
        ),
        OptimizerRunner::new("children_optimizer", &children_optimizer),
        OptimizerRunner::new("path_optimizer", &path_optimizer),
        OptimizerRunner::new("quote_null_optimizer", &quote_null_optimizer),
        OptimizerRunner::new("apply_null_optimizer", &apply_null_optimizer),
    ];

    loop {
        let start_r = r;
        let mut name = "".to_string();

        match allocator.sexp(r) {
            SExp::Atom(_) => {
                return Ok(r);
            }
            SExp::Pair(_, _) => {
                for opt in OPTIMIZERS.iter() {
                    name = opt.name.clone();
                    match opt.invoke(allocator, r, eval_f.clone()) {
                        Err(e) => {
                            return Err(e);
                        }
                        Ok(res) => {
                            if !equal_to(allocator, r, res) {
                                r = res;
                                break;
                            }
                        }
                    }
                }

                if equal_to(allocator, start_r, r) {
                    return Ok(r);
                }

                if DEBUG_OPTIMIZATIONS {
                    println!(
                        "OPT-{:?}[{}] => {}",
                        name,
                        disassemble(allocator, start_r),
                        disassemble(allocator, r)
                    );
                    if name == "var_change_optimizer_cons_eval" {
                        panic!("not supposed to happen for this");
                    }
                }
            }
        }
    }
}

pub fn optimize_sexp<'a>(
    allocator: &mut Allocator,
    r: NodePtr,
    eval_f: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    if DIAG_OPTIMIZATIONS {
        print!("START OPTIMIZE {}", disassemble(allocator, r));
    }
    optimize_sexp_(allocator, r, eval_f).map(|x| {
        if DIAG_OPTIMIZATIONS {
            println!(
                "OPTIMIZE_SEXP {} GIVING {}",
                disassemble(allocator, r),
                disassemble(allocator, x)
            );
        }
        x
    })
}

pub fn do_optimize(runner: Rc<dyn TRunProgram>, allocator: &mut Allocator, r: NodePtr) -> Response {
    m! {
        r_first <- first(allocator, r);
        optimize_sexp(allocator, r_first, runner.clone()).
            map(|optimized| Reduction(1, optimized))
    }
}

fn test_cons_q_a(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let optimized = cons_q_a_optimizer(&mut allocator, assembled, runner.clone()).unwrap();
    disassemble(&mut allocator, optimized)
}

fn test_var_change_optimizer_cons_eval(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let optimized =
        var_change_optimizer_cons_eval(&mut allocator, assembled, runner.clone()).unwrap();
    disassemble(&mut allocator, optimized)
}

fn test_children_optimizer(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let optimized = children_optimizer(&mut allocator, assembled, runner.clone()).unwrap();
    disassemble(&mut allocator, optimized)
}

fn test_constant_optimizer(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let optimized = constant_optimizer(&mut allocator, assembled, 0, runner.clone()).unwrap();
    disassemble(&mut allocator, optimized)
}

fn test_optimizer(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let optimized = optimize_sexp(&mut allocator, assembled, runner.clone()).unwrap();
    disassemble(&mut allocator, optimized)
}

fn test_sub_args(src: String) -> String {
    let mut allocator = Allocator::new();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    match allocator.sexp(assembled) {
        SExp::Pair(a, b) => {
            let optimized = sub_args(&mut allocator, a, b).unwrap();
            disassemble(&mut allocator, optimized)
        }
        _ => {
            panic!("assembled a list got an atom");
        }
    }
}

#[test]
fn cons_q_a_simple() {
    assert_eq!(
        test_cons_q_a("(a (q 1 . \"opt\") 1)".to_string()),
        "(q . \"opt\")".to_string()
    );
}

#[test]
fn cons_q_a_optimizer_example() {
    let src = "(a (q \"opt\" (q 2 (\"opt\" (\"com\" (q 88 65 66) (q () () ((q . \"list\") (a (q (q . 97) (q (q . 97) (q . 2) (c (q . 2) (c (q . 3) (q)))) (c (q (q . 97) (i (q . 5) (q (q . 99) 4 (c (q . 9) (c (a (q . 2) (c (q . 2) (c (q . 13) (q)))) (q)))) (q (q . 1))) (q . 1)) (q . 1))) (q . 1))) ((q . \"defmacro\") (c \"list\" (c (f (q . 1)) (c (c \"mod\" (c (f (r (q . 1))) (c (f (r (r (q . 1)))) (q)))) (q)))))) (q (65 5) (66 11) (88 2)))) (c (\"opt\" (\"com\" (q 16 65 66) (q () () ((q . \"list\") (a (q (q . 97) (q (q . 97) (q . 2) (c (q . 2) (c (q . 3) (q)))) (c (q (q . 97) (i (q . 5) (q (q . 99) 4 (c (q . 9) (c (a (q . 2) (c (q . 2) (c (q . 13) (q)))) (q)))) (q (q . 1))) (q . 1)) (q . 1))) (q . 1))) ((q . \"defmacro\") (c \"list\" (c (f (q . 1)) (c (c \"mod\" (c (f (r (q . 1))) (c (f (r (r (q . 1)))) (q)))) (q)))))) (q (65 5) (66 11) (88 2)))) 1))) 1)".to_string();
    let optimized = test_cons_q_a(src);
    assert_eq!(optimized, "(\"opt\" (q 2 (\"opt\" (\"com\" (q 88 65 66) (q () () ((q . \"list\") (a (q (q . 97) (q (q . 97) (q . 2) (c (q . 2) (c (q . 3) (q)))) (c (q (q . 97) (i (q . 5) (q (q . 99) 4 (c (q . 9) (c (a (q . 2) (c (q . 2) (c (q . 13) (q)))) (q)))) (q (q . 1))) (q . 1)) (q . 1))) (q . 1))) ((q . \"defmacro\") (c \"list\" (c (f (q . 1)) (c (c \"mod\" (c (f (r (q . 1))) (c (f (r (r (q . 1)))) (q)))) (q)))))) (q (65 5) (66 11) (88 2)))) (c (\"opt\" (\"com\" (q 16 65 66) (q () () ((q . \"list\") (a (q (q . 97) (q (q . 97) (q . 2) (c (q . 2) (c (q . 3) (q)))) (c (q (q . 97) (i (q . 5) (q (q . 99) 4 (c (q . 9) (c (a (q . 2) (c (q . 2) (c (q . 13) (q)))) (q)))) (q (q . 1))) (q . 1)) (q . 1))) (q . 1))) ((q . \"defmacro\") (c \"list\" (c (f (q . 1)) (c (c \"mod\" (c (f (r (q . 1))) (c (f (r (r (q . 1)))) (q)))) (q)))))) (q (65 5) (66 11) (88 2)))) 1)))".to_string());
}

#[test]
fn children_optimizer_example() {
    let src = "(c (a (q 1 . 1) 1) (a (q . 2) 1))".to_string();
    assert_eq!(test_children_optimizer(src), "(c (q . 1) 2)");
}

#[test]
fn constant_optimizer_example() {
    let src = "(c (q . 29041) (c (c (q . \"unquote\") (c (c (a (q 1 . \"macros\") (q . 1)) (a (q 1) (q . 1))) (q))) (q)))".to_string();
    assert_eq!(
        test_constant_optimizer(src),
        "(q 29041 (\"unquote\" (\"macros\")))".to_string()
    );
}

#[test]
fn test_sub_args_1() {
    let src = "(5 . 1)".to_string();
    assert_eq!(test_sub_args(src), "(f (r 1))".to_string());
}

#[test]
fn test_path_optimizer_3() {
    let src = "(sha256 (r 1))".to_string();
    assert_eq!(test_optimizer(src), "(sha256 3)");
}

#[test]
fn test_path_optimizer_5() {
    let src = "(sha256 (f (r 1)))".to_string();
    assert_eq!(test_optimizer(src), "(sha256 5)");
}

#[test]
fn children_optimizer_test_2() {
    let src = "(c (a (q 1) 1) (a (q 1) 1))".to_string();
    assert_eq!(test_children_optimizer(src), "(c () ())");
}

#[test]
fn test_optimizer_q_empty_list() {
    let src = "(a (q 1) 1)".to_string();
    assert_eq!(test_optimizer(src), "()");
}

#[test]
fn seems_constant_quote_test() {
    let mut allocator = Allocator::new();
    let src = "(q . 15)".to_string();
    let input_ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(&mut allocator, Rc::new(input_ir)).unwrap();
    assert_eq!(seems_constant(&mut allocator, assembled), true);
}

fn constant_optimize_test_from_file(src: String) -> (String, String) {
    let mut testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let name_src = src.clone() + ".txt";
    let name_tgt = src.clone() + ".want";
    testpath.push("resources/tests/stage_2/");
    let mut in_path = testpath.clone();
    in_path.push(name_src);
    let mut out_path = testpath.clone();
    out_path.push(name_tgt);

    fs::read_to_string(in_path)
        .and_then(|input| {
            fs::read_to_string(out_path).map(|output| (input, output.trim().to_string()))
        })
        .unwrap()
}

#[test]
fn test_optimize_1() {
    let src = "(\"opt\" (\"com\" (q 29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) (q (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))))) (q (\"BODY\" 2))))".to_string();
    assert_eq!(
        test_optimizer(src),
        "(q 4 (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))".to_string()
    );
}
