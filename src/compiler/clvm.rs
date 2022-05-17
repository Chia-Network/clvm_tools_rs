use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator;
use clvm_rs::allocator::{Allocator, NodePtr};

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero, sha256, Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::util::{number_from_u8, u8_from_number, Number};

#[derive(Clone, Debug)]
pub enum RunStep {
    Done(Srcloc, Rc<SExp>),
    OpResult(Srcloc, Rc<SExp>, Rc<RunStep>),
    Op(
        Rc<SExp>,
        Rc<SExp>,
        Rc<SExp>,
        Option<Vec<Rc<SExp>>>,
        Rc<RunStep>,
    ),
    Step(Rc<SExp>, Rc<SExp>, Rc<RunStep>),
}

impl RunStep {
    pub fn parent(&self) -> Option<Rc<RunStep>> {
        match self {
            RunStep::Done(_, _) => None,
            RunStep::OpResult(_, _, p) => Some(p.clone()),
            RunStep::Op(_, _, _, _, p) => Some(p.clone()),
            RunStep::Step(_, _, p) => Some(p.clone()),
        }
    }
}

fn choose_path(
    l: Srcloc,
    orig: Number,
    p: Number,
    all: Rc<SExp>,
    context: Rc<SExp>,
) -> Result<Rc<SExp>, RunFailure> {
    if p == bi_one() {
        Ok(context.clone())
    } else {
        match context.borrow() {
            SExp::Cons(l, a, b) => {
                let next = if p.clone() % 2_i32.to_bigint().unwrap() == bi_zero() {
                    a
                } else {
                    b
                };

                choose_path(
                    l.clone(),
                    orig,
                    p / (2_i32.to_bigint().unwrap()),
                    all,
                    next.clone(),
                )
            }

            _ => Err(RunFailure::RunErr(
                l,
                format!("bad path {} in {}", orig, all.to_string()),
            )),
        }
    }
}

fn translate_head(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    l: Srcloc,
    sexp: Rc<SExp>,
    context: Rc<SExp>,
) -> Result<Rc<SExp>, RunFailure> {
    match sexp.borrow() {
        SExp::Nil(l) => Err(RunFailure::RunErr(
            l.clone(),
            "cannot apply nil".to_string(),
        )),
        SExp::QuotedString(l, _, v) => translate_head(
            allocator,
            runner,
            prim_map,
            l.clone(),
            Rc::new(SExp::Atom(l.clone(), v.clone())),
            context.clone(),
        ),
        SExp::Atom(l, v) => match prim_map.get(v) {
            None => translate_head(
                allocator,
                runner,
                prim_map,
                l.clone(),
                Rc::new(SExp::Integer(l.clone(), number_from_u8(v))),
                context.clone(),
            ),
            Some(v) => Ok(Rc::new(v.with_loc(l.clone()))),
        },
        SExp::Integer(l, i) => match prim_map.get(&u8_from_number(i.clone())) {
            None => Ok(sexp.clone()),
            Some(v) => Ok(Rc::new(v.with_loc(l.clone()))),
        },
        SExp::Cons(l, a, nil) => match nil.borrow() {
            SExp::Nil(l1) => run(allocator, runner, prim_map, sexp.clone(), context.clone()),
            _ => Err(RunFailure::RunErr(
                sexp.loc(),
                format!("Unexpected head form in clvm {}", sexp.to_string()),
            )),
        },
    }
}

fn eval_args(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    head: Rc<SExp>,
    sexp_: Rc<SExp>,
    context_: Rc<SExp>,
    parent: Rc<RunStep>,
) -> Result<RunStep, RunFailure> {
    let mut sexp = sexp_.clone();
    let mut eval_list: Vec<Rc<SExp>> = Vec::new();

    loop {
        match sexp.borrow() {
            SExp::Nil(l) => {
                return Ok(RunStep::Op(
                    head,
                    context_.clone(),
                    sexp.clone(),
                    Some(eval_list),
                    parent.clone(),
                ));
            }
            SExp::Cons(l, a, b) => {
                eval_list.push(a.clone());
                sexp = b.clone();
            }
            _ => {
                return Err(RunFailure::RunErr(
                    sexp.loc(),
                    format!(
                        "bad argument list {} {}",
                        sexp_.to_string(),
                        context_.to_string()
                    ),
                ));
            }
        }
    }
}

pub fn convert_to_clvm_rs(
    allocator: &mut Allocator,
    head: Rc<SExp>,
) -> Result<NodePtr, RunFailure> {
    match head.borrow() {
        SExp::Nil(_) => Ok(allocator.null()),
        SExp::Atom(l, x) => allocator.new_atom(x).map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!("failed to alloc atom {}", head.to_string()),
            )
        }),
        SExp::QuotedString(_, _, x) => allocator.new_atom(x).map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!("failed to alloc string {}", head.to_string()),
            )
        }),
        SExp::Integer(_, i) => {
            if *i == bi_zero() {
                Ok(allocator.null())
            } else {
                allocator.new_atom(&u8_from_number(i.clone())).map_err(|e| {
                    RunFailure::RunErr(
                        head.loc(),
                        format!("failed to alloc integer {}", head.to_string()),
                    )
                })
            }
        }
        SExp::Cons(_, a, b) => convert_to_clvm_rs(allocator, a.clone()).and_then(|head| {
            convert_to_clvm_rs(allocator, b.clone()).and_then(|tail| {
                allocator.new_pair(head, tail).map_err(|e| {
                    RunFailure::RunErr(
                        a.loc(),
                        format!("failed to alloc cons {}", head.to_string()),
                    )
                })
            })
        }),
    }
}

pub fn convert_from_clvm_rs(
    allocator: &mut Allocator,
    loc: Srcloc,
    head: NodePtr,
) -> Result<Rc<SExp>, RunFailure> {
    match allocator.sexp(head) {
        allocator::SExp::Atom(h) => {
            if h.len() == 0 {
                Ok(Rc::new(SExp::Nil(loc)))
            } else {
                let atom_data = allocator.buf(&h);
                let integer = number_from_u8(atom_data);
                // Ensure that atom values that don't evaluate equal to integers
                // are represented faithfully as atoms.
                if u8_from_number(integer.clone()) == atom_data {
                    Ok(Rc::new(SExp::Integer(loc, integer)))
                } else {
                    Ok(Rc::new(SExp::Atom(loc, atom_data.to_vec())))
                }
            }
        }
        allocator::SExp::Pair(a, b) => {
            convert_from_clvm_rs(allocator, loc.clone(), a).and_then(|h| {
                convert_from_clvm_rs(allocator, loc.clone(), b)
                    .map(|t| Rc::new(SExp::Cons(loc.clone(), h, t)))
            })
        }
    }
}

fn generate_argument_refs(start: Number, sexp: Rc<SExp>) -> Rc<SExp> {
    match sexp.borrow() {
        SExp::Cons(l, a, b) => {
            let next_index = bi_one() + 2_i32.to_bigint().unwrap() * start.clone();
            let tail = generate_argument_refs(next_index, b.clone());
            Rc::new(SExp::Cons(
                l.clone(),
                Rc::new(SExp::Integer(a.loc(), start)),
                tail,
            ))
        }
        _ => sexp.clone(),
    }
}

fn apply_op(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    l: Srcloc,
    head: Rc<SExp>,
    args: Rc<SExp>,
) -> Result<Rc<SExp>, RunFailure> {
    let wrapped_args = Rc::new(SExp::Cons(
        l.clone(),
        Rc::new(SExp::Nil(l.clone())),
        args.clone(),
    ));
    let application = Rc::new(SExp::Cons(
        l.clone(),
        head.clone(),
        generate_argument_refs(5_i32.to_bigint().unwrap(), args.clone()),
    ));
    let converted_app = convert_to_clvm_rs(allocator, application.clone())?;
    let converted_args = convert_to_clvm_rs(allocator, wrapped_args.clone())?;

    runner
        .run_program(allocator, converted_app, converted_args, None)
        .map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!(
                    "{} in {} {}",
                    e.1,
                    application.to_string(),
                    wrapped_args.to_string()
                ),
            )
        })
        .and_then(|v| convert_from_clvm_rs(allocator, head.loc(), v.1))
}

fn atom_value(head: Rc<SExp>) -> Result<Number, RunFailure> {
    match head.borrow() {
        SExp::Integer(_, i) => Ok(i.clone()),
        SExp::Nil(_) => Ok(bi_zero()),
        SExp::QuotedString(_, _, s) => Ok(number_from_u8(s)),
        SExp::Atom(_, s) => Ok(number_from_u8(s)),
        SExp::Cons(l, _, _) => Err(RunFailure::RunErr(
            l.clone(),
            format!("cons is not a number {}", head.to_string()),
        )),
    }
}

pub fn get_history_len(step: Rc<RunStep>) -> usize {
    match step.borrow() {
        RunStep::Done(_, _) => 1,
        RunStep::OpResult(_, _, p) => 1 + get_history_len(p.clone()),
        RunStep::Op(_, _, _, _, p) => 1 + get_history_len(p.clone()),
        RunStep::Step(_, _, p) => 1 + get_history_len(p.clone()),
    }
}

pub fn truthy(sexp: Rc<SExp>) -> bool {
    // Fails for cons, but cons is truthy
    atom_value(sexp.clone()).unwrap_or_else(|_| bi_one()) != bi_zero()
}

pub fn combine(a: &RunStep, b: &RunStep) -> RunStep {
    match (a, b.borrow()) {
        (RunStep::Done(l, x), RunStep::Done(_, _)) => RunStep::Done(l.clone(), x.clone()),
        (RunStep::Done(l, x), RunStep::Op(head, context, args, Some(remain), parent)) => {
            RunStep::Op(
                head.clone(),
                context.clone(),
                Rc::new(SExp::Cons(l.clone(), x.clone(), args.clone())),
                Some(remain.clone()),
                parent.clone(),
            )
        }
        (RunStep::Done(l, x), RunStep::Op(head, context, args, None, parent)) => {
            combine(a, parent.borrow())
        }
        (RunStep::Done(l, x), RunStep::Step(sexp, context, parent)) => combine(a, parent.borrow()),
        _ => a.clone(),
    }
}

pub fn flatten_signed_int(v: Number) -> Number {
    let mut sign_digits = v.to_signed_bytes_le();
    sign_digits.push(0);
    Number::from_signed_bytes_le(&sign_digits)
}

pub fn run_step(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    step_: &RunStep,
) -> Result<RunStep, RunFailure> {
    let mut step = step_.clone();

    match &step {
        RunStep::OpResult(l, x, p) => {
            let parent: &RunStep = p.borrow();
            return Ok(combine(&RunStep::Done(l.clone(), x.clone()), parent));
        }
        RunStep::Done(l, x) => {}
        RunStep::Step(sexp, context, parent) => {
            match sexp.borrow() {
                SExp::Integer(l, v) => {
                    /* An integer picks a value from the context */
                    let flat_v = flatten_signed_int(v.clone());
                    return Ok(RunStep::OpResult(
                        l.clone(),
                        choose_path(
                            l.clone(),
                            flat_v.clone(),
                            flat_v,
                            context.clone(),
                            context.clone(),
                        )?,
                        Rc::new(step_.clone()),
                    ));
                }
                SExp::QuotedString(l, _, v) => {
                    step = RunStep::Step(
                        Rc::new(SExp::Integer(l.clone(), number_from_u8(v))),
                        context.clone(),
                        parent.clone(),
                    );
                }
                SExp::Atom(l, v) => {
                    step = RunStep::Step(
                        Rc::new(SExp::Integer(l.clone(), number_from_u8(v))),
                        context.clone(),
                        parent.clone(),
                    );
                }
                SExp::Nil(l) => {
                    return Ok(RunStep::OpResult(
                        l.clone(),
                        sexp.clone(),
                        Rc::new(step_.clone()),
                    ));
                }
                SExp::Cons(l, a, b) => {
                    let head = Rc::new(
                        translate_head(
                            allocator,
                            runner.clone(),
                            prim_map.clone(),
                            l.clone(),
                            a.clone(),
                            context.clone(),
                        )?
                        .with_loc(l.clone()),
                    );

                    if atom_value(head.clone())? == bi_one() {
                        step = RunStep::Done(l.clone(), b.clone());
                    } else {
                        step = eval_args(
                            allocator,
                            runner.clone(),
                            prim_map.clone(),
                            head.clone(),
                            b.clone(),
                            context.clone(),
                            parent.clone(),
                        )?;
                    }
                }
            }
        }
        RunStep::Op(head, context, tail, Some(rest), parent) => {
            let mut rest_mut = rest.clone();
            match rest_mut.pop() {
                Some(x) => {
                    step = RunStep::Step(
                        x.clone(),
                        context.clone(),
                        Rc::new(RunStep::Op(
                            head.clone(),
                            context.clone(),
                            tail.clone(),
                            Some(rest_mut),
                            parent.clone(),
                        )),
                    );
                }
                None => {
                    step = RunStep::Op(
                        head.clone(),
                        context.clone(),
                        tail.clone(),
                        None,
                        parent.clone(),
                    );
                }
            }
        }
        RunStep::Op(head, context, tail, None, parent) => {
            let aval = atom_value(head.clone())?;
            let apply_atom = 2_i32.to_bigint().unwrap();
            let if_atom = 3_i32.to_bigint().unwrap();
            let cons_atom = 4_i32.to_bigint().unwrap();
            let first_atom = 5_i32.to_bigint().unwrap();
            let rest_atom = 6_i32.to_bigint().unwrap();

            let wanted_args: i32 = if aval == if_atom {
                3
            } else if aval == cons_atom || aval == apply_atom {
                2
            } else if aval == first_atom || aval == rest_atom {
                1
            } else {
                -1
            };

            let op = if aval == apply_atom {
                "apply".to_string()
            } else if aval == if_atom {
                "i (primitive if)".to_string()
            } else if aval == cons_atom {
                "cons".to_string()
            } else if aval == first_atom {
                "first".to_string()
            } else if aval == rest_atom {
                "rest".to_string()
            } else {
                format!("operator {}", aval)
            };

            match tail.proper_list() {
                None => {
                    return Err(RunFailure::RunErr(
                        tail.loc(),
                        format!("Bad arguments given to cons {}", tail.to_string()),
                    ));
                }
                Some(l) => {
                    if wanted_args != -1 && l.len() as i32 != wanted_args {
                        return Err(RunFailure::RunErr(
                            tail.loc(),
                            format!("Wrong number of parameters to {}: {}", op, tail.to_string()),
                        ));
                    }

                    if aval == if_atom {
                        let outcome = if truthy(Rc::new(l[0].clone())) {
                            l[1].clone()
                        } else {
                            l[2].clone()
                        };

                        step = RunStep::Done(outcome.loc(), Rc::new(outcome));
                    } else if aval == cons_atom {
                        return Ok(RunStep::OpResult(
                            head.loc(),
                            Rc::new(SExp::Cons(
                                head.loc(),
                                Rc::new(l[0].clone()),
                                Rc::new(l[1].clone()),
                            )),
                            Rc::new(step_.clone()),
                        ));
                    } else if aval == first_atom || aval == rest_atom {
                        match &l[0] {
                            SExp::Cons(_, a, b) => {
                                if aval == first_atom {
                                    return Ok(RunStep::OpResult(
                                        a.loc(),
                                        a.clone(),
                                        Rc::new(step_.clone()),
                                    ));
                                } else {
                                    return Ok(RunStep::OpResult(
                                        b.loc(),
                                        b.clone(),
                                        Rc::new(step_.clone()),
                                    ));
                                }
                            }
                            _ => {
                                return Err(RunFailure::RunErr(
                                    tail.loc(),
                                    format!("Cons expected for {}, got {}", op, tail.to_string()),
                                ));
                            }
                        }
                    } else if aval == apply_atom {
                        step = RunStep::Step(
                            Rc::new(l[0].clone()),
                            Rc::new(l[1].clone()),
                            parent.clone(),
                        );
                    } else {
                        let result = apply_op(
                            allocator,
                            runner.clone(),
                            head.loc(),
                            head.clone(),
                            tail.clone(),
                        )?;

                        return Ok(RunStep::OpResult(
                            head.loc(),
                            result,
                            Rc::new(step_.clone()),
                        ));
                    }
                }
            }
        }
    }

    Ok(combine(&step, step_))
}

pub fn start_step(sexp_: Rc<SExp>, context_: Rc<SExp>) -> RunStep {
    RunStep::Step(
        sexp_.clone(),
        context_.clone(),
        Rc::new(RunStep::Done(sexp_.loc(), sexp_.clone())),
    )
}

pub fn run(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    sexp_: Rc<SExp>,
    context_: Rc<SExp>,
) -> Result<Rc<SExp>, RunFailure> {
    let mut step = start_step(sexp_.clone(), context_.clone());

    loop {
        step = run_step(allocator, runner.clone(), prim_map.clone(), &step)?;
        match step {
            RunStep::Done(_, x) => {
                return Ok(x);
            }
            _ => {}
        }
    }
}

pub fn parse_and_run(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    file: &String,
    content: &String,
    args: &String,
) -> Result<Rc<SExp>, RunFailure> {
    let code =
        parse_sexp(Srcloc::start(file), content).map_err(|e| RunFailure::RunErr(e.0, e.1))?;
    let args = parse_sexp(Srcloc::start(file), args).map_err(|e| RunFailure::RunErr(e.0, e.1))?;

    if code.len() == 0 {
        Err(RunFailure::RunErr(
            Srcloc::start(file),
            "no code".to_string(),
        ))
    } else if args.len() == 0 {
        Err(RunFailure::RunErr(
            Srcloc::start(file),
            "no args".to_string(),
        ))
    } else {
        let prim_map = prims::prim_map();
        run(
            allocator,
            runner,
            prim_map,
            code[0].clone(),
            args[0].clone(),
        )
    }
}

fn sha256tree_from_atom(v: Vec<u8>) -> Vec<u8> {
    sha256(
        Bytes::new(Some(BytesFromType::Raw(vec![1])))
            .concat(&Bytes::new(Some(BytesFromType::Raw(v)))),
    )
    .data()
    .clone()
}

// sha256tree for modern style SExp
pub fn sha256tree(s: Rc<SExp>) -> Vec<u8> {
    match s.borrow() {
        SExp::Cons(l, a, b) => {
            let t1 = sha256tree(a.clone());
            let t2 = sha256tree(b.clone());
            sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![2])))
                    .concat(&Bytes::new(Some(BytesFromType::Raw(t1))))
                    .concat(&Bytes::new(Some(BytesFromType::Raw(t2)))),
            )
            .data()
            .clone()
        }
        SExp::Nil(_) => sha256tree_from_atom(vec![]),
        SExp::Integer(_, i) => sha256tree_from_atom(u8_from_number(i.clone())),
        SExp::QuotedString(_, _, v) => sha256tree_from_atom(v.clone()),
        SExp::Atom(_, v) => sha256tree_from_atom(v.clone()),
    }
}
