use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use clvm_rs::allocator;
use clvm_rs::reduction::EvalErr;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{
    bi_zero,
    bi_one
};
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};

use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{
    SExp,
    decode_string,
    parse_sexp
};
use crate::compiler::srcloc::Srcloc;
use crate::util::{
    Number,
    number_from_u8,
    u8_from_number
};

fn choose_path(
    l: Srcloc,
    orig: Number,
    p: Number,
    all: Rc<SExp>,
    context: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    if p == bi_one() {
        Ok(context.clone())
    } else {
        match context.borrow() {
            SExp::Cons(l,a,b) => {
                let next =
                    if p.clone() % 2_i32.to_bigint().unwrap() == bi_zero() {
                        a
                    } else {
                        b
                    };

                choose_path(l.clone(), orig, p/(2_i32.to_bigint().unwrap()), all, next.clone())
            },

            _ => {
                Err(RunFailure::RunErr(
                    l,
                    format!("bad path {} in {}", orig, all.to_string())
                ))
            }
        }
    }
}

fn translate_head(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    l: Srcloc,
    sexp: Rc<SExp>,
    context: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    match sexp.borrow() {
        SExp::Nil(l) => {
            Err(RunFailure::RunErr(l.clone(), "cannot apply nil".to_string()))
        },
        SExp::QuotedString(l,_,v) => {
            translate_head(
                allocator,
                runner,
                prim_map,
                l.clone(),
                Rc::new(SExp::Atom(l.clone(),v.clone())),
                context.clone()
            )
        },
        SExp::Atom(l,v) => {
            match prim_map.get(v) {
                None => {
                    translate_head(
                        allocator,
                        runner,
                        prim_map,
                        l.clone(),
                        Rc::new(SExp::Integer(l.clone(),number_from_u8(v))),
                        context.clone()
                    )
                },
                Some(v) => Ok(v.clone())
            }
        },
        SExp::Integer (_,i) => {
            match prim_map.get(&u8_from_number(i.clone())) {
                None => Ok(sexp.clone()),
                Some(v) => Ok(v.clone())
            }
        },
        SExp::Cons(l,a,nil) => {
            match nil.borrow() {
                SExp::Nil(l1) => {
                    run(
                        allocator,
                        runner,
                        prim_map,
                        Rc::new(SExp::Cons(
                            l.clone(),
                            a.clone(),
                            Rc::new(SExp::Nil(l1.clone()))
                        )),
                        context.clone()
                    )
                },
                _ => Err(RunFailure::RunErr(
                    sexp.loc(),
                    format!("Unexpected head form in clvm {}", sexp.to_string())
                ))
            }
        }
    }
}

fn eval_args(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    args: Rc<SExp>,
    context: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    match args.borrow() {
        SExp::Nil(l) => Ok(args),
        SExp::Cons(l,a,b) => {
            run(
                allocator,
                runner.clone(),
                prim_map.clone(),
                a.clone(),
                context.clone()
            ).and_then(|aval| {
                eval_args(
                    allocator,
                    runner,
                    prim_map,
                    b.clone(),
                    context.clone()
                ).map(|atail| {
                    Rc::new(SExp::Cons(l.clone(),aval,atail))
                })
            })
        },
        _ => Err(RunFailure::RunErr(
            args.loc(),
            format!(
                "bad argument list {} {}",
                args.to_string(),
                context.to_string()
            )
        ))
    }
}

fn convert_to_clvm_rs(
    allocator: &mut Allocator,
    head: Rc<SExp>
) -> Result<NodePtr, RunFailure> {
    match head.borrow() {
        SExp::Nil(_) => Ok(allocator.null()),
        SExp::Atom(l,x) => allocator.new_atom(x).map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!("failed to alloc atom {}", head.to_string())
            )
        }),
        SExp::QuotedString(_,_,x) => allocator.new_atom(x).map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!("failed to alloc string {}", head.to_string())
            )
        }),
        SExp::Integer(_,i) => allocator.new_atom(&u8_from_number(i.clone())).map_err(|e| {
            RunFailure::RunErr(
                head.loc(),
                format!("failed to alloc integer {}", head.to_string())
            )
        }),
        SExp::Cons(_,a,b) => {
            convert_to_clvm_rs(allocator, a.clone()).and_then(|head| {
                convert_to_clvm_rs(allocator, b.clone()).and_then(|tail| {
                    allocator.new_pair(head, tail).map_err(|e| {
                        RunFailure::RunErr(
                            a.loc(),
                            format!("failed to alloc cons {}", head.to_string())
                        )
                    })
                })
            })
        }
    }
}

fn convert_from_clvm_rs(
    allocator: &mut Allocator,
    loc: Srcloc,
    head: NodePtr
) -> Result<Rc<SExp>, RunFailure> {
    match allocator.sexp(head) {
        allocator::SExp::Atom(h) => {
            if h.len() == 0 {
                Ok(Rc::new(SExp::Nil(loc)))
            } else {
                Ok(Rc::new(SExp::Integer(loc, number_from_u8(allocator.buf(&h)))))
            }
        },
        allocator::SExp::Pair(a,b) => {
            convert_from_clvm_rs(allocator, loc.clone(), a).and_then(|h| {
                convert_from_clvm_rs(allocator, loc.clone(), b).map(|t| {
                    Rc::new(SExp::Cons(loc.clone(), h, t))
                })
            })
        }
    }
}

fn generate_argument_refs(start: Number, sexp: Rc<SExp>) -> Rc<SExp> {
    match sexp.borrow() {
        SExp::Cons(l,a,b) => {
            let next_index = bi_one() + 2_i32.to_bigint().unwrap() * start.clone();
            let tail = generate_argument_refs(next_index, b.clone());
            Rc::new(SExp::Cons(
                l.clone(),
                Rc::new(SExp::Integer(a.loc(), start)),
                tail
            ))
        },
        _ => sexp.clone(),
    }
}

fn apply_op(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    l: Srcloc,
    head: Rc<SExp>,
    args: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    let wrapped_args = Rc::new(SExp::Cons(
        l.clone(),
        Rc::new(SExp::Nil(l.clone())),
        args.clone()
    ));
    let application = Rc::new(SExp::Cons(
        l.clone(),
        head.clone(),
        generate_argument_refs(5_i32.to_bigint().unwrap(), args.clone())
    ));
    let converted_app = convert_to_clvm_rs(allocator, application.clone())?;
    let converted_args = convert_to_clvm_rs(allocator, wrapped_args.clone())?;

    runner.run_program(
        allocator,
        converted_app,
        converted_args,
        None
    ).map_err(|e| {
        RunFailure::RunErr(head.loc(), format!("{} in {} {}", e.1, application.to_string(), wrapped_args.to_string()))
    }).and_then(|v| convert_from_clvm_rs(allocator, head.loc(), v.1))
}

fn atom_value(head: Rc<SExp>) -> Result<Number, RunFailure> {
    match head.borrow() {
        SExp::Integer(_, i) => Ok(i.clone()),
        SExp::Nil(_) => Ok(bi_zero()),
        SExp::QuotedString(_,_,s) => Ok(number_from_u8(s)),
        SExp::Atom(_,s) => Ok(number_from_u8(s)),
        SExp::Cons(l,_,_) => {
            Err(RunFailure::RunErr(
                l.clone(),
                format!("cons is not a number {}", head.to_string())
            ))
        }
    }
}

pub fn run(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    sexp_: Rc<SExp>,
    context_: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    let mut sexp = sexp_.clone();
    let mut context = context_.clone();

    loop {
        let sexp_first = sexp.clone();
        let context_first = context.clone();

        match sexp.borrow() {
            SExp::Integer(l,v) => {
                /* An integer picks a value from the context */
                return choose_path(
                    l.clone(),
                    v.clone(),
                    v.clone(),
                    context.clone(),
                    context.clone()
                );
            },
            SExp::QuotedString (l,_,v) => {
                sexp = Rc::new(SExp::Integer(l.clone(), number_from_u8(v)));
            },
            SExp::Atom(l,v) => {
                sexp = Rc::new(SExp::Integer(l.clone(), number_from_u8(v)));
            },
            SExp::Nil(l) => { return Ok(sexp.clone()); },
            SExp::Cons(l,a,b) => {
                let head = translate_head(
                    allocator,
                    runner.clone(),
                    prim_map.clone(),
                    l.clone(),
                    a.clone(),
                    context.clone()
                )?;

                if atom_value(head.clone())? == bi_one() {
                    return Ok(b.clone());
                }

                let tail = eval_args(
                    allocator,
                    runner.clone(),
                    prim_map.clone(),
                    b.clone(),
                    context.clone()
                )?;

                if atom_value(head.clone())? != 2_i32.to_bigint().unwrap() {
                    return apply_op(
                        allocator,
                        runner.clone(),
                        l.clone(),
                        head.clone(),
                        tail.clone()
                    );
                }

                // Handle apply here.
                match tail.proper_list() {
                    None => {
                        return Err(RunFailure::RunErr(
                            b.loc(),
                            format!("Bad parameter list for apply atom {}", b.to_string())
                        ));
                    },
                    Some(l) => {
                        if l.len() != 2 {
                            return Err(RunFailure::RunErr(
                                b.loc(),
                                format!("Wrong parameter list length for apply atom {}", b.to_string())
                            ));
                        }
                        sexp = Rc::new(l[0].clone());
                        context = Rc::new(l[1].clone());
                    }
                }
            }
        }
    }
}

pub fn parse_and_run(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    file: &String,
    content: &String,
    args: &String
) -> Result<Rc<SExp>, RunFailure> {
    let code = parse_sexp(Srcloc::start(file), content).map_err(|e| {
        RunFailure::RunErr(e.0, e.1)
    })?;
    let args = parse_sexp(Srcloc::start(file), args).map_err(|e| {
        RunFailure::RunErr(e.0, e.1)
    })?;

    if code.len() == 0 {
        Err(RunFailure::RunErr(Srcloc::start(file), "no code".to_string()))
    } else if args.len() == 0 {
        Err(RunFailure::RunErr(Srcloc::start(file), "no args".to_string()))
    } else {
        let prim_map = prims::prim_map();
        run(
            allocator, runner, prim_map, code[0].clone(), args[0].clone()
        )
    }
}
