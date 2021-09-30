use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{
    bi_zero,
    bi_one
};

use crate::compiler::comptypes::decode_string;
use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::Srcloc;
use crate::util::{
    Number,
    number_from_u8
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
                prim_map,
                l.clone(),
                Rc::new(SExp::Atom(l.clone(),v.clone())),
                context.clone()
            )
        },
        SExp::Atom(l,v) => {
            match prim_map.get(v) {
                None => {
                    Err(RunFailure::RunErr(
                        l.clone(),
                        format!("Can't find operator '{}'", decode_string(v))
                    ))
                },
                Some(v) => Ok(v.clone())
            }
        },
        SExp::Integer (_,_) => Ok(sexp.clone()),
        SExp::Cons(l,a,nil) => {
            match nil.borrow() {
                SExp::Nil(l1) => {
                    run(
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
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    args: Rc<SExp>,
    context: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    match args.borrow() {
        SExp::Nil(l) => Ok(args),
        SExp::Cons(l,a,b) => {
            run(prim_map.clone(), a.clone(), context.clone()).and_then(|aval| {
                eval_args(prim_map, b.clone(), context.clone()).map(|atail| {
                    Rc::new(SExp::Cons(l.clone(),aval,atail))
                })
            })
        },
        _ => Err(RunFailure::RunErr(args.loc(), "bad argument list".to_string()))
    }
}

fn apply_op(
    l: Srcloc,
    head: Rc<SExp>,
    args: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    Err(RunFailure::RunErr(
        l,
        format!(
            "unimplemented apply prim {} {}",
            head.to_string(),
            args.to_string()
        )
    ))
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
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    sexp: Rc<SExp>,
    context: Rc<SExp>
) -> Result<Rc<SExp>, RunFailure> {
    match sexp.borrow() {
        SExp::Integer(l,v) => {
            /* An integer picks a value from the context */
            choose_path(
                l.clone(),
                v.clone(),
                v.clone(),
                context.clone(),
                context.clone()
            )
        },
        SExp::QuotedString (_,_,_) => {
            Ok(sexp.clone())
        },
        SExp::Atom(l,v) => {
            run(
                prim_map,
                Rc::new(SExp::Integer(l.clone(), number_from_u8(v))),
                context
            )
        },
        SExp::Nil(l) => Ok(sexp.clone()),
        SExp::Cons(l,a,b) => {
            translate_head(
                prim_map.clone(),
                l.clone(),
                a.clone(),
                context.clone()
            ).and_then(|head| {
                if atom_value(head.clone())? == bi_one() {
                    Ok(b.clone())
                } else {
                    eval_args(prim_map, b.clone(), context.clone()).and_then(
                        |tail| apply_op(l.clone(),head.clone(),tail.clone())
                    )
                }
            })
        }
    }
}

pub fn parse_and_run(
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
        run(prim_map, code[0].clone(), args[0].clone())
    }
}
