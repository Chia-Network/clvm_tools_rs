use std::rc::Rc;

use crate::classic::clvm::SExp::{SExp, cons, bool_sexp};
use crate::classic::clvm::__type_compatibility__::{
    Tuple,
    t
};
use crate::classic::clvm::costs::{
    CONS_COST,
    EQ_BASE_COST,
    EQ_COST_PER_BYTE,
    FIRST_COST,
    IF_COST,
    LISTP_COST,
    REST_COST
};
use crate::classic::clvm::EvalError::EvalError;

pub fn op_if(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 3 {
        return Err(EvalError::new(
            "i takes exactly 3 arguments".to_string(),
            args.clone()
        ));
    }

    return args.explode().and_then(|tuple| {
        let f = tuple.first();
        let r = tuple.rest();

        if f.nullp() {
            return r.rest().and_then(|rr| {
                return rr.first().map(|res| t(IF_COST, res));
            });
        }
        return r.first().map(|res| t(IF_COST, res));
    });
}

pub fn op_cons(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 2 {
        return Err(EvalError::new(
            "c takes exactly 2 arguments".to_string(),
            args.clone()
        ));
    }

    return args.explode().and_then(|tuple| {
        let f = tuple.first();
        let r = tuple.rest();
        return r.first().map(|rr| t(CONS_COST, Rc::new(cons(f.clone(), rr))));
    });
}

pub fn op_first(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 1 {
        return Err(EvalError::new(
            "f takes exactly 1 argument".to_string(),
            args.clone()
        ));
    }

    return args.first().and_then(|f| f.first()).map(|f| t(FIRST_COST, f.clone()));
}

pub fn op_rest(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 1 {
        return Err(EvalError::new(
            "r takes exactly 1 argument".to_string(),
            args.clone()
        ));
    }

    return args.first().and_then(|f| f.rest()).map(|r| t(REST_COST, r.clone()));
}

pub fn op_listp(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 1 {
        return Err(EvalError::new(
            "l takes exactly 1 argument".to_string(),
            args.clone()
        ));
    }

    return args.first().map(
        |f| t(LISTP_COST, Rc::new(bool_sexp(f.listp())))
    );
}

pub fn op_raise(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    return Err(EvalError::new("clvm raise".to_string(), args));
}

pub fn op_eq(args: Rc<SExp>) -> Result<Tuple<u64,Rc<SExp>>, EvalError> {
    if args.list_len() != 2 {
        return Err(EvalError::new(
            "= takes exactly 2 arguments".to_string(), args)
        );
    }

    return args.explode().and_then(|tuple| {
        let a0 = tuple.first();
        return tuple.rest().first().and_then(
            |a1| {
                return a0.as_bytes().and_then(
                    |b0| a1.as_bytes().map(|b1| t(b0,b1))
                );
            }
        ).map(|tuple| {
            let b0 = tuple.first();
            let b1 = tuple.rest();
            let cost : u64 = EQ_BASE_COST +
                (b0.length() as u64 + b1.length() as u64) *
                EQ_COST_PER_BYTE;

            return t(cost, Rc::new(bool_sexp(b0.equal_to(b1))));
        });
    });
}
