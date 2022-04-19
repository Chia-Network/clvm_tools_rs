use num_bigint::ToBigInt;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

pub fn prims() -> Vec<(Vec<u8>, SExp)> {
    let primloc = Srcloc::start(&"*prims*".to_string());
    vec![
        (
            "q".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 1_u32.to_bigint().unwrap()),
        ),
        (
            "a".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 2_u32.to_bigint().unwrap()),
        ),
        (
            "i".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 3_u32.to_bigint().unwrap()),
        ),
        (
            "c".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 4_u32.to_bigint().unwrap()),
        ),
        (
            "f".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 5_u32.to_bigint().unwrap()),
        ),
        (
            "r".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 6_u32.to_bigint().unwrap()),
        ),
        (
            "l".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 7_u32.to_bigint().unwrap()),
        ),
        (
            "x".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 8_u32.to_bigint().unwrap()),
        ),
        (
            "=".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 9_u32.to_bigint().unwrap()),
        ),
        (
            ">s".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 10_u32.to_bigint().unwrap()),
        ),
        (
            "sha256".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 11_u32.to_bigint().unwrap()),
        ),
        (
            "substr".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 12_u32.to_bigint().unwrap()),
        ),
        (
            "strlen".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 13_u32.to_bigint().unwrap()),
        ),
        (
            "concat".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 14_u32.to_bigint().unwrap()),
        ),
        (
            "+".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 16_u32.to_bigint().unwrap()),
        ),
        (
            "-".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 17_u32.to_bigint().unwrap()),
        ),
        (
            "*".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 18_u32.to_bigint().unwrap()),
        ),
        (
            "/".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 19_u32.to_bigint().unwrap()),
        ),
        (
            "divmod".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 20_u32.to_bigint().unwrap()),
        ),
        (
            ">".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 21_u32.to_bigint().unwrap()),
        ),
        (
            "ash".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 22_u32.to_bigint().unwrap()),
        ),
        (
            "lsh".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 23_u32.to_bigint().unwrap()),
        ),
        (
            "logand".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 24_u32.to_bigint().unwrap()),
        ),
        (
            "logior".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 25_u32.to_bigint().unwrap()),
        ),
        (
            "logxor".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 26_u32.to_bigint().unwrap()),
        ),
        (
            "lognot".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 27_u32.to_bigint().unwrap()),
        ),
        (
            "point_add".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 29_u32.to_bigint().unwrap()),
        ),
        (
            "pubkey_for_exp".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 30_u32.to_bigint().unwrap()),
        ),
        (
            "not".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 32_u32.to_bigint().unwrap()),
        ),
        (
            "any".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 33_u32.to_bigint().unwrap()),
        ),
        (
            "all".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 34_u32.to_bigint().unwrap()),
        ),
        (
            "softfork".as_bytes().to_vec(),
            SExp::Integer(primloc.clone(), 36_u32.to_bigint().unwrap()),
        ),
    ]
}

pub fn prim_map() -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
    let mut out_map = HashMap::new();
    for p in prims() {
        out_map.insert(p.0, Rc::new(p.1));
    }
    Rc::new(out_map)
}

pub fn primquote(l: Srcloc, a: Rc<SExp>) -> SExp {
    SExp::Cons(l.clone(), Rc::new(SExp::Integer(l, bi_one())), a)
}

pub fn primcons(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons(
        l.clone(),
        Rc::new(SExp::Integer(l.clone(), 4_u32.to_bigint().unwrap())),
        Rc::new(SExp::Cons(
            l.clone(),
            a,
            Rc::new(SExp::Cons(l.clone(), b, Rc::new(SExp::Nil(l)))),
        )),
    )
}

pub fn primapply(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons(
        l.clone(),
        Rc::new(SExp::Integer(l.clone(), 2_u32.to_bigint().unwrap())),
        Rc::new(SExp::Cons(
            l.clone(),
            a,
            Rc::new(SExp::Cons(l.clone(), b, Rc::new(SExp::Nil(l)))),
        )),
    )
}

pub fn primexc(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons(
        l.clone(),
        Rc::new(SExp::Integer(l.clone(), 8_u32.to_bigint().unwrap())),
        Rc::new(SExp::Cons(
            l.clone(),
            a,
            Rc::new(SExp::Cons(l.clone(), b, Rc::new(SExp::Nil(l)))),
        )),
    )
}

pub fn primop(l: Srcloc, op: Rc<SExp>, args: Rc<SExp>) -> SExp {
    SExp::Cons(l, op, args)
}
