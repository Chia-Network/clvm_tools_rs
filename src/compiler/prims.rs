use std::rc::Rc;
use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::bi_one;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

pub fn prims() -> Vec<(String, SExp)> {
    let primloc = Srcloc::start(&"*prims*".to_string());
    vec!(
        ("q".to_string(), SExp::Integer (primloc.clone(), 1_u32.to_bigint().unwrap())),
        ("a".to_string(), SExp::Integer (primloc.clone(), 2_u32.to_bigint().unwrap())),
        ("i".to_string(), SExp::Integer (primloc.clone(), 3_u32.to_bigint().unwrap())),
        ("c".to_string(), SExp::Integer (primloc.clone(), 4_u32.to_bigint().unwrap())),
        ("f".to_string(), SExp::Integer (primloc.clone(), 5_u32.to_bigint().unwrap())),
        ("r".to_string(), SExp::Integer (primloc.clone(), 6_u32.to_bigint().unwrap())),
        ("l".to_string(), SExp::Integer (primloc.clone(), 7_u32.to_bigint().unwrap())),
        ("x".to_string(), SExp::Integer (primloc.clone(), 8_u32.to_bigint().unwrap())),
        ("=".to_string(), SExp::Integer (primloc.clone(), 9_u32.to_bigint().unwrap())),
        (">s".to_string(), SExp::Integer (primloc.clone(), 10_u32.to_bigint().unwrap())),
        ("sha256".to_string(), SExp::Integer (primloc.clone(), 11_u32.to_bigint().unwrap())),
        ("substr".to_string(), SExp::Integer (primloc.clone(), 12_u32.to_bigint().unwrap())),
        ("strlen".to_string(), SExp::Integer (primloc.clone(), 13_u32.to_bigint().unwrap())),
        ("concat".to_string(), SExp::Integer (primloc.clone(), 14_u32.to_bigint().unwrap())),
        ("+".to_string(), SExp::Integer (primloc.clone(), 16_u32.to_bigint().unwrap())),
        ("-".to_string(), SExp::Integer (primloc.clone(), 17_u32.to_bigint().unwrap())),
        ("*".to_string(), SExp::Integer (primloc.clone(), 18_u32.to_bigint().unwrap())),
        ("/".to_string(), SExp::Integer (primloc.clone(), 19_u32.to_bigint().unwrap())),
        ("divmod".to_string(), SExp::Integer (primloc.clone(), 20_u32.to_bigint().unwrap())),
        (">".to_string(), SExp::Integer (primloc.clone(), 21_u32.to_bigint().unwrap())),
        ("ash".to_string(), SExp::Integer (primloc.clone(), 22_u32.to_bigint().unwrap())),
        ("lsh".to_string(), SExp::Integer (primloc.clone(), 23_u32.to_bigint().unwrap())),
        ("logand".to_string(), SExp::Integer (primloc.clone(), 24_u32.to_bigint().unwrap())),
        ("logior".to_string(), SExp::Integer (primloc.clone(), 25_u32.to_bigint().unwrap())),
        ("logxor".to_string(), SExp::Integer (primloc.clone(), 26_u32.to_bigint().unwrap())),
        ("lognot".to_string(), SExp::Integer (primloc.clone(), 27_u32.to_bigint().unwrap())),
        ("point_add".to_string(), SExp::Integer (primloc.clone(), 29_u32.to_bigint().unwrap())),
        ("pubkey_for_exp".to_string(), SExp::Integer (primloc.clone(), 30_u32.to_bigint().unwrap())),
        ("not".to_string(), SExp::Integer (primloc.clone(), 32_u32.to_bigint().unwrap())),
        ("any".to_string(), SExp::Integer (primloc.clone(), 33_u32.to_bigint().unwrap())),
        ("all".to_string(), SExp::Integer (primloc.clone(), 34_u32.to_bigint().unwrap())),
        ("softfork".to_string(), SExp::Integer (primloc.clone(), 36_u32.to_bigint().unwrap()))
    )
}

pub fn primquote(l: Srcloc, a: Rc<SExp>) -> SExp {
    SExp::Cons (l.clone(), Rc::new(SExp::Integer (l, bi_one())), a)
}

pub fn primcons(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons (l.clone(), Rc::new(SExp::Integer (l.clone(), 4_u32.to_bigint().unwrap())), Rc::new(SExp::Cons (l.clone(), a, Rc::new(SExp::Cons (l.clone(), b, Rc::new(SExp::Nil(l)))))))
}

pub fn primapply(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons (l.clone(), Rc::new(SExp::Integer (l.clone(), 2_u32.to_bigint().unwrap())), Rc::new(SExp::Cons (l.clone(), a, Rc::new(SExp::Cons (l.clone(), b, Rc::new(SExp::Nil(l)))))))
}

pub fn primexc(l: Srcloc, a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons (l.clone(), Rc::new(SExp::Integer (l.clone(), 8_u32.to_bigint().unwrap())), Rc::new(SExp::Cons (l.clone(), a, Rc::new(SExp::Cons (l.clone(), b, Rc::new(SExp::Nil(l)))))))
}

pub fn primop(l: Srcloc, op: Rc<SExp>, args: Rc<SExp>) -> SExp {
    SExp::Cons (l, op, args)
}

