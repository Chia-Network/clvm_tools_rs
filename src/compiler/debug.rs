use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    sha256,
    bi_zero
};

use crate::compiler::sexp::SExp;
use crate::util::u8_from_number;

pub fn sha256tree(sexp: &SExp) -> Bytes {
    match sexp.borrow() {
        SExp::Cons(_,l,r) => {
            let left = sha256tree(l.borrow());
            let right = sha256tree(r.borrow());
            return sha256(
                Bytes::new(Some(BytesFromType::Raw(vec!(2)))).
                    concat(&left).concat(&right)
            );
        },
        SExp::Atom(_,a) => {
            return sha256(
                Bytes::new(Some(BytesFromType::Raw(vec!(1)))).
                    concat(&Bytes::new(Some(BytesFromType::Raw(a.clone()))))
            );
        },
        SExp::QuotedString(l,_,a) => {
            return sha256tree(&SExp::Atom(l.clone(),a.clone()));
        },
        SExp::Integer(l,i) => {
            return sha256tree(&SExp::Atom(l.clone(),u8_from_number(i.clone())));
        },
        SExp::Nil(l) => {
            return sha256tree(&SExp::Integer(l.clone(),bi_zero()));
        }
    }
}

pub fn build_symbol_table_mut(
    code_map: &mut HashMap<String, String>,
    code: &SExp
) {
    match code {
        SExp::Cons(l,a,b) => {
            build_symbol_table_mut(code_map, a.borrow());
            build_symbol_table_mut(code_map, b.borrow());
            let treehash = sha256tree(code);
            code_map.insert(treehash.hex(), l.to_string());
        },
        _ => {
            let treehash = sha256tree(code);
            code_map.insert(treehash.hex(), code.loc().to_string());
        }
    }
}
