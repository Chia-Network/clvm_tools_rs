use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType};

use crate::compiler::sexp::SExp;
use crate::util::u8_from_number;

pub fn build_table_mut<X>(
    code_map: &mut HashMap<String, X>,
    tx: &dyn Fn(&SExp) -> X,
    code: &SExp,
) -> Bytes {
    match code {
        SExp::Cons(l, a, b) => {
            let left = build_table_mut(code_map, tx, a.borrow());
            let right = build_table_mut(code_map, tx, b.borrow());
            let treehash = sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![2])))
                    .concat(&left)
                    .concat(&right),
            );
            if !code_map.contains_key(&treehash.hex()) {
                code_map.insert(treehash.hex(), tx(code));
            }
            treehash
        }
        SExp::Atom(_, a) => {
            let treehash = sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![1])))
                    .concat(&Bytes::new(Some(BytesFromType::Raw(a.clone())))),
            );
            code_map.insert(treehash.hex(), tx(code));
            treehash
        }
        SExp::QuotedString(l, _, a) => {
            build_table_mut(code_map, tx, &SExp::Atom(l.clone(), a.clone()))
        }
        SExp::Integer(l, i) => build_table_mut(
            code_map,
            tx,
            &SExp::Atom(l.clone(), u8_from_number(i.clone())),
        ),
        SExp::Nil(l) => build_table_mut(code_map, tx, &SExp::Atom(l.clone(), Vec::new())),
    }
}

pub fn build_symbol_table_mut(code_map: &mut HashMap<String, String>, code: &SExp) -> Bytes {
    build_table_mut(code_map, &|sexp| sexp.loc().to_string(), code)
}

pub fn build_swap_table_mut(code_map: &mut HashMap<String, SExp>, code: &SExp) -> Bytes {
    build_table_mut(code_map, &|sexp| sexp.clone(), code)
}

fn relabel_inner_(
    code_map: &HashMap<String, SExp>,
    swap_table: &HashMap<SExp, String>,
    code: &SExp,
) -> SExp {
    swap_table
        .get(code)
        .and_then(|res| code_map.get(res))
        .map(|x| x.clone())
        .unwrap_or_else(|| match code {
            SExp::Cons(l, a, b) => {
                let new_a = relabel_inner_(code_map, swap_table, a.borrow());
                let new_b = relabel_inner_(code_map, swap_table, b.borrow());
                SExp::Cons(l.clone(), Rc::new(new_a), Rc::new(new_b))
            }
            _ => code.clone(),
        })
}

pub fn relabel(code_map: &HashMap<String, SExp>, code: &SExp) -> SExp {
    let mut inv_swap_table = HashMap::new();
    build_swap_table_mut(&mut inv_swap_table, code);
    let mut swap_table = HashMap::new();
    for ent in inv_swap_table.iter() {
        swap_table.insert(ent.1.clone(), ent.0.clone());
    }
    relabel_inner_(code_map, &swap_table, code)
}
