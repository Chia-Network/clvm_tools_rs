use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType};

use crate::compiler::sexp::SExp;
use crate::util::u8_from_number;

/// Given an SExp and a transformation, make a map of the transformed subtrees of
/// the given SExp in code that's indexed by treehash.  This will merge equivalent
/// subtrees but the uses to which it's put will generally work well enough.
///
/// Given how it's used downstream, there'd be no way to disambiguate anyhow.
pub fn build_table_mut<X>(
    code_map: &mut HashMap<String, X>,
    tx: &dyn Fn(&SExp) -> X,
    code: &SExp,
) -> Bytes {
    match code {
        SExp::Cons(_l, a, b) => {
            let left = build_table_mut(code_map, tx, a.borrow());
            let right = build_table_mut(code_map, tx, b.borrow());
            let treehash = sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![2])))
                    .concat(&left)
                    .concat(&right),
            );
            code_map.entry(treehash.hex()).or_insert_with(|| tx(code));
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
        .cloned()
        .unwrap_or_else(|| match code {
            SExp::Cons(l, a, b) => {
                let new_a = relabel_inner_(code_map, swap_table, a.borrow());
                let new_b = relabel_inner_(code_map, swap_table, b.borrow());
                SExp::Cons(l.clone(), Rc::new(new_a), Rc::new(new_b))
            }
            _ => code.clone(),
        })
}

/// Given a map generated from preexisting code, replace value identical subtrees
/// with their rich valued equivalents.
///
/// Consider code that has run through a macro:
///
/// (defmacro M (VAR) VAR)
///
/// vs
///
/// (defmacro M (VAR) (q . 87))
///
/// The raw result of either the integer 87, which doesn't give much clue as
/// to what's intended.  In one case, it *might* be true that VAR was untransformed
/// and the user intends the compiler to check whether downstream uses of W are
/// bound, in the second case, it's clear that won't be intended.
///
/// In classic chialisp, unclaimed identifiers are always treated as constant
/// numbers, but when we're being asked to make things strict, deciding which
/// to do makes things difficult.  Existing macro code assumes it can use unbound
/// words to name functions in the parent frame, among other things and they'll
/// be passed through as atom constants if not bound.
///
/// Relabel here takes a map made from the input of the macro invocation and
/// substitutes any equivalent subtree from before the application, which will
/// retain the form the user gave it.  This is fragile but works for now.
///
/// A way to do this better is planned.
pub fn relabel(code_map: &HashMap<String, SExp>, code: &SExp) -> SExp {
    let mut inv_swap_table = HashMap::new();
    build_swap_table_mut(&mut inv_swap_table, code);
    let mut swap_table = HashMap::new();
    for ent in inv_swap_table.iter() {
        swap_table.insert(ent.1.clone(), ent.0.clone());
    }
    relabel_inner_(code_map, &swap_table, code)
}
