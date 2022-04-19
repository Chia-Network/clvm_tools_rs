use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm::sexp::equal_to;
use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use std::collections::HashMap;

lazy_static! {
    pub static ref ATOM_MATCH: Vec<u8> = {
        return vec!['$' as u8];
    };
    pub static ref SEXP_MATCH: Vec<u8> = {
        return vec![':' as u8];
    };
}

pub fn unify_bindings<'a>(
    allocator: &'a mut Allocator,
    bindings: HashMap<String, NodePtr>,
    new_key: &Vec<u8>,
    new_value: NodePtr,
) -> Option<HashMap<String, NodePtr>> {
    /*
     * Try to add a new binding to the list, rejecting it if it conflicts
     * with an existing binding.
     */
    let new_key_str = Bytes::new(Some(BytesFromType::Raw(new_key.to_vec()))).decode();
    match bindings.get(&new_key_str) {
        Some(binding) => {
            if !equal_to(allocator, *binding, new_value) {
                return None;
            }
            Some(bindings)
        }
        _ => {
            let mut new_bindings = bindings.clone();
            new_bindings.insert(new_key_str, new_value);
            Some(new_bindings)
        }
    }
}

pub fn match_sexp<'a>(
    allocator: &'a mut Allocator,
    pattern: NodePtr,
    sexp: NodePtr,
    known_bindings: HashMap<String, NodePtr>,
) -> Option<HashMap<String, NodePtr>> {
    /*
     * Determine if sexp matches the pattern, with the given known bindings already applied.
     * Returns None if no match, or a (possibly empty) dictionary of bindings if there is a match
     * Patterns look like this:
     * ($ . $) matches the literal "$", no bindings (mostly useless)
     * (: . :) matches the literal ":", no bindings (mostly useless)
     * ($ . A) matches B if B is an atom; and A is bound to B
     * (: . A) matches B always; and A is bound to B
     * (A . B) matches (C . D) if A matches C and B matches D
     *         and bindings are the unification (as long as unification is possible)
     */

    match (allocator.sexp(pattern), allocator.sexp(sexp)) {
        (SExp::Atom(pat_buf), SExp::Atom(sexp_buf)) => {
            let sexp_bytes = allocator.buf(&sexp_buf).to_vec();
            if allocator.buf(&pat_buf).to_vec() == sexp_bytes {
                Some(known_bindings)
            } else {
                None
            }
        }
        (SExp::Pair(pleft, pright), _) => match (allocator.sexp(pleft), allocator.sexp(pright)) {
            (SExp::Atom(pat_left), SExp::Atom(pat_right)) => {
                let pat_right_bytes = allocator.buf(&pat_right).to_vec();
                let pat_left_bytes = allocator.buf(&pat_left).to_vec();

                match allocator.sexp(sexp) {
                    SExp::Atom(sexp_buf) => {
                        let sexp_bytes = allocator.buf(&sexp_buf).to_vec();
                        if pat_left_bytes == ATOM_MATCH.to_vec() {
                            if pat_right_bytes == ATOM_MATCH.to_vec() {
                                if sexp_bytes == ATOM_MATCH.to_vec() {
                                    return Some(HashMap::new());
                                }
                                return None;
                            }

                            return unify_bindings(
                                allocator,
                                known_bindings,
                                &pat_right_bytes,
                                sexp,
                            );
                        }
                        if pat_left_bytes == SEXP_MATCH.to_vec() {
                            if pat_right_bytes == SEXP_MATCH.to_vec()
                                && sexp_bytes == SEXP_MATCH.to_vec()
                            {
                                return Some(HashMap::new());
                            }

                            return unify_bindings(
                                allocator,
                                known_bindings,
                                &pat_right_bytes,
                                sexp,
                            );
                        }

                        None
                    }
                    SExp::Pair(sleft, sright) => {
                        if pat_left_bytes == SEXP_MATCH.to_vec()
                            && pat_right_bytes != SEXP_MATCH.to_vec()
                        {
                            return unify_bindings(
                                allocator,
                                known_bindings,
                                &pat_right_bytes,
                                sexp,
                            );
                        }

                        match_sexp(allocator, pleft, sleft, known_bindings).and_then(
                            |new_bindings| match_sexp(allocator, pright, sright, new_bindings),
                        )
                    }
                }
            }
            _ => match allocator.sexp(sexp) {
                SExp::Atom(_) => None,
                SExp::Pair(sleft, sright) => match_sexp(allocator, pleft, sleft, known_bindings)
                    .and_then(|new_bindings| match_sexp(allocator, pright, sright, new_bindings)),
            },
        },
        (SExp::Atom(_), _) => None,
    }
}
