use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm::sexp::equal_to;
use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use std::collections::HashMap;

pub const ATOM_MATCH: [u8; 1] = [b'$'];
pub const SEXP_MATCH: [u8; 1] = [b':'];

pub fn unify_bindings(
    allocator: &mut Allocator,
    bindings: HashMap<String, NodePtr>,
    new_key: &[u8],
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

pub fn match_sexp(
    allocator: &mut Allocator,
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
        (SExp::Atom, SExp::Atom) => {
            // Two nodes in scope, both used.
            if allocator.atom(pattern) == allocator.atom(sexp) {
                Some(known_bindings)
            } else {
                None
            }
        }
        (SExp::Pair(pleft, pright), _) => match (allocator.sexp(pleft), allocator.sexp(pright)) {
            (SExp::Atom, SExp::Atom) => {
                let pright_atom = allocator.atom(pright).to_vec();
                match allocator.sexp(sexp) {
                    SExp::Atom => {
                        // Expression is ($ . $), sexp is '$', result: no capture.
                        // Avoid double borrow.
                        if allocator.atom(pleft) == ATOM_MATCH {
                            if allocator.atom(pright) == ATOM_MATCH {
                                if allocator.atom(sexp) == ATOM_MATCH {
                                    return Some(HashMap::new());
                                }
                                return None;
                            }

                            return unify_bindings(allocator, known_bindings, &pright_atom, sexp);
                        }
                        if allocator.atom(pleft) == SEXP_MATCH {
                            if allocator.atom(pright) == SEXP_MATCH
                                && allocator.atom(sexp) == SEXP_MATCH
                            {
                                return Some(HashMap::new());
                            }

                            return unify_bindings(
                                allocator,
                                known_bindings,
                                // pat_right_bytes
                                &pright_atom,
                                sexp,
                            );
                        }

                        None
                    }
                    SExp::Pair(sleft, sright) => {
                        if allocator.atom(pleft) == SEXP_MATCH
                            && allocator.atom(pright) != SEXP_MATCH
                        {
                            return unify_bindings(
                                allocator,
                                known_bindings,
                                // pat_right_bytes
                                &pright_atom,
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
                SExp::Atom => None,
                SExp::Pair(sleft, sright) => match_sexp(allocator, pleft, sleft, known_bindings)
                    .and_then(|new_bindings| match_sexp(allocator, pright, sright, new_bindings)),
            },
        },
        (SExp::Atom, _) => None,
    }
}
