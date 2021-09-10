// import {Atom, Bytes, None, SExp, str, b} from "clvm";

lazy_static! {
    pub static ref ATOM_MATCH = vec!('$' as u8);
    pub static ref SEXP_MATCH = vec!(':' as u8);
}

export function unify_bindings(bindings: Record<str, SExp>, new_key: Bytes, new_value: SExp){
  /*
    Try to add a new binding to the list, rejecting it if it conflicts
    with an existing binding.
   */
  const new_key_str = new_key.decode();
  if(new_key_str in bindings){
    if(!bindings[new_key_str].equal_to(new_value)){
      return None;
    }
    return bindings;
  }
  const new_bindings = {...bindings};
  new_bindings[new_key_str] = new_value;
  return new_bindings;
}

pub fn match_sexp(pattern: NodePtr, sexp: NodePtr, known_bindings: Record<str, NodePtr> = {}): Record<str, NodePtr> {
  /*
    Determine if sexp matches the pattern, with the given known bindings already applied.
    Returns None if no match, or a (possibly empty) dictionary of bindings if there is a match
    Patterns look like this:
    ($ . $) matches the literal "$", no bindings (mostly useless)
    (: . :) matches the literal ":", no bindings (mostly useless)
    ($ . A) matches B if B is an atom; and A is bound to B
    (: . A) matches B always; and A is bound to B
    (A . B) matches (C . D) if A matches C and B matches D
          and bindings are the unification (as long as unification is possible)
   */
  
  if(!pattern.listp()){
    if(sexp.listp()){
      return None;
    }
    return (pattern as Atom).atom.equal_to((sexp as Atom).atom) ? known_bindings : None;
  }
  
  const left = pattern.first();
  const right = pattern.rest();
  const atom = sexp.atom;
  
  if(left.equal_to(ATOM_MATCH)){
    if(sexp.listp()){
      return None;
    }
    if(right.equal_to(ATOM_MATCH)){
      if(atom?.equal_to(ATOM_MATCH)){
        return {};
      }
      return None;
    }
    return unify_bindings(known_bindings, right.atom as Bytes, sexp);
  }
  
  if(left.equal_to(SEXP_MATCH)){
    if(right.equal_to(SEXP_MATCH)){
      if(atom?.equal_to(SEXP_MATCH)){
        return {};
      }
      return None;
    }
    return unify_bindings(known_bindings, right.atom as Bytes, sexp);
  }
  
  if(!sexp.listp()){
    return None;
  }
  
  const new_bindings = match(left, sexp.first(), known_bindings);
  if(new_bindings === None){
    return new_bindings;
  }
  return match(right, sexp.rest(), new_bindings);
}
