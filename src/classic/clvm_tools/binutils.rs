use std::borrow::Borrow;
use std::rc::Rc;

use encoding8::ascii::is_printable;
use unicode_segmentation::UnicodeSegmentation;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    Record
};
use crate::classic::clvm::CLVMObject::CLVMObject;
use crate::classic::clvm::SExp::SExp;
use crate::classic::clvm::{
    KEYWORD_TO_ATOM,
    KEYWORD_FROM_ATOM
};
use crate::classic::clvm_tools::ir::Type::IRRepr;
use crate::classic::clvm_tools::ir::writer::write_ir;

pub fn is_printable_string(s: &String) -> bool {
    for ch in s.graphemes(true) {
        if ch.chars().nth(0).unwrap() > 0xff as char || !is_printable(ch.chars().nth(0).unwrap() as u8) {
            return false;
        }
    }
    return true;
}

// export function assemble_from_ir(ir_sexp: SExp): SExp {
//   let keyword = ir_as_symbol(ir_sexp);
//   if(keyword){
//     if(keyword[0] === "#"){
//       keyword = keyword.substring(1);
//     }
//     const atom = KEYWORD_TO_ATOM[keyword as keyof typeof KEYWORD_TO_ATOM];
//     if(atom){
//       return SExp.to(h(atom));
//     }
//     else{
//       return ir_val(ir_sexp);
//     }
//     // Original code raises an Error, which never reaches.
//     // throw new SyntaxError(`can't parse ${keyrowd} at ${ir_sexp._offset}`);
//   }
  
//   if(!ir_listp(ir_sexp)){
//     return ir_val(ir_sexp);
//   }
  
//   if(ir_nullp(ir_sexp)){
//     return SExp.to([]);
//   }
  
//   // handle "q"
//   const first = ir_first(ir_sexp);
//   keyword = ir_as_symbol(first);
//   if(keyword === "q"){
//     // pass;
//   }
  
//   const sexp_1 = assemble_from_ir(first);
//   const sexp_2 = assemble_from_ir(ir_rest(ir_sexp));
//   return sexp_1.cons(sexp_2);
// }

pub fn ir_for_atom(atom: &Bytes, allow_keyword: bool) -> IRRepr {
    if atom.length() == 0 {
        return IRRepr::Null;
    }
    if atom.length() > 2 {
        match String::from_utf8(atom.data().to_vec()) {
            Ok(v) => {
                if is_printable_string(&v) {
                    return IRRepr::Quotes(atom.clone());
                }
            },
            _ => { }
        }
        // Determine whether the bytes identity an integer in canonical form.
    } else {
        if allow_keyword {
            match KEYWORD_FROM_ATOM.get(atom.data()) {
                Some(kw) => { return IRRepr::Symbol(kw.to_string()); },
                _ => { }
            }
        }

        if atom.length() == 1 || (atom.length() > 1 && atom.data()[0] != 0) {
            return IRRepr::Int(atom.clone(), true);
        }
    }
    return IRRepr::Hex(atom.clone());
}

/*
 * (2 2 (2) (2 3 4)) => (a 2 (a) (a 3 4))
 *
 * d(P(2,P(2,P(P(2,()),P(P(2,P(3,P(4))))))), head=true)
 * a(2,true); d(P(2,P(P(2,()),P(P(2,P(3,P(4)))))), head=false)
 * a(2,false); d(P(P(2,()),P(P(2,P(3,P(4))))), head=false)
 * d(P(2,()), head=true); d(P(P(2,P(3,P(4)))), head=false)
 * a(2,true); d((), head=false); d(P(P(2,P(3,P(4)))), head=false)
 * a((),false); d(P(P(2,P(3,P(4)))), head=false)
 */
pub fn disassemble_to_ir_with_kw(
    sexp: Rc<SExp>,
    keyword_from_atom: &Record<String, Vec<u8>>,
    head: bool,
    allow_keyword: bool
) -> IRRepr {
    match sexp.borrow() {
        CLVMObject::Pair(l,r) => {
            let new_head =
                match l.borrow() {
                    CLVMObject::Pair(_,_) => true,
                    _ => head
                };

            let v0 =
                disassemble_to_ir_with_kw(
                    l.clone(), keyword_from_atom, new_head, allow_keyword
                );
            let v1 =
                disassemble_to_ir_with_kw(
                    r.clone(), keyword_from_atom, false, allow_keyword
                );
            return IRRepr::Cons(Rc::new(v0), Rc::new(v1));
        },

        CLVMObject::Atom(a) => { return ir_for_atom(a, head && allow_keyword); }
    }
}

pub fn disassemble_with_kw(
    sexp: Rc<SExp>, keyword_from_atom: &Record<String, Vec<u8>>
) -> String {
  let symbols = disassemble_to_ir_with_kw(sexp, &keyword_from_atom, true, true);
  return write_ir(Rc::new(symbols));
}

pub fn disassemble(sexp: Rc<SExp>) -> String {
    return disassemble_with_kw(sexp.clone(), &KEYWORD_TO_ATOM);
}

// export function assemble(s: str){
//   const symbols = read_ir(s);
//   return assemble_from_ir(symbols);
// }
