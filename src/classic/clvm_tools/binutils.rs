use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::Record;
use crate::classic::clvm::CLVMObject::CLVMObject;
use crate::classic::clvm::SExp::SExp;
use crate::classic::clvm::{KEYWORD_FROM_ATOM, KEYWORD_TO_ATOM};
use crate::classic::clvm_tools::ir::writer::write_ir;

// import {
//   KEYWORD_FROM_ATOM,
//   KEYWORD_TO_ATOM,
//   int_from_bytes,
//   int_to_bytes,
//   SExp,
//   str,
//   Bytes,
//   int,
//   Tuple,
//   t,
//   h,
// } from "clvm";
// import {read_ir} from "../ir/reader";
// import {write_ir} from "../ir/writer";
// import {
//   ir_as_symbol,
//   ir_cons,
//   ir_first,
//   ir_listp,
//   ir_null,
//   ir_nullp,
//   ir_rest,
//   ir_symbol,
//   ir_val,
//   is_ir,
// } from "../ir/utils";
// import {Type} from "../ir/Type";

// function isPrintable(s: str){
//   // eslint-disable-next-line no-control-regex
//   const regex = /^[0-9a-zA-Z!"#$%&'()*+,-./:;<=>?@\\[\]^_`{|}~ \t\n\r\x0b\x0c]+$/;
//   return regex.test(s);
// }

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

// export function type_for_atom(atom: Bytes): int {
//   if(atom.length > 2){
//     try{
//       const v = atom.decode();
//       if(isPrintable(v)){
//         return Type.QUOTES.i;
//       }
//     }
//     catch (e) {
//       // do nothing
//     }
//     return Type.HEX.i;
//   }
//   if(int_to_bytes(int_from_bytes(atom)).equal_to(atom)){
//     return Type.INT.i;
//   }
//   return Type.HEX.i;
// }

pub fn disassemble_to_ir_with_kw(
  sexp: &SExp,
  keyword_from_atom: &Record<String, String>
) -> SExp {
  // if(is_ir(sexp) && allow_keyword !== false){
  //   return ir_cons(ir_symbol("ir"), sexp);
  // }
  
  // if(sexp.listp()){
  //   if(sexp.first().listp() || allow_keyword !== false){
  //     allow_keyword = true as A;
  //   }
  //   const v0 = disassemble_to_ir(sexp.first(), keyword_from_atom, allow_keyword);
  //   const v1 = disassemble_to_ir(sexp.rest(), keyword_from_atom, false);
  //   return ir_cons(v0, v1);
  // }
  
  // const as_atom = sexp.atom as Bytes;
  // if(allow_keyword){
  //   const v = keyword_from_atom[as_atom.hex()];
  //   if(v && v !== "."){
  //     // eslint-disable-next-line @typescript-eslint/ban-ts-comment
  //     // @ts-ignore
  //     return ir_symbol(v); // @todo Find a good way not to use `ts-ignore`
  //   }
  // }
  
  // if(sexp.nullp()){
  //   return ir_null();
  // }
  
    // return SExp.to(t(type_for_atom(as_atom), as_atom));
    return CLVMObject::new();
}

pub fn disassemble_with_kw(
    sexp: &SExp, keyword_from_atom: &Record<String, String>
) -> String {
  let symbols = disassemble_to_ir_with_kw(sexp, &keyword_from_atom);
  return write_ir(Rc::new(symbols));
}

pub fn disassemble(sexp: Rc<SExp>) -> String {
    return disassemble_with_kw(&sexp, KEYWORD_TO_ATOM());
}

// export function assemble(s: str){
//   const symbols = read_ir(s);
//   return assemble_from_ir(symbols);
// }
