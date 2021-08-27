use crate::classic::clvm::__type_compatibility__::{Bytes, Tuple};

// import {None, Optional} from "./__python_types__";
// import {Bytes, isTuple, Tuple} from "./__type_compatibility__";
// import {EvalError} from "./EvalError";

pub enum CLVMObject {
    Atom(Bytes),
    Pair(Tuple<Box<CLVMObject>, Box<CLVMObject>>)
}

pub fn nil() -> CLVMObject {
    return CLVMObject::Atom(Bytes::new(None));
}

// /*
//   This class implements the CLVM Object protocol in the simplest possible way,
//   by just having an "atom" and a "pair" field
//  */
// export class CLVMObject implements CLVMType {
//   atom: Optional<Bytes> = None;
//   // this is always a 2-tuple of an object implementing the CLVM object protocol.
//   pair: Optional<Tuple<any, any>> = None;
  
//   public constructor(v: any) {
//     if(isCLVMObject(v)){
//       this.atom = v.atom;
//       this.pair = v.pair;
//     }
//     else if(isTuple(v)){
//       this.pair = v;
//       this.atom = None;
//     }
//     else{
//       this.atom = v;
//       this.pair = None;
//     }
//   }
// }

// export function isAtom(obj: CLVMType): obj is Atom {
//   if((obj.atom && obj.pair) || (!obj.atom && !obj.pair)){
//     throw new EvalError("Invalid clvm", obj);
//   }
  
//   return Boolean(obj.atom && !obj.pair);
// }

// export function isCons(obj: CLVMType): obj is Cons {
//   if((obj.atom && obj.pair) || (!obj.atom && !obj.pair)){
//     throw new EvalError("Invalid clvm", obj);
//   }
  
//   return Boolean((!obj.atom && obj.pair));
// }

// export function isCLVMObject(v: any): v is CLVMObject {
//   return v && typeof v.atom !== "undefined" && typeof v.pair !== "undefined";
// }
