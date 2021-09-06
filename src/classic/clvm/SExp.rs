use std::borrow::Borrow;
use std::fmt::Debug;
use std::mem::swap;
use std::rc::Rc;
use std::string::String;

use bls12_381::G1Affine;

use crate::util::{Number, u8_from_number};
use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Tuple,
    isNone,
    t
};
use crate::classic::clvm::CLVMObject::{CLVMObject};
use crate::classic::clvm::EvalError::EvalError;

pub type SExp = CLVMObject;

// import {CLVMObject, CLVMType} from "./CLVMObject";
// import {Bytes, isIterable, Tuple, t, Stream, isBytes, isTuple} from "./__type_compatibility__";
// import {bigint_from_bytes, bigint_to_bytes, int_from_bytes, int_to_bytes} from "./casts";
// import {sexp_to_stream} from "./serialize";
// import {as_javascript} from "./as_javascript";
// import {EvalError} from "./EvalError";

#[derive(Debug)]
pub enum CastableType {
    CLVMObject(Rc<CLVMObject>),
    Bytes(Bytes),
    String(String),
    Number(Number),
    G1Affine(G1Affine),
    ListOf(usize, Vec<Rc<CastableType>>),
    TupleOf(Rc<CastableType>, Rc<CastableType>)
}

// export function looks_like_clvm_object(o: any): o is CLVMObject {
//   if(!o || typeof o !== "object"){
//     return false;
//   }
  
//   return Boolean("atom" in o && "pair" in o);
// }

// // this function recognizes some common types and turns them into plain bytes
// export function convert_atom_to_bytes(v: any): Bytes {
//   if(isBytes(v)){
//     return v;
//   }
//   else if(typeof v === "string"){
//     return Bytes.from(v, "utf8");
//   }
//   else if(typeof v === "number"){
//     return int_to_bytes(v, {signed: true});
//   }
//   else if(typeof v === "boolean"){ // Tips. In Python, isinstance(True, int) == True. 
//     return int_to_bytes(v ? 1 : 0, {signed: true});
//   }
//   else if(typeof v === "bigint"){
//     return bigint_to_bytes(v, {signed: true});
//   }
//   else if(v === None || !v){
//     return Bytes.NULL;
//   }
//   else if(isIterable(v)){
//     if(v.length > 0){
//       throw new Error(`can't cast ${JSON.stringify(v)} to bytes`);
//     }
//     return Bytes.NULL
//   }
//   else if(typeof v.serialize === "function"){
//     return Bytes.from(v, "G1Element");
//   }
  
//   throw new Error(`can't cast ${JSON.stringify(v)} to bytes`);
// }

#[derive(Debug)]
pub enum SexpStackOp {
    OpConvert,
    OpSetPair(bool, usize),
    OpPrepend(usize)
}

// type operations = typeof op_convert | typeof op_set_left | typeof op_set_right | typeof op_prepend_list;
// type op_target = number | None;

fn replace_stack_top(stack : &mut Vec<CastableType>, v : CastableType) {
    let vlen = stack.len();
    stack[vlen - 1] = v;
}

pub fn to_sexp_type(value: CastableType) -> Result<Rc<CLVMObject>, EvalError> {
    let mut stack = vec!(Rc::new(value));
    let mut ops : Vec<SexpStackOp> = vec!(SexpStackOp::OpConvert);
    let mut op = ops.pop();

    while !isNone(&op) {
        // convert value
        match op {
            None => {
                return Err(EvalError::new_str("empty value stack".to_string()));
            },
            Some(op) => {
                match op.borrow() {
                    SexpStackOp::OpConvert => {
                        let top = stack.pop();
                        match top {
                            None => {
                                return Err(EvalError::new_str("empty value stack".to_string()));
                            },
                            Some(rc) => {
                                match rc.borrow() {
                                    CastableType::CLVMObject(o) => {
                                        stack.push(rc.clone());
                                    },
                                    CastableType::TupleOf(left, right) => {
                                        let targetIndex = stack.len();
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(Rc::new(CLVMObject::Pair(Rc::new(CLVMObject::new()), Rc::new(CLVMObject::new())))))
                                        );

                                        stack.push(right.clone());
                                        ops.push(SexpStackOp::OpSetPair(true, targetIndex)); // set right
                                        ops.push(SexpStackOp::OpConvert); // convert

                                        stack.push(left.clone());
                                        ops.push(SexpStackOp::OpSetPair(false, targetIndex));
                                        ops.push(SexpStackOp::OpConvert);
                                    },
                                    CastableType::ListOf(sel,v) => {
                                        let targetIndex = stack.len();
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(Rc::new(CLVMObject::new())))
                                        );
                                        for i in 0..v.len() - 1 {
                                            stack.push(v[i].clone());
                                            ops.push(SexpStackOp::OpPrepend(targetIndex));
                                            // we only need to convert if it's not already the right type
                                            ops.push(SexpStackOp::OpConvert);
                                        }
                                    },
                                    CastableType::Bytes(b) => {
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(Rc::new(CLVMObject::Atom(b.clone()))))
                                        );
                                    },
                                    CastableType::String(s) => {
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(
                                                Rc::new(CLVMObject::Atom(
                                                    Bytes::new(
                                                        Some(
                                                            BytesFromType::Raw(
                                                                s.as_bytes().into_iter().map(|x| *x).collect()
                                                            )
                                                        )
                                                    )
                                                ))
                                            ))
                                        );
                                    },
                                    CastableType::Number(n) => {
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(
                                                Rc::new(CLVMObject::Atom(
                                                    Bytes::new(
                                                        Some(BytesFromType::Raw(u8_from_number(n.clone())))
                                                    )
                                                ))
                                            ))
                                        );
                                    },
                                    CastableType::G1Affine(g) => {
                                        stack.push(
                                            Rc::new(CastableType::CLVMObject(
                                                Rc::new(CLVMObject::Atom(
                                                    Bytes::new(Some(BytesFromType::G1Element(*g)))
                                                ))
                                            ))
                                        );
                                    }
                                }
                            }
                        }
                    },

                    SexpStackOp::OpSetPair(toset, target) => {
                        match stack.pop() {
                            None => {
                                return Err(EvalError::new_str("empty value stack".to_string()));
                            },
                            Some(top) => {
                                match top.borrow() {
                                    CastableType::CLVMObject(new_value) => {
                                        match stack[*target].borrow() {
                                            CastableType::CLVMObject(target_value) => {
                                                match target_value.borrow() {
                                                    CLVMObject::Pair(l,r) => {
                                                        if *toset {
                                                            stack[*target] =
                                                                Rc::new(CastableType::CLVMObject(
                                                                    Rc::new(CLVMObject::Pair(
                                                                        l.clone(),
                                                                        new_value.clone()
                                                                    ))
                                                                ));
                                                        } else {
                                                            stack[*target] =
                                                                Rc::new(CastableType::CLVMObject(
                                                                    Rc::new(CLVMObject::Pair(
                                                                        new_value.clone(),
                                                                        r.clone()
                                                                    ))
                                                                ));
                                                        }
                                                    },
                                                    CLVMObject::Atom(_) => {
                                                        return Err(
                                                            EvalError::new_str("attempt to set_pair in atom".to_string())
                                                        );
                                                    }
                                                }
                                            },
                                            _ => {
                                                return Err(
                                                    EvalError::new_str(format!(
                                                        "Setting wing of non pair {:?}",
                                                        stack[*target]
                                                    ))
                                                );
                                            }
                                        }
                                    },
                                    _ => {
                                        return Err(
                                            EvalError::new_str(format!(
                                                "op_set_pair on atom item {:?} in vec {:?} ops {:?}",
                                                target,
                                                stack,
                                                ops
                                            ))
                                        );
                                    }
                                }
                            }
                        }
                    },

                    SexpStackOp::OpPrepend(target) => {
                        match stack.pop() {
                            None => {
                                return Err(
                                    EvalError::new_str(
                                        "no pair for prepend".to_string()
                                    )
                                );
                            },

                            Some(top) => {
                                match top.borrow() {
                                    CastableType::CLVMObject(f) => {
                                        match stack[*target].borrow() {
                                            CastableType::CLVMObject(o) => {
                                                stack[*target] =
                                                    Rc::new(CastableType::CLVMObject(
                                                        Rc::new(CLVMObject::Pair(f.clone(), o.clone()))
                                                    ));
                                            },

                                            _ => {
                                                return Err(
                                                    EvalError::new_str(
                                                        format!(
                                                            "unrealized pair prepended {:?}",
                                                            stack[*target]
                                                        )
                                                    )
                                                );
                                            }
                                        }
                                    },

                                    _ => {
                                        return Err(
                                            EvalError::new_str(
                                                format!(
                                                    "unrealized prepend {:?}",
                                                    top
                                                )
                                            )
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        };

        op = ops.pop();
    }

    if stack.len() != 1 {
        return Err(
            EvalError::new_str(format!("too many values left on op stack {:?}", stack))
        );
    }

    return match stack.pop() {
        None => {
            Err(EvalError::new_str("stack empty".to_string()))
        },
        Some(top) => {
            match top.borrow() {
                CastableType::CLVMObject(o) => Ok(o.clone()),
                _ => {
                    Err(EvalError::new_str(format!("unimplemented {:?}", stack[0])))
                }
            }
        }
    };
}

/*
 SExp provides higher level API on top of any object implementing the CLVM
 object protocol.
 The tree of values is not a tree of SExp objects, it's a tree of CLVMObject
 like objects. SExp simply wraps them to privide a uniform view of any
 underlying conforming tree structure.

 The CLVM object protocol (concept) exposes two attributes:
 1. "atom" which is either None or bytes
 2. "pair" which is either None or a tuple of exactly two elements. Both
 elements implementing the CLVM object protocol.
 Exactly one of "atom" and "pair" must be None.
 */
impl SExp {
    pub fn explode(&self) -> Result<Tuple<Rc<SExp>, Rc<SExp>>, EvalError> {
        match self {
            CLVMObject::Pair(f,r) => {
                return Ok(t(f.clone(), r.clone()));
            },
            _ => {
                return Err(
                    EvalError::new_str(
                        format!("explode called on non-pair {:?}", self)
                    )
                );
            }
        }
    }

    pub fn nullp(&self) -> bool {
        match self {
            CLVMObject::Atom(b) => { return b.length() == 0; },
            _ => { return false; }
        }
    }

    pub fn listp(&self) -> bool {
        match self {
            CLVMObject::Atom(_) => { return false; },
            _ => { return true; }
        }
    }

    pub fn first(&self) -> Result<Rc<CLVMObject>, EvalError> {
        return self.explode().map(|t| t.first().clone());
      }

    pub fn rest(&self) -> Result<Rc<SExp>, EvalError> {
        return self.explode().map(|t| t.rest().clone());
    }

    pub fn list_len(&self) -> usize {
        let null = CLVMObject::new();
        let mut v: &SExp = self;
        let mut holder = Rc::new(CLVMObject::new());
        let mut size = 0;

        while v.listp() {
            size += 1;
            match v.rest() {
                Ok(r) => {
                    holder = r.clone();
                    v = &*holder;
                },
                _ => {
                    v = &null;
                }
            };
        }

        return size;
    }

    pub fn as_bytes(&self) -> Result<Bytes, EvalError> {
        match self {
            CLVMObject::Atom(b) => Ok(b.clone()),
            _ => Err(EvalError::new_str("pair converted to bytes".to_string()))
        }
    }
}

pub fn cons(left: Rc<SExp>, right: Rc<SExp>) -> SExp {
    return CLVMObject::Pair(left, right);
}

pub fn bool_sexp(b: bool) -> SExp {
    if b {
        return CLVMObject::Atom(Bytes::new(Some(BytesFromType::Raw(vec!(1)))));
    } else {
        return CLVMObject::new();
    }
}

// export class SExp implements CLVMType {
//   atom: Optional<Bytes> = None;
//   // this is always a 2-tuple of an object implementing the CLVM object protocol.
//   pair: Optional<Tuple<any, any>> = None;
  
//   static readonly TRUE: SExp = new SExp(new CLVMObject(Bytes.from("0x01", "hex")));
//   static readonly FALSE: SExp = new SExp(new CLVMObject(Bytes.NULL));
//   static readonly __NULL__: SExp = new SExp(new CLVMObject(Bytes.NULL));
  
//   static to(v: CastableType): SExp {
//     if(isSExp(v)){
//       return v;
//     }
    
//     if(looks_like_clvm_object(v)){
//       return new SExp(v);
//     }
    
//     // this will lazily convert elements
//     return new SExp(to_sexp_type(v));
//   }
  
//   static null(){
//     return SExp.__NULL__;
//   }
  
//   public as_pair(): Tuple<SExp, SExp>|None {
//     const pair = this.pair;
//     if(pair === None){
//       return pair;
//     }
//     return t(new SExp(pair[0]), new SExp(pair[1]));
//   }
  
//   public as_int(){
//     return int_from_bytes(this.atom, {signed: true});
//   }
  
//   public as_bigint(){
//     return bigint_from_bytes(this.atom, {signed: true});
//   }
  
//   public as_bin(){
//     const f = new Stream();
//     sexp_to_stream(this, f);
//     return f.getValue();
//   }
  
//   public *as_iter(){
//     let v: SExp = this;
//     while(!v.nullp()){
//       yield v.first();
//       v = v.rest();
//     }
//   }
  
//   public equal_to(other: any/* CastableType */): boolean {
//     try{
//       other = SExp.to(other);
//       const to_compare_stack = [t(this, other)] as Array<Tuple<SExp, SExp>>;
//       while(to_compare_stack.length){
//         const [s1, s2] = (to_compare_stack.pop() as Tuple<SExp, SExp>);
//         const p1 = s1.as_pair();
//         if(p1){
//           const p2 = s2.as_pair();
//           if(p2){
//             to_compare_stack.push(t(p1[0], p2[0]));
//             to_compare_stack.push(t(p1[1], p2[1]));
//           }
//           else{
//             return false;
//           }
//         }
//         else if(s2.as_pair() || !(s1.atom && s2.atom && s1.atom.equal_to(s2.atom))){
//           return false;
//         }
//       }
//       return true;
//     }
//     catch(e){
//       return false;
//     }
//   }
  
//   public as_javascript(){
//     return as_javascript(this);
//   }
  
//   public toString(){
//     return this.as_bin().hex();
//   }
  
//   public __repr__(){
//     return `SExp(${this.as_bin().hex()})`;
//   }
// }

// export function isSExp(v: any): v is SExp {
//   return v && typeof v.atom !== "undefined"
//     && typeof v.pair !== "undefined"
//     && typeof v.first === "function"
//     && typeof v.rest === "function"
//     && typeof v.cons === "function"
//   ;
// }
