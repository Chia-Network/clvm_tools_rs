use std::borrow::Borrow;
use std::fmt::Debug;
use std::rc::Rc;
use std::string::String;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::reduction::EvalErr;

use bls12_381::G1Affine;

use crate::util::{Number, u8_from_number};
use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};
use crate::classic::clvm::serialize::sexp_to_stream;

// import {CLVMObject, CLVMType} from "./CLVMObject";
// import {Bytes, isIterable, Tuple, t, Stream, isBytes, isTuple} from "./__type_compatibility__";
// import {bigint_from_bytes, bigint_to_bytes, int_from_bytes, int_to_bytes} from "./casts";
// import {sexp_to_stream} from "./serialize";
// import {as_javascript} from "./as_javascript";
// import {EvalError} from "./EvalError";

#[derive(Debug)]
pub enum CastableType {
    CLVMObject(NodePtr),
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

pub fn to_sexp_type<'a>(allocator: &'a mut Allocator, value: CastableType) -> Result<NodePtr, EvalErr> {
    let mut stack = vec!(Rc::new(value));
    let mut ops : Vec<SexpStackOp> = vec!(SexpStackOp::OpConvert);

    loop {
        let mut op = SexpStackOp::OpConvert;

        match ops.pop() {
            None => { break; },
            Some(o) => { op = o; }
        }

        let mut top =
            Rc::new(CastableType::CLVMObject(allocator.null()));

        match stack.pop() {
            None => {
                return Err(EvalErr(allocator.null(), "empty value stack".to_string()));
            },
            Some(rc) => { top = rc; }
        }

        // convert value
        match op {
            SexpStackOp::OpConvert => {
                match top.borrow() {
                    CastableType::CLVMObject(_) => {
                        stack.push(top.clone());
                    },
                    CastableType::TupleOf(left, right) => {
                        let target_index = stack.len();
                        match allocator.new_pair(allocator.null(), allocator.null()) {
                            Ok(pair) => {
                                stack.push(
                                    Rc::new(
                                        CastableType::CLVMObject(pair)
                                    )
                                );
                            },
                            Err(e) => { return Err(e); }
                        };
                        stack.push(right.clone());
                        ops.push(SexpStackOp::OpSetPair(true, target_index)); // set right
                        ops.push(SexpStackOp::OpConvert); // convert

                        stack.push(left.clone());
                        ops.push(SexpStackOp::OpSetPair(false, target_index));
                        ops.push(SexpStackOp::OpConvert);
                    },
                    CastableType::ListOf(_sel,v) => {
                        let target_index = stack.len();
                        stack.push(
                            Rc::new(CastableType::CLVMObject(allocator.null()))
                        );
                        for i in 0..v.len() - 1 {
                            stack.push(v[i].clone());
                            ops.push(SexpStackOp::OpPrepend(target_index));
                            // we only need to convert if it's not already the right type
                            ops.push(SexpStackOp::OpConvert);
                        }
                    },
                    CastableType::Bytes(b) => {
                        match allocator.new_atom(b.data()) {
                            Ok(a) => {
                                stack.push(
                                    Rc::new(CastableType::CLVMObject(a))
                                );
                            },
                            Err(e) => { return Err(e); }
                        }
                    },
                    CastableType::String(s) => {
                        let result_vec : Vec<u8> = s.as_bytes().into_iter().map(|x| *x).collect();
                        match allocator.new_atom(&result_vec) {
                            Ok(a) => {
                                stack.push(
                                    Rc::new(CastableType::CLVMObject(a))
                                );
                            },
                            Err(e) => { return Err(e); }
                        };
                    },
                    CastableType::Number(n) => {
                        match allocator.new_atom(&u8_from_number(n.clone())) {
                            Ok(a) => {
                                stack.push(
                                    Rc::new(CastableType::CLVMObject(a))
                                );
                            },
                            Err(e) => { return Err(e); }
                        }
                    },
                    CastableType::G1Affine(g) => {
                        let bytes_ver =
                            Bytes::new(Some(BytesFromType::G1Element(*g)));

                        match allocator.new_atom(bytes_ver.data()) {
                            Ok(a) => {
                                stack.push(
                                    Rc::new(CastableType::CLVMObject(a))
                                );
                            },
                            Err(e) => { return Err(e); }
                        }
                    }
                }
            },
            SexpStackOp::OpSetPair(toset, target) => {
                match top.borrow() {
                    CastableType::CLVMObject(new_value) => {
                        match stack[target].borrow() {
                            CastableType::CLVMObject(target_value) => {
                                match allocator.sexp(*target_value) {
                                    SExp::Pair(l,r) => {
                                        if toset {
                                            match allocator.new_pair(
                                                l,
                                                *new_value
                                            ) {
                                                Ok(pair) => {
                                                    stack[target] =
                                                        Rc::new(CastableType::CLVMObject(pair));
                                                },
                                                Err(e) => { return Err(e); }
                                            }
                                        } else {
                                            match allocator.new_pair(
                                                *new_value,
                                                r
                                            ) {
                                                Ok(pair) => {
                                                    stack[target] =
                                                        Rc::new(CastableType::CLVMObject(pair));
                                                },
                                                Err(e) => { return Err(e); }
                                            }
                                        }
                                    },
                                    SExp::Atom(_) => {
                                        return Err(
                                            EvalErr(*target_value, "attempt to set_pair in atom".to_string())
                                        );
                                    }
                                }
                            },
                            _ => {
                                return Err(
                                    EvalErr(
                                        allocator.null(),
                                        format!(
                                            "Setting wing of non pair {:?}",
                                            stack[target]
                                        )
                                    )
                                );
                            }
                        }
                    },
                    _ => {
                        return Err(
                            EvalErr(
                                allocator.null(),
                                format!(
                                    "op_set_pair on atom item {:?} in vec {:?} ops {:?}",
                                    target,
                                    stack,
                                    ops
                                )
                            )
                        );
                    }
                }
            },

            SexpStackOp::OpPrepend(target) => {
                match top.borrow() {
                    CastableType::CLVMObject(f) => {
                        match stack[target].borrow() {
                            CastableType::CLVMObject(o) => {
                                match allocator.new_pair(*f, *o) {
                                    Ok(pair) => {
                                        stack[target] =
                                            Rc::new(CastableType::CLVMObject(pair));
                                    },
                                    Err(e) => { return Err(e); }
                                }
                            },
                            _ => {
                                return Err(
                                    EvalErr(
                                        allocator.null(),
                                        format!(
                                            "unrealized pair prepended {:?}",
                                            stack[target]
                                        )
                                    )
                                );
                            }
                        }
                    },
                    _ => {
                        return Err(
                            EvalErr(
                                allocator.null(),
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

    print!("post conversion: {:?}\n", &stack);

    if stack.len() != 1 {
        return Err(
            EvalErr(
                allocator.null(),
                format!("too many values left on op stack {:?}", stack)
            )
        );
    }

    return match stack.pop() {
        None => {
            Err(EvalErr(allocator.null(), "stack empty".to_string()))
        },
        Some(top) => {
            match top.borrow() {
                CastableType::CLVMObject(o) => Ok(o.clone()),
                _ => {
                    Err(EvalErr(allocator.null(), format!("unimplemented {:?}", stack[0])))
                }
            }
        }
    };
}

pub fn sexp_as_bin<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> Bytes {
    let mut f = Stream::new(None);
    sexp_to_stream(allocator, sexp, &mut f);
    return f.get_value();
}

pub fn bool_sexp<'a>(allocator: &'a mut Allocator, b: bool) -> NodePtr {
    if b {
        return allocator.one();
    } else {
        return allocator.null();
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

pub fn non_nil<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> bool {
    match allocator.sexp(sexp) {
        SExp::Pair(_,_) => { return true; },
        SExp::Atom(b) => { return allocator.buf(&b).len() > 0; }
    }
}

pub fn first<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Pair(f,_) => { return Ok(f); },
        _ => { return Err(EvalErr(sexp, "first of non-cons".to_string())); }
    }
}

pub fn rest<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Pair(_,r) => { return Ok(r); },
        _ => { return Err(EvalErr(sexp, "rest of non-cons".to_string())); }
    }
}
