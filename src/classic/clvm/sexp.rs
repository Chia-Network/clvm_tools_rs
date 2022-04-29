use std::borrow::Borrow;
use std::fmt::Debug;
use std::rc::Rc;
use std::string::String;

use clvm_rs::allocator::{Allocator, AtomBuf, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use bls12_381::G1Affine;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};
use crate::classic::clvm::serialize::sexp_to_stream;
use crate::util::{u8_from_number, Number};

#[derive(Debug)]
pub enum CastableType {
    CLVMObject(NodePtr),
    Bytes(Bytes),
    String(String),
    Number(Number),
    G1Affine(G1Affine),
    ListOf(usize, Vec<Rc<CastableType>>),
    TupleOf(Rc<CastableType>, Rc<CastableType>),
}

#[derive(Debug)]
pub enum SexpStackOp {
    OpConvert,
    OpSetPair(bool, usize),
    OpPrepend(usize),
}

pub fn to_sexp_type(allocator: &mut Allocator, value: CastableType) -> Result<NodePtr, EvalErr> {
    let mut stack = vec![Rc::new(value)];
    let mut ops: Vec<SexpStackOp> = vec![SexpStackOp::OpConvert];

    loop {
        let op;

        match ops.pop() {
            None => {
                break;
            }
            Some(o) => {
                op = o;
            }
        }

        let top;

        match stack.pop() {
            None => {
                return Err(EvalErr(allocator.null(), "empty value stack".to_string()));
            }
            Some(rc) => {
                top = rc;
            }
        }

        // convert value
        match op {
            SexpStackOp::OpConvert => {
                match top.borrow() {
                    CastableType::CLVMObject(_) => {
                        stack.push(top.clone());
                    }
                    CastableType::TupleOf(left, right) => {
                        let target_index = stack.len();
                        match allocator.new_pair(allocator.null(), allocator.null()) {
                            Ok(pair) => {
                                stack.push(Rc::new(CastableType::CLVMObject(pair)));
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        };
                        stack.push(right.clone());
                        ops.push(SexpStackOp::OpSetPair(true, target_index)); // set right
                        ops.push(SexpStackOp::OpConvert); // convert

                        stack.push(left.clone());
                        ops.push(SexpStackOp::OpSetPair(false, target_index));
                        ops.push(SexpStackOp::OpConvert);
                    }
                    CastableType::ListOf(_sel, v) => {
                        let target_index = stack.len();
                        stack.push(Rc::new(CastableType::CLVMObject(allocator.null())));
                        for i in 0..v.len() - 1 {
                            stack.push(v[i].clone());
                            ops.push(SexpStackOp::OpPrepend(target_index));
                            // we only need to convert if it's not already the right type
                            ops.push(SexpStackOp::OpConvert);
                        }
                    }
                    CastableType::Bytes(b) => match allocator.new_atom(b.data()) {
                        Ok(a) => {
                            stack.push(Rc::new(CastableType::CLVMObject(a)));
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    },
                    CastableType::String(s) => {
                        let result_vec: Vec<u8> = s.as_bytes().into_iter().map(|x| *x).collect();
                        match allocator.new_atom(&result_vec) {
                            Ok(a) => {
                                stack.push(Rc::new(CastableType::CLVMObject(a)));
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        };
                    }
                    CastableType::Number(n) => {
                        match allocator.new_atom(&u8_from_number(n.clone())) {
                            Ok(a) => {
                                stack.push(Rc::new(CastableType::CLVMObject(a)));
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                    CastableType::G1Affine(g) => {
                        let bytes_ver = Bytes::new(Some(BytesFromType::G1Element(*g)));

                        match allocator.new_atom(bytes_ver.data()) {
                            Ok(a) => {
                                stack.push(Rc::new(CastableType::CLVMObject(a)));
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                }
            }
            SexpStackOp::OpSetPair(toset, target) => match top.borrow() {
                CastableType::CLVMObject(new_value) => match stack[target].borrow() {
                    CastableType::CLVMObject(target_value) => match allocator.sexp(*target_value) {
                        SExp::Pair(l, r) => {
                            if toset {
                                match allocator.new_pair(l, *new_value) {
                                    Ok(pair) => {
                                        stack[target] = Rc::new(CastableType::CLVMObject(pair));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            } else {
                                match allocator.new_pair(*new_value, r) {
                                    Ok(pair) => {
                                        stack[target] = Rc::new(CastableType::CLVMObject(pair));
                                    }
                                    Err(e) => {
                                        return Err(e);
                                    }
                                }
                            }
                        }
                        SExp::Atom(_) => {
                            return Err(EvalErr(
                                *target_value,
                                "attempt to set_pair in atom".to_string(),
                            ));
                        }
                    },
                    _ => {
                        return Err(EvalErr(
                            allocator.null(),
                            format!("Setting wing of non pair {:?}", stack[target]),
                        ));
                    }
                },
                _ => {
                    return Err(EvalErr(
                        allocator.null(),
                        format!(
                            "op_set_pair on atom item {:?} in vec {:?} ops {:?}",
                            target, stack, ops
                        ),
                    ));
                }
            },

            SexpStackOp::OpPrepend(target) => match top.borrow() {
                CastableType::CLVMObject(f) => match stack[target].borrow() {
                    CastableType::CLVMObject(o) => match allocator.new_pair(*f, *o) {
                        Ok(pair) => {
                            stack[target] = Rc::new(CastableType::CLVMObject(pair));
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    },
                    _ => {
                        return Err(EvalErr(
                            allocator.null(),
                            format!("unrealized pair prepended {:?}", stack[target]),
                        ));
                    }
                },
                _ => {
                    return Err(EvalErr(
                        allocator.null(),
                        format!("unrealized prepend {:?}", top),
                    ));
                }
            },
        }
    }

    if stack.len() != 1 {
        return Err(EvalErr(
            allocator.null(),
            format!("too many values left on op stack {:?}", stack),
        ));
    }

    return match stack.pop() {
        None => Err(EvalErr(allocator.null(), "stack empty".to_string())),
        Some(top) => match top.borrow() {
            CastableType::CLVMObject(o) => Ok(*o),
            _ => Err(EvalErr(
                allocator.null(),
                format!("unimplemented {:?}", stack[0]),
            )),
        },
    };
}

pub fn sexp_as_bin(allocator: &mut Allocator, sexp: NodePtr) -> Bytes {
    let mut f = Stream::new(None);
    sexp_to_stream(allocator, sexp, &mut f);
    f.get_value()
}

pub fn bool_sexp(allocator: &mut Allocator, b: bool) -> NodePtr {
    if b {
        allocator.one()
    } else {
        allocator.null()
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

pub fn non_nil(allocator: &mut Allocator, sexp: NodePtr) -> bool {
    match allocator.sexp(sexp) {
        SExp::Pair(_, _) => true,
        SExp::Atom(b) => allocator.buf(&b).len() > 0,
    }
}

pub fn first(allocator: &mut Allocator, sexp: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Pair(f, _) => Ok(f),
        _ => Err(EvalErr(sexp, "first of non-cons".to_string())),
    }
}

pub fn rest(allocator: &mut Allocator, sexp: NodePtr) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Pair(_, r) => Ok(r),
        _ => Err(EvalErr(sexp, "rest of non-cons".to_string())),
    }
}

pub fn atom(allocator: &mut Allocator, sexp: NodePtr) -> Result<AtomBuf, EvalErr> {
    match allocator.sexp(sexp) {
        SExp::Atom(abuf) => Ok(abuf),
        _ => Err(EvalErr(sexp, "not an atom".to_string())),
    }
}

pub fn proper_list(allocator: &mut Allocator, sexp: NodePtr, store: bool) -> Option<Vec<NodePtr>> {
    let mut args = vec![];
    let mut args_sexp = sexp;
    loop {
        match allocator.sexp(args_sexp) {
            SExp::Atom(_) => {
                if !non_nil(allocator, args_sexp) {
                    return Some(args);
                } else {
                    return None;
                }
            }
            SExp::Pair(f, r) => {
                if store {
                    args.push(f);
                }
                args_sexp = r;
            }
        }
    }
}

pub fn enlist<'a>(allocator: &'a mut Allocator, vec: &Vec<NodePtr>) -> Result<NodePtr, EvalErr> {
    let mut built = allocator.null();

    for i_reverse in 0..vec.len() {
        let i = vec.len() - i_reverse - 1;
        match allocator.new_pair(vec[i], built) {
            Err(e) => return Err(e),
            Ok(v) => {
                built = v;
            }
        }
    }
    Ok(built)
}

pub fn mapM<T>(
    allocator: &mut Allocator,
    iter: &mut impl Iterator<Item = T>,
    f: &dyn Fn(&mut Allocator, T) -> Result<NodePtr, EvalErr>,
) -> Result<Vec<NodePtr>, EvalErr> {
    let mut result = Vec::new();
    loop {
        match iter.next() {
            None => {
                return Ok(result);
            }
            Some(v) => match f(allocator, v) {
                Err(e) => {
                    return Err(e);
                }
                Ok(v) => {
                    result.push(v);
                }
            },
        }
    }
}

pub fn foldM<A, B, E>(
    allocator: &mut Allocator,
    f: &dyn Fn(&mut Allocator, A, B) -> Result<A, E>,
    start_: A,
    iter: &mut impl Iterator<Item = B>,
) -> Result<A, E> {
    let mut start = start_;
    loop {
        match iter.next() {
            None => {
                return Ok(start);
            }
            Some(v) => match f(allocator, start, v) {
                Err(e) => {
                    return Err(e);
                }
                Ok(v) => {
                    start = v;
                }
            },
        }
    }
}

pub fn equal_to<'a>(allocator: &'a mut Allocator, first_: NodePtr, second_: NodePtr) -> bool {
    let mut first = first_;
    let mut second = second_;

    loop {
        match (allocator.sexp(first), allocator.sexp(second)) {
            (SExp::Atom(fbuf), SExp::Atom(sbuf)) => {
                let fvec = allocator.buf(&fbuf).to_vec();
                let svec = allocator.buf(&sbuf).to_vec();
                return fvec == svec;
            }
            (SExp::Pair(ff, fr), SExp::Pair(rf, rr)) => {
                if !equal_to(allocator, ff, rf) {
                    return false;
                }
                first = fr;
                second = rr;
            }
            _ => {
                return false;
            }
        }
    }
}

pub fn flatten<'a>(allocator: &'a mut Allocator, tree_: NodePtr, res: &mut Vec<NodePtr>) {
    let mut tree = tree_;

    loop {
        match allocator.sexp(tree) {
            SExp::Atom(_) => {
                if !non_nil(allocator, tree) {
                    return;
                } else {
                    res.push(tree);
                    return;
                }
            }
            SExp::Pair(l, r) => {
                flatten(allocator, l, res);
                tree = r;
            }
        }
    }
}
