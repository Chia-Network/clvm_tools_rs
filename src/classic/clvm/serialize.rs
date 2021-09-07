/*
decoding:
read a byte
if it's 0xfe, it's nil (which might be same as 0)
if it's 0xff, it's a cons box. Read two items, build cons
otherwise, number of leading set bits is length in bytes to read size
0-0x7f are literal one byte values
leading bits is the count of bytes to read of size
0x80-0xbf is a size of one byte (perform logical and of first byte with 0x3f to get size)
0xc0-0xdf is a size of two bytes (perform logical and of first byte with 0x1f)
0xe0-0xef is 3 bytes ((perform logical and of first byte with 0xf))
0xf0-0xf7 is 4 bytes ((perform logical and of first byte with 0x7))
0xf7-0xfb is 5 bytes ((perform logical and of first byte with 0x3))
 */

use std::borrow::Borrow;
use std::rc::Rc;
use std::vec::Vec;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};
use crate::classic::clvm::as_rust::{TToSexpF, TValStack};
use crate::classic::clvm::casts::int_from_bytes;
use crate::classic::clvm::SExp::{
    CastableType,
    SExp,
    to_sexp_type
};
use crate::classic::clvm::EvalError::EvalError;
use crate::classic::clvm::CLVMObject::CLVMObject;

const MAX_SINGLE_BYTE : u32 = 0x7F;
const CONS_BOX_MARKER : u32 = 0xFF;

fn atom_size_blob(b: &Bytes) -> Result<Vec<u8>,EvalError> {
    let size = b.length();
    if size == 0 {
        return Ok(vec!(0x80));
    } else if size == 1 && b.at(0) <= MAX_SINGLE_BYTE as u8 {
        return Ok(b.data().clone());
    }

    if size < 0x40 {
        return Ok(vec!(0x80 | size as u8));
    } else if size < 0x2000 {
        return Ok(vec!(0xC0 | ((size >> 8) as u8), ((size >> 0) & 0xFF) as u8));
    } else if size < 0x100000 {
        return Ok(vec!(
            0xE0 | ((size >> 16) as u8),
            ((size >> 8) & 0xFF) as u8,
            ((size >> 0) & 0xFF) as u8
        ));
    } else if size < 0x8000000 {
        return Ok(vec!(
            0xF0 | ((size >> 24) as u8),
            ((size >> 16) & 0xFF) as u8,
            ((size >> 8) & 0xFF) as u8,
            ((size >> 0) & 0xFF) as u8
        ));
    } else if size < 0x400000000 {
        return Ok(vec!(
            0xF8 | ((size / (65536 * 65536)) as u8),// (size >> 32),
            ((size >> 24) & 0xFF) as u8,
            ((size >> 16) & 0xFF) as u8,
            ((size >> 8) & 0xFF) as u8,
            (size & 0xFF) as u8
        ));
    } else {
        return Err(EvalError::new_str(format!("oversize bytes is unrepresentable {:?}", size)));
    }
}

enum SExpToByteOp {
    Blob(Vec<u8>),
    Object(Rc<SExp>)
}

struct SExpToBytesIterator {
    pub state: Vec<SExpToByteOp>
}

impl SExpToBytesIterator {
    fn new(sexp: Rc<SExp>) -> Self {
        return SExpToBytesIterator {
            state: vec!(SExpToByteOp::Object(sexp.clone()))
        };
    }
}

impl Iterator for SExpToBytesIterator {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.state.pop() {
                None => { break; }
                Some(SExpToByteOp::Object(x)) => {
                    match x.borrow() {
                        CLVMObject::Atom(b) => {
                            self.state.push(SExpToByteOp::Blob(b.data().clone()));
                            match atom_size_blob(&b) {
                                Ok(b) => { return Some(b); },
                                Err(_) => { return None; }
                            }
                        },
                        CLVMObject::Pair(f,r) => {
                            self.state.push(SExpToByteOp::Object(r.clone()));
                            self.state.push(SExpToByteOp::Object(f.clone()));
                            return Some(vec!(CONS_BOX_MARKER as u8));
                        }
                    }
                },
                Some(SExpToByteOp::Blob(b)) => {
                    return Some(b);
                }
            }
        }
        return None;
    }
}

pub trait OpStackEntry {
    fn invoke(&self, op_stack: &mut TOpStack, val_stack: &mut TValStack, f: &mut Stream, to_sexp_f: Box<dyn TToSexpF>) -> Option<EvalError>;
}

type TOpStack = Vec<Option<Box<dyn OpStackEntry>>>;

pub fn sexp_to_stream(sexp: Rc<SExp>, f: &mut Stream) {
    for b in SExpToBytesIterator::new(sexp) {
        f.write(Bytes::new(Some(BytesFromType::Raw(b))));
    }
}

struct OpCons { }

impl OpStackEntry for OpCons {
    fn invoke(&self, op_stack: &mut TOpStack, val_stack: &mut TValStack, f: &mut Stream, to_sexp_f: Box<dyn TToSexpF>) -> Option<EvalError> {
        return val_stack.pop().and_then(|l| {
            return val_stack.pop().and_then(|r| {
                match to_sexp_f.invoke(
                    CastableType::TupleOf(Rc::new(l), Rc::new(r))
                ) {
                    Ok(c) => {
                        val_stack.push(CastableType::CLVMObject(c.clone()));
                        return None;
                    },
                    Err(e) => {
                        return Some(e);
                    }
                }
            });
        });
    }
}

struct OpReadSexp { }

impl OpStackEntry for OpReadSexp {
    fn invoke(&self, op_stack: &mut TOpStack, val_stack: &mut TValStack, f: &mut Stream, to_sexp_f: Box<dyn TToSexpF>) -> Option<EvalError> {
        let blob = f.read(1);
        if blob.length() == 0 {
            return Some(EvalError::new_str("bad encoding".to_string()));
        }
        let b = blob.at(0);
        if b == CONS_BOX_MARKER as u8 {
            op_stack.push(Some(Box::new(OpCons {})));
            op_stack.push(Some(Box::new(OpReadSexp {})));
            op_stack.push(Some(Box::new(OpReadSexp {})));
            return None;
        }

        match atom_from_stream(f, b, to_sexp_f) {
            Ok(v) => {
                val_stack.push(CastableType::CLVMObject(Rc::new(v)));
                return None;
            },
            Err(e) => { return Some(e); }
        }
    }
}

pub struct SimpleCreateCLVMObject { }

impl TToSexpF for SimpleCreateCLVMObject {
    fn invoke(&self, v: CastableType) -> Result<Rc<SExp>, EvalError> {
        return to_sexp_type(v);
    }
}

pub fn sexp_from_stream(f: &mut Stream, to_sexp_f: Box<dyn TToSexpF>) -> Result<Rc<SExp>, EvalError> {
    let mut op_stack: TOpStack = vec!(Some(Box::new(OpReadSexp {})));
    let mut val_stack: TValStack = vec!();

    while op_stack.len() > 0 {
        op_stack.pop().and_then(|x| x).map(|func| {
            func.invoke(&mut op_stack, &mut val_stack, f, Box::new(SimpleCreateCLVMObject {}));
        });
    }

    return val_stack.pop().map(|v| to_sexp_f.invoke(v)).
        unwrap_or_else(|| Err(EvalError::new_str(
            "No value left after conversion".
                to_string())
        ));
}

// function _op_consume_sexp(f: Stream){
//   const blob = f.read(1);
//   if(blob.length === 0){
//     throw new Error("bad encoding");
//   }
//   const b = blob.at(0);
//   if(b === CONS_BOX_MARKER){
//     return t(blob, 2);
//   }
//   return t(_consume_atom(f, b), 0);
// }

// function _consume_atom(f: Stream, b: number){
//   if(b === 0x80){
//     return Bytes.from([b]);
//   }
//   else if(b <= MAX_SINGLE_BYTE){
//     return Bytes.from([b]);
//   }
  
//   let bit_count = 0;
//   let bit_mask = 0x80;
//   let ll = b;
  
//   while(ll & bit_mask){
//     bit_count += 1;
//     ll &= 0xFF ^ bit_mask;
//     bit_mask >>= 1;
//   }
  
//   let size_blob = Bytes.from([ll]);
//   if(bit_count > 1){
//     const ll2 = f.read(bit_count-1);
//     if(ll2.length !== bit_count-1){
//       throw new Error("bad encoding");
//     }
//     size_blob = size_blob.concat(ll2);
//   }
  
//   const size = int_from_bytes(size_blob);
//   if(size >= 0x400000000){
//     throw new Error("blob too large");
//   }
//   const blob = f.read(size);
//   if(blob.length !== size){
//     throw new Error("bad encoding");
//   }
//   return Bytes.from([b]).concat(size_blob.subarray(1)).concat(blob);
// }

/*
instead of parsing the input stream, this function pulls out all the bytes
that represent on S-expression tree, and returns them. This is more efficient
than parsing and returning a python S-expression tree.
 */
// export function sexp_buffer_from_stream(f: Stream): Bytes {
//   const buffer = new Stream();
//   let depth = 1;
//   while(depth > 0){
//     depth -= 1;
//     const [buf, d] = _op_consume_sexp(f) as [Bytes, number];
//     depth += d;
//     buffer.write(buf);
//   }
//   return buffer.getValue();
// }

pub fn atom_from_stream(f: &mut Stream, b_: u8, to_sexp_f: Box<dyn TToSexpF>) -> Result<SExp, EvalError> {
    let mut b = b_;

    if b == 0x80 {
        return Ok(CLVMObject::new());
    }
    else if b <= MAX_SINGLE_BYTE as u8 {
        return Ok(CLVMObject::Atom(Bytes::new(Some(BytesFromType::Raw(vec!(b))))));
    }

    let mut bit_count = 0;
    let mut bit_mask = 0x80;

    while (b & bit_mask) != 0 {
        bit_count += 1;
        b &= 0xFF ^ bit_mask;
        bit_mask >>= 1;
    }

    let mut size_blob = Bytes::new(Some(BytesFromType::Raw(vec!(b))));
    if bit_count > 1 {
        let bin = f.read(bit_count - 1);
        if bin.length() != bit_count - 1 {
            return Err(EvalError::new_str("bad encoding".to_string()));
        }
        size_blob = size_blob.concat(&bin);
    }
    return int_from_bytes(Some(size_blob), None).and_then(|size| {
        if size >= 0x400000000 {
            return Err(EvalError::new_str("blob too large".to_string()));
        }
        let blob = f.read(size as usize);
        if blob.length() != size as usize {
            return Err(EvalError::new_str("bad encoding".to_string()));
        }
        return Ok(CLVMObject::Atom(blob));
    });
}
