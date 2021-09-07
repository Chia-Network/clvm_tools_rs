use std::borrow::Borrow;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};
use crate::classic::clvm::CLVMObject::CLVMObject;
use crate::classic::clvm::SExp::SExp;

// import {SExp, int_from_bytes, sexp_to_stream, str, Stream, b} from "clvm";
// import {Type} from "./Type";
// import {
//   ir_nullp,
//   ir_type,
//   ir_listp,
//   ir_first,
//   ir_rest,
//   ir_as_atom,
//   ir_val,
// } from "./utils";

enum IROutputState {
    Start(Rc<SExp>),
    ListOf(Rc<SExp>),
    DotThen(Rc<SExp>),
    EndParen,
}

struct IROutputIterator {
    state : Vec<IROutputState>
}

impl IROutputIterator {
    fn new(ir_sexp: Rc<SExp>) -> IROutputIterator {
        return IROutputIterator {
            state: vec!(IROutputState::Start(ir_sexp))
        };
    }
}

impl Iterator for IROutputIterator {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state.pop() {
            None => None,
            Some(IROutputState::EndParen) => { return Some(")".to_string()); },
            Some(IROutputState::Start(v)) => {
                match v.borrow() {
                    CLVMObject::Atom(a) => {
                        if a.length() == 0 {
                            return Some("()".to_string());
                        }

                        // TODO: stringify bytes properly.
                        return Some(("0x".to_string() + &a.hex()).to_string());
                    },
                    CLVMObject::Pair(l,r) => {
                        self.state.push(IROutputState::ListOf(Rc::new(CLVMObject::Pair(l.clone(),r.clone()))));
                        return Some("(".to_string());
                    }
                }
            },
            Some(IROutputState::ListOf(v)) => {
                match v.borrow() {
                    CLVMObject::Atom(a) => {
                        if a.length() == 0 {
                            return Some(")".to_string());
                        }
                        self.state.push(IROutputState::DotThen(Rc::new(CLVMObject::Atom(a.clone()))));
                        return Some(".".to_string());
                    },
                    CLVMObject::Pair(l,r) => {
                        self.state.push(IROutputState::ListOf(l.clone()));
                        return self.next();
                    }
                }
            },
            Some(IROutputState::DotThen(v)) => {
                self.state.push(IROutputState::EndParen);
                match v.borrow() {
                    CLVMObject::Atom(a) => {
                        if a.length() == 0 {
                            return Some(")".to_string());
                        }
                        self.state.push(IROutputState::DotThen(Rc::new(CLVMObject::Atom(a.clone()))));
                        return Some(".".to_string());
                    },
                    CLVMObject::Pair(l,r) => {
                        self.state.push(IROutputState::ListOf(l.clone()));
                        return self.next();
                    }
                }
            }
        }
    }
}

pub fn write_ir_to_stream(ir_sexp: Rc<SExp>, f: &mut Stream) {
    for b in IROutputIterator::new(ir_sexp) {
        f.write(Bytes::new(Some(BytesFromType::String(b))));
    }
}

pub fn write_ir(ir_sexp: Rc<SExp>) -> String {
    let mut s = Stream::new(None);
    write_ir_to_stream(ir_sexp, &mut s);
    return s.getValue().decode();
}
