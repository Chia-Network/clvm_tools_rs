use std::borrow::Borrow;
use std::rc::Rc;

use encoding8::ascii::is_printable;
use unicode_segmentation::UnicodeSegmentation;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Record, Stream};
use crate::classic::clvm::{KEYWORD_FROM_ATOM, KEYWORD_TO_ATOM};
use crate::classic::clvm_tools::ir::reader::IRReader;
use crate::classic::clvm_tools::ir::writer::write_ir;
use crate::classic::clvm_tools::ir::Type::IRRepr;

pub fn is_printable_string(s: &String) -> bool {
    for ch in s.graphemes(true) {
        if ch.chars().nth(0).unwrap() > 0xff as char
            || !is_printable(ch.chars().nth(0).unwrap() as u8)
        {
            return false;
        }
    }
    true
}

pub fn assemble_from_ir<'a>(
    allocator: &'a mut Allocator,
    ir_sexp: Rc<IRRepr>,
) -> Result<NodePtr, EvalErr> {
    match ir_sexp.borrow() {
        IRRepr::Null => Ok(allocator.null()),
        IRRepr::Quotes(b) => allocator.new_atom(b.data()),
        IRRepr::Int(b, _signed) => allocator.new_atom(b.data()),
        IRRepr::Hex(b) => allocator.new_atom(b.data()),
        IRRepr::Symbol(s) => {
            let mut s_real_name = s.clone();
            if s.starts_with("#") {
                s_real_name = s[1..].to_string();
            }

            match KEYWORD_TO_ATOM().get(&s_real_name) {
                Some(v) => allocator.new_atom(v),
                None => {
                    let v: Vec<u8> = s_real_name.as_bytes().to_vec();
                    allocator.new_atom(&v)
                }
            }
        }
        IRRepr::Cons(l, r) => assemble_from_ir(allocator, l.clone()).and_then(|l| {
            assemble_from_ir(allocator, r.clone()).and_then(|r| allocator.new_pair(l, r))
        }),
    }
}

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
            }
            _ => {}
        }
        // Determine whether the bytes identity an integer in canonical form.
    } else {
        if allow_keyword {
            match KEYWORD_FROM_ATOM().get(atom.data()) {
                Some(kw) => {
                    return IRRepr::Symbol(kw.to_string());
                }
                _ => {}
            }
        }

        if atom.length() == 1 || (atom.length() > 1 && atom.data()[0] != 0) {
            return IRRepr::Int(atom.clone(), true);
        }
    }
    IRRepr::Hex(atom.clone())
}

/*
 * (2 2 (2) (2 3 4)) => (a 2 (a) (a 3 4))
 */
pub fn disassemble_to_ir_with_kw<'a>(
    allocator: &'a mut Allocator,
    sexp: NodePtr,
    keyword_from_atom: &Record<Vec<u8>, String>,
    allow_keyword_: bool,
) -> IRRepr {
    let mut allow_keyword = allow_keyword_;
    match allocator.sexp(sexp) {
        SExp::Pair(l, r) => {
            match allocator.sexp(l) {
                SExp::Pair(_, _) => {
                    allow_keyword = true;
                }
                _ => {}
            };

            let v0 =
                disassemble_to_ir_with_kw(allocator, l.clone(), keyword_from_atom, allow_keyword);
            let v1 = disassemble_to_ir_with_kw(allocator, r.clone(), keyword_from_atom, false);
            IRRepr::Cons(Rc::new(v0), Rc::new(v1))
        }

        SExp::Atom(a) => {
            let bytes = Bytes::new(Some(BytesFromType::Raw(allocator.buf(&a).to_vec())));
            ir_for_atom(&bytes, allow_keyword)
        }
    }
}

pub fn disassemble_with_kw<'a>(
    allocator: &'a mut Allocator,
    sexp: NodePtr,
    keyword_from_atom: &Record<Vec<u8>, String>,
) -> String {
    let with_keywords = match allocator.sexp(sexp) {
        SExp::Atom(_) => false,
        _ => true,
    };

    let symbols = disassemble_to_ir_with_kw(allocator, sexp, &keyword_from_atom, with_keywords);
    write_ir(Rc::new(symbols))
}

pub fn disassemble<'a>(allocator: &'a mut Allocator, sexp: NodePtr) -> String {
    return disassemble_with_kw(allocator, sexp, KEYWORD_FROM_ATOM());
}

pub fn assemble<'a>(allocator: &'a mut Allocator, s: &String) -> Result<NodePtr, EvalErr> {
    let v = s.as_bytes().to_vec();
    let stream = Stream::new(Some(Bytes::new(Some(BytesFromType::Raw(v)))));
    let mut reader = IRReader::new(stream);
    reader
        .read_expr()
        .map_err(|e| EvalErr(allocator.null(), e))
        .and_then(|ir| assemble_from_ir(allocator, Rc::new(ir)))
}
