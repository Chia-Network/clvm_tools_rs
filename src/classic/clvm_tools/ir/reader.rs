use std::mem::swap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};
use crate::classic::clvm::casts::{bigint_to_bytes, TConvertOption};
use crate::classic::clvm_tools::ir::Type::IRRepr;
use crate::util::Number;

pub struct IRReader {
    stream: Stream,
}

// XXX Allows us to track line and column later if desired.
impl IRReader {
    fn read(&mut self, n: usize) -> Bytes {
        self.stream.read(n)
    }

    fn backup(&mut self, n: usize) {
        let cur_seek = self.stream.get_seek();
        if n > cur_seek {
            self.stream.set_seek(0);
        } else {
            self.stream.set_seek((cur_seek - n) as i64);
        }
    }

    pub fn read_expr(&mut self) -> Result<IRRepr, String> {
        consume_object(self)
    }

    pub fn new(s: Stream) -> Self {
        IRReader { stream: s }
    }
}

pub fn is_eol(chval: u8) -> bool {
    chval == '\r' as u8 || chval == '\n' as u8
}

pub fn is_space(chval: u8) -> bool {
    chval == ' ' as u8 || chval == '\t' as u8 || is_eol(chval)
}

pub fn consume_whitespace(s: &mut IRReader) {
    let mut in_comment = false;

    // This also deals with comments
    // eslint-disable-next-line no-constant-condition
    loop {
        let b = s.read(1);
        if b.length() == 0 {
            return;
        }

        let ch = b.at(0);
        if in_comment {
            if is_eol(ch) {
                in_comment = false;
            } else {
                continue;
            }
        }

        if ch == b';' {
            in_comment = true;
            continue;
        }

        if is_space(ch) {
            continue;
        }

        break;
    }

    s.backup(1);
}

pub fn consume_quoted(s: &mut IRReader, q: char) -> Result<IRRepr, String> {
    let starting_at = s.stream.get_seek() - 1;
    let mut bs = false;
    let mut qchars = vec![];

    loop {
        let b = s.read(1);
        if b.length() == 0 {
            return Err(format!(
                "unterminated string starting at {}, {}",
                starting_at,
                Bytes::new(Some(BytesFromType::Raw(qchars))).decode()
            ));
        }

        if bs {
            bs = false;
            qchars.push(b.at(0));
        } else if b.at(0) == '\\' as u8 {
            bs = true;
        } else if b.at(0) == q as u8 {
            break;
        } else {
            qchars.push(b.at(0));
        }
    }

    Ok(IRRepr::Quotes(Bytes::new(Some(BytesFromType::Raw(qchars)))))
}

pub fn is_hex(chars: &Vec<u8>) -> bool {
    chars.len() > 2 && chars[0] == '0' as u8 && (chars[1] == 'x' as u8 || chars[1] == 'X' as u8)
}

pub fn is_dec(chars: &Vec<u8>) -> bool {
    let mut first = true;

    for ch in chars.iter() {
        if first {
            first = false;
            if *ch == '-' as u8 {
                continue;
            }
        }
        if *ch > '9' as u8 || *ch < '0' as u8 {
            return false;
        }
    }

    true
}

pub fn interpret_atom_value(chars: &Vec<u8>) -> IRRepr {
    if chars.len() == 0 {
        IRRepr::Null
    } else if is_hex(chars) {
        let mut string_bytes = if chars.len() % 2 > 0 {
            Bytes::new(Some(BytesFromType::Raw(vec!['0' as u8])))
        } else {
            Bytes::new(None)
        };
        string_bytes =
            string_bytes.concat(&Bytes::new(Some(BytesFromType::Raw(chars[2..].to_vec()))));

        IRRepr::Hex(Bytes::new(Some(BytesFromType::Hex(string_bytes.decode()))))
    } else {
        match String::from_utf8(chars.to_vec())
            .ok()
            .and_then(|s| s.parse::<Number>().ok())
            .and_then(|n| bigint_to_bytes(&n, Some(TConvertOption { signed: true })).ok())
        {
            Some(n) => IRRepr::Int(n, true),
            None => {
                let string_bytes = Bytes::new(Some(BytesFromType::Raw(chars.to_vec())));
                IRRepr::Symbol(string_bytes.decode())
            }
        }
    }
}

pub fn consume_atom(s: &mut IRReader, b: &Bytes) -> Option<IRRepr> {
    let mut result_vec = b.data().to_vec();
    loop {
        let b = s.read(1);
        if b.length() == 0 {
            if result_vec.len() == 0 {
                return None;
            } else {
                return Some(interpret_atom_value(&result_vec));
            }
        }

        if b.at(0) == '(' as u8 || b.at(0) == ')' as u8 || is_space(b.at(0)) {
            s.backup(1);
            return Some(interpret_atom_value(&result_vec));
        }

        result_vec.push(b.at(0));
    }
}

fn enlist_ir(vec: &mut Vec<IRRepr>, tail: IRRepr) -> IRRepr {
    let mut result = tail;
    for i_reverse in 0..vec.len() {
        let i = vec.len() - i_reverse - 1;
        let mut next_head = IRRepr::Null;
        swap(&mut vec[i], &mut next_head);
        result = IRRepr::Cons(Rc::new(next_head), Rc::new(result));
    }
    result
}

pub fn consume_cons_body(s: &mut IRReader) -> Result<IRRepr, String> {
    let mut result = vec![];

    loop {
        consume_whitespace(s);

        let b = s.read(1);
        if b.length() == 0 {
            return Err("missing )".to_string());
        }

        if b.at(0) == ')' as u8 {
            return Ok(enlist_ir(&mut result, IRRepr::Null));
        }

        if b.at(0) == '(' as u8 {
            match consume_cons_body(s) {
                Err(e) => {
                    return Err(e);
                }
                Ok(v) => {
                    result.push(v);
                    continue;
                }
            }
        }

        if b.at(0) == '.' as u8 {
            consume_whitespace(s);
            let tail_obj = consume_object(s);
            match tail_obj {
                Err(e) => {
                    return Err(e);
                }
                Ok(v) => {
                    consume_whitespace(s);
                    let b = s.read(1);
                    if b.length() == 0 || b.at(0) != ')' as u8 {
                        return Err("missing )".to_string());
                    }
                    return Ok(enlist_ir(&mut result, v));
                }
            }
        }

        if b.at(0) == '\"' as u8 || b.at(0) == '\'' as u8 {
            match consume_quoted(s, b.at(0) as char) {
                Err(e) => {
                    return Err(e);
                }
                Ok(v) => {
                    result.push(v);
                    continue;
                }
            }
        } else {
            match consume_atom(s, &b) {
                Some(f) => {
                    result.push(f);
                    continue;
                }
                _ => {
                    return Err("missing )".to_string());
                }
            }
        }
    }
}

pub fn consume_object(s: &mut IRReader) -> Result<IRRepr, String> {
    consume_whitespace(s);
    let b = s.read(1);

    if b.length() == 0 {
        Ok(IRRepr::Null)
    } else if b.at(0) == '(' as u8 {
        consume_cons_body(s)
    } else if b.at(0) == '\"' as u8 || b.at(0) == '\'' as u8 {
        match consume_quoted(s, b.at(0) as char) {
            Err(e) => Err(e),
            Ok(v) => Ok(v),
        }
    } else {
        match consume_atom(s, &b) {
            None => Err("empty stream".to_string()),
            Some(ir) => Ok(ir),
        }
    }
}

pub fn read_ir(s: &String) -> Result<IRRepr, String> {
    let bytes_of_string = Bytes::new(Some(BytesFromType::Raw(s.as_bytes().to_vec())));
    let stream = Stream::new(Some(bytes_of_string));
    let mut reader = IRReader::new(stream);
    reader.read_expr()
}
