use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};
use crate::classic::clvm::casts::{
    TConvertOption,
    bigint_to_bytes
};
use crate::classic::clvm_tools::ir::Type::IRRepr;
use crate::util::Number;

pub struct IRReader {
    stream: Stream
}

// XXX Allows us to track line and column later if desired.
impl IRReader {
    fn read(&mut self, n: usize) -> Bytes {
        return self.stream.read(n);
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
        return consume_object(self);
    }

    pub fn new(s: Stream) -> Self {
        return IRReader { stream: s };
    }
}

pub fn is_eol(chval: u8) -> bool {
    return chval == '\r' as u8 || chval == '\n' as u8;
}

pub fn is_space(chval: u8) -> bool {
    return chval == ' ' as u8 || chval == '\t' as u8 || is_eol(chval);
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

        if ch == ';' as u8 {
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
    let mut qchars = vec!();

    loop {
        let b = s.read(1);
        if b.length() == 0 {
            return Err(format!("unterminated string starting at {}, {}", starting_at, Bytes::new(Some(BytesFromType::Raw(qchars))).decode()));
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

    return Ok(IRRepr::Quotes(Bytes::new(Some(BytesFromType::Raw(qchars)))));
}

pub fn is_hex(chars: &Vec<u8>) -> bool {
    return chars.len() > 2 && chars[0] == '0' as u8 &&
        (chars[1] == 'x' as u8 || chars[1] == 'X' as u8);
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

    return true;
}

pub fn interpret_atom_value(chars: &Vec<u8>) -> IRRepr {
    if chars.len() == 0 {
        return IRRepr::Null;
    } else if is_hex(chars) {
        let mut string_bytes =
            if chars.len() % 2 > 0 {
                Bytes::new(Some(BytesFromType::Raw(vec!('0' as u8))))
            } else {
                Bytes::new(None)
            };
        string_bytes =
            string_bytes.concat(&Bytes::new(Some(BytesFromType::Raw(chars[2..].to_vec()))));

        return IRRepr::Hex(
            Bytes::new(Some(BytesFromType::Hex(string_bytes.decode())))
        );
    } else {
        match String::from_utf8(chars.to_vec()).ok().
            and_then(|s| s.parse::<Number>().ok()).
            and_then(|n| bigint_to_bytes(&n, Some(TConvertOption { signed: true })).ok())
        {
            Some(n) => { return IRRepr::Int(n,true); },
            None => {
                let string_bytes = Bytes::new(Some(BytesFromType::Raw(chars.to_vec())));
                return IRRepr::Symbol(string_bytes.decode());
            }
        }
    }
}

pub fn consume_atom(s: &mut IRReader, b: &Bytes) -> Option<IRRepr> {
    let mut result_vec = b.data().to_vec();
    loop {
        let b = s.read(1);
        if b.length() == 0 {
            return None;
        }

        if b.at(0) == '(' as u8 || b.at(0) == ')' as u8 || b.at(0) == '.' as u8 || is_space(b.at(0)) {
            s.backup(1);
            return Some(interpret_atom_value(&result_vec));
        }

        result_vec.push(b.at(0));
    }
}

pub fn consume_cons_body(s: &mut IRReader) -> Result<IRRepr, String> {
    consume_whitespace(s);

    let b = s.read(1);
    if b.length() == 0 {
        return Err("missing )".to_string());
    }

    if b.at(0) == ')' as u8 {
        return Ok(IRRepr::Null);
    }

    if b.at(0) == '(' as u8 {
        return consume_cons_body(s).and_then(|f| {
            return consume_cons_body(s).map(|r| {
                return IRRepr::Cons(Rc::new(f), Rc::new(r));
            });
        });
    }

    if b.at(0) == '.' as u8 {
        let result = consume_object(s);
        consume_whitespace(s);
        let b = s.read(1);
        if b.length() == 0 || b.at(0) != ')' as u8 {
            return Err("missing )".to_string());
        }
        return result;
    }

    if b.at(0) == '\"' as u8 || b.at(0) == '\'' as u8 {
        match consume_quoted(s, b.at(0) as char) {
            Err(e) => { return Err(e); },
            Ok(v) => { return Ok(v); }
        }
    } else {
        match consume_atom(s, &b) {
            Some(r) => { return Ok(r); },
            _ => { return Err("missing )".to_string()); }
        }
    }

}

pub fn consume_object(s: &mut IRReader) -> Result<IRRepr, String> {
    consume_whitespace(s);
    let b = s.read(1);

    if b.length() == 0 {
        return Ok(IRRepr::Null);
    } else if b.at(0) == '(' as u8 {
        return consume_cons_body(s);
    } else {
        if b.at(0) == '\"' as u8 || b.at(0) == '\'' as u8 {
            match consume_quoted(s, b.at(0) as char) {
                Err(e) => { return Err(e); },
                Ok(v) => { return Ok(v); }
            }
        } else {
            match consume_atom(s, &b) {
                None => { return Err("empty stream".to_string()); },
                Some(ir) => { return Ok(ir); }
            }
        }
    }
}

pub fn read_ir(s: &String) -> Result<IRRepr, String> {
    let bytes_of_string = Bytes::new(Some(BytesFromType::Raw(s.as_bytes().to_vec())));
    let stream = Stream::new(Some(bytes_of_string));
    let mut reader = IRReader::new(stream);
    return reader.read_expr();
}
