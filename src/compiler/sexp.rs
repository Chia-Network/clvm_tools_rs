use std::rc::Rc;
use std::string::String;

use num_bigint::ToBigInt;
use num_traits::zero;
use unicode_segmentation::UnicodeSegmentation;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType
};
use crate::classic::clvm::casts::{
    TConvertOption,
    bigint_from_bytes,
    bigint_to_bytes
};
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

// Compiler view of SExp
pub enum SExp {
    Nil(Srcloc),
    Cons(Srcloc,Rc<SExp>,Rc<SExp>),
    Integer(Srcloc,Number),
    QuotedString(Srcloc,u8,Vec<u8>),
    Atom(Srcloc, Vec<u8>)
}

fn make_cons(a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons(a.loc().ext(&b.loc()), a.clone(), b.clone())
}

enum SExpParseState {
    Empty,
    CommentText(Srcloc, String),
    Bareword(Srcloc, String),
    QuotedText(Srcloc, char, String),
    QuotedEscaped(Srcloc, char, String),
    OpenList(Srcloc),
    ParsingList(Srcloc, Rc<SExpParseState>, Vec<Rc<SExp>>),
    TermList(Srcloc, Rc<SExpParseState>, Vec<Rc<SExp>>)
}

enum SExpParseResult {
    PResume(SExpParseState),
    PEmit(Rc<SExp>, SExpParseState),
    PError(Srcloc, String)
}

enum Integral { Decimal, Hex, NotIntegral }

fn is_hex(s: &String) -> bool { s.starts_with("0x") }

fn is_dec(s: &String) -> bool {
    let mut first = true;
    let mut dec = true;
    for ch in s.graphemes(true) {
        if first && ch == "-" {
            // Nothing
        } else if !(ch >= "0" && ch <= "9") {
            dec = false;
            break;
        }
        first = false;
    }
    return dec && s != "-";
}

fn matches_integral(s: &String) -> Integral {
    if is_hex(s) {
        Integral::Hex
    } else if is_dec(s) {
        Integral::Decimal
    } else {
        Integral::NotIntegral
    }
}

fn escape_quote(q: u8, s: &Vec<u8>) -> String {
    let mut res: Vec<char> = Vec::new();
    let basic_escape =
        s.iter().map(|ch| {
            if *ch == q as u8 {
                res.push('\\');
                res.push(*ch as char);
            } else {
                res.push(*ch as char);
            }
        });

    res.into_iter().collect()
}

fn list_no_parens(a: &SExp, b: &SExp) -> String {
    match b {
        SExp::Nil(_) => a.to_string(),
        SExp::Cons(_,b,c) => a.to_string() + " " + &list_no_parens(b,c),
        _ => a.to_string() + " . " + &b.to_string()
    }
}

fn encode_hex_digit_list(v: &Vec<u8>, res: &mut Vec<u8>) {
    let enclen = v.len().to_bigint().unwrap();
    let lenor =
        if enclen < 0x40.to_bigint().unwrap() {
            0x80.to_bigint().unwrap()
        } else if enclen < 0x2000.to_bigint().unwrap() {
            0xc000.to_bigint().unwrap()
        } else if enclen < 0x1000000.to_bigint().unwrap() {
            0xe0000000_u64.to_bigint().unwrap()
        } else if enclen < 0x80000000_u64.to_bigint().unwrap() {
            0xf0000000_u64.to_bigint().unwrap()
        } else {
            0xf80000000000_u64.to_bigint().unwrap()
        };
    let combined_prefix = lenor | enclen;
    let encoded_prefix = bigint_to_bytes(&combined_prefix, None).unwrap();
    let mut encoded_data = encoded_prefix.data().to_vec();
    res.append(&mut encoded_data);
}

fn encode_integer_value(v: &Vec<u8>, res: &mut Vec<u8>) {
    if v.len() == 1 && v[0] < 0x80 {
        res.push(v[0]);
    } else {
        encode_hex_digit_list(v, res);
        let mut vcopy = v.to_vec();
        res.append(&mut vcopy);
    }
}

impl SExp {
    pub fn loc(&self) -> Srcloc {
        match self {
            SExp::Nil(l) => l.clone(),
            SExp::Cons(l,_,_) => l.clone(),
            SExp::Integer(l,_) => l.clone(),
            SExp::QuotedString(l,_,_) => l.clone(),
            SExp::Atom(l,_) => l.clone()
        }
    }

    pub fn atom_from_string(loc: Srcloc, s: &String) -> SExp {
        return SExp::Atom(loc, s.as_bytes().to_vec());
    }

    pub fn quoted_from_string(loc: Srcloc, s: &String) -> SExp {
        return SExp::QuotedString(loc, '\"' as u8, s.as_bytes().to_vec());
    }

    pub fn to_string(&self) -> String {
        match self {
            SExp::Nil(_) => "()".to_string(),
            SExp::Cons(_,a,b) => "(".to_owned() + &list_no_parens(a,b) + ")",
            SExp::Integer(_,v) => v.to_string(),
            SExp::QuotedString(_,q,s) =>
                "\"".to_owned() + &escape_quote(*q,s) + "\"",
            SExp::Atom(_,a) =>
                Bytes::new(Some(BytesFromType::Raw(a.to_vec()))).decode()
        }
    }

    pub fn nilp(&self) -> bool {
        let bizero: Number = zero();
        match self {
            SExp::Nil(_) => true,
            SExp::QuotedString(_,_,v) => v.len() == 0,
            SExp::Integer(_,i) => *i == bizero,
            SExp::Atom(_,a) => a.len() == 0,
            _ => false
        }
    }

    pub fn listp(&self) -> bool {
        match self {
            SExp::Nil(_) => true,
            SExp::Cons(_,_,_) => true,
            _ => false
        }
    }

    pub fn cons_fst(&self) -> Rc<SExp> {
        match self {
            SExp::Cons(_,a,_) => a.clone(),
            _ => Rc::new(SExp::Nil(self.loc()))
        }
    }

    pub fn cons_snd(&self) -> Rc<SExp> {
        match self {
            SExp::Cons(_,_,b) => b.clone(),
            _ => Rc::new(SExp::Nil(self.loc()))
        }
    }

    pub fn encode_mut(&self, v: &mut Vec<u8>) {
        match self {
            SExp::Nil(_) => v.push(0x80),
            SExp::Cons(_,a,b) => {
                v.push(0xff);
                a.encode_mut(v);
                b.encode_mut(v);
            },
            SExp::Integer(_,i) => {
                let mut bi_bytes =
                    bigint_to_bytes(
                        i,
                        Some(TConvertOption { signed: true })
                    ).unwrap().data().to_vec();

                v.append(&mut bi_bytes);
            },
            SExp::QuotedString(_,q,s) => encode_integer_value(s, v),
            SExp::Atom(_,a) => encode_integer_value(a, v)
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        self.encode_mut(&mut v);
        return v;
    }

    pub fn to_bigint(&self) -> Option<Number> {
        match self {
            SExp::Nil(_) => Some(zero()),
            SExp::Integer(_,v) => Some(v.clone()),
            SExp::QuotedString(_,_,v) =>
                Some(bigint_from_bytes(&Bytes::new(Some(BytesFromType::Raw(v.to_vec()))), Some(TConvertOption { signed: true }))),
            SExp::Atom(_,v) =>
                Some(bigint_from_bytes(&Bytes::new(Some(BytesFromType::Raw(v.to_vec()))), Some(TConvertOption { signed: true }))),
            _ => None
        }
    }

    pub fn equal_to(&self, other: &SExp) -> bool {
        if self.nilp() && other.nilp() {
            true
        } else if self.nilp() || other.nilp() {
            false
        } else {
            match (self,other) {
                (SExp::Cons(_,r,s), SExp::Cons(_,t,u)) => {
                    r.equal_to(t) && s.equal_to(u)
                },
                (SExp::Cons(_,_,_), _) => false,
                (_, SExp::Cons(_,_,_)) => false,
                (SExp::Integer(_,a), SExp::Integer(_,b)) => a == b,
                (a,b) => a.encode() == b.encode()
            }
        }
    }
}
