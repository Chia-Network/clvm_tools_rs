use std::borrow::Borrow;
use std::rc::Rc;
use std::string::String;

use num_bigint::ToBigInt;
use num_traits::{
    Num,
    zero
};
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
#[derive(Clone)]
#[derive(Debug)]
pub enum SExp {
    Nil(Srcloc),
    Cons(Srcloc,Rc<SExp>,Rc<SExp>),
    Integer(Srcloc,Number),
    QuotedString(Srcloc,u8,Vec<u8>),
    Atom(Srcloc, Vec<u8>)
}

impl PartialEq for SExp {
    fn eq(&self, other: &Self) -> bool {
        return self.equal_to(other);
    }

    fn ne(&self, other: &Self) -> bool {
        return !self.eq(other);
    }
}

fn make_cons(a: Rc<SExp>, b: Rc<SExp>) -> SExp {
    SExp::Cons(a.loc().ext(&b.loc()), a.clone(), b.clone())
}

#[derive(Debug)]
enum SExpParseState {
    Empty,
    CommentText(Srcloc, Vec<u8>),
    Bareword(Srcloc, Vec<u8>),
    QuotedText(Srcloc, u8, Vec<u8>),
    QuotedEscaped(Srcloc, u8, Vec<u8>),
    OpenList(Srcloc),
    ParsingList(Srcloc, Rc<SExpParseState>, Vec<Rc<SExp>>),
    TermList(Srcloc, Rc<SExpParseState>, Vec<Rc<SExp>>)
}

#[derive(Debug)]
enum SExpParseResult {
    PResume(SExpParseState),
    PEmit(Rc<SExp>, SExpParseState),
    PError(Srcloc, String)
}

#[derive(Debug)]
enum Integral { Decimal, Hex, NotIntegral }

fn is_hex(s: &Vec<u8>) -> bool {
    s.len() >= 2 && s[0] == '0' as u8 && s[1] == 'x' as u8
}

fn is_dec(s: &Vec<u8>) -> bool {
    let mut first = true;
    let mut dec = true;

    for ch in s {
        if first && *ch == '-' as u8 {
            // Nothing
        } else if !(*ch >= '0' as u8 && *ch <= '9' as u8) {
            dec = false;
            break;
        }
        first = false;
    }

    return dec && *s != vec!('-' as u8);
}

fn matches_integral(s: &Vec<u8>) -> Integral {
    if is_hex(s) {
        Integral::Hex
    } else if is_dec(s) {
        Integral::Decimal
    } else {
        Integral::NotIntegral
    }
}

fn normalize_int(v: Vec<u8>, base: u32) -> Number {
    let s = Bytes::new(Some(BytesFromType::Raw(v))).decode();
    return Number::from_str_radix(&s, base).unwrap();
}

fn make_atom(l: Srcloc, v: Vec<u8>) -> SExp {
    let alen = v.len();
    if alen > 1 && v[0] == '#' as u8 {
        SExp::Atom(l,v[1..].to_vec())
    } else {
        match matches_integral(&v) {
            Integral::Hex => { SExp::Integer(l, normalize_int(v[2..].to_vec(), 16)) },
            Integral::Decimal => { SExp::Integer(l, normalize_int(v, 10)) },
            Integral::NotIntegral => { SExp::Atom(l,v) }
        }
    }
}

fn enlist(l: Srcloc, v: Vec<Rc<SExp>>) -> SExp {
    let mut result = SExp::Nil(l);
    for i_reverse in 0..v.len() {
        let i = v.len() - i_reverse - 1;
        result = make_cons(v[i].clone(), Rc::new(result));
    }
    return result;
}

fn emit(a: Rc<SExp>, p: SExpParseState) -> SExpParseResult {
    SExpParseResult::PEmit(a, p)
}

fn error(l: Srcloc, t: &String) -> SExpParseResult {
    SExpParseResult::PError(l, t.to_string())
}

fn resume(p: SExpParseState) -> SExpParseResult {
    SExpParseResult::PResume(p)
}

fn escape_quote(q: u8, s: &Vec<u8>) -> String {
    let mut res: Vec<char> = Vec::new();
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
            SExp::QuotedString(_,_,s) => encode_integer_value(s, v),
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

fn parse_sexp_step(loc: Srcloc, p: &SExpParseState, this_char: u8) -> SExpParseResult {
    match p {
        SExpParseState::Empty => {
            match this_char as char {
                '(' => resume(SExpParseState::OpenList(loc.clone())),
                '\n' => resume(SExpParseState::Empty),
                ';' => resume(SExpParseState::CommentText(loc.clone(), Vec::new())),
                ')' => error(loc, &"Too many close parens".to_string()),
                '"' => resume(SExpParseState::QuotedText(loc.clone(), '"' as u8, Vec::new())),
                '\'' => resume(SExpParseState::QuotedText(loc.clone(), '\'' as u8, Vec::new())),
                ch => {
                    if char::is_whitespace(ch) {
                        resume(SExpParseState::Empty)
                    } else {
                        resume(SExpParseState::Bareword(loc, vec!(this_char)))
                    }
                }
            }
        },
        SExpParseState::CommentText(pl, t) => {
            match this_char as char {
                '\r' => resume(SExpParseState::CommentText(pl.clone(),t.to_vec())),
                '\n' => resume(SExpParseState::Empty),
                _ => {
                    let mut tcopy = t.to_vec();
                    tcopy.push(this_char);
                    resume(SExpParseState::CommentText(pl.ext(&loc), tcopy))
                }
            }
        },
        SExpParseState::Bareword(pl, a) => {
            if char::is_whitespace(this_char as char) {
                emit(Rc::new(make_atom(pl.clone(),a.to_vec())),SExpParseState::Empty)
            } else {
                let mut acopy = a.to_vec();
                acopy.push(this_char);
                resume(SExpParseState::Bareword(pl.ext(&loc), acopy))
            }
        },
        SExpParseState::QuotedText(pl, term, t) => {
            if this_char == '\\' as u8 {
                resume(SExpParseState::QuotedEscaped(pl.clone(), *term, t.to_vec()))
            } else {
                if this_char == *term {
                    emit(Rc::new(SExp::QuotedString(pl.ext(&loc), *term, t.to_vec())), SExpParseState::Empty)
                } else {
                    let mut tcopy = t.to_vec();
                    tcopy.push(this_char);
                    resume(SExpParseState::QuotedText(pl.clone(), *term, tcopy))
                }
            }
        },
        SExpParseState::QuotedEscaped(pl, term, t) => {
            let mut tcopy = t.to_vec();
            tcopy.push(this_char);
            resume(SExpParseState::QuotedText(pl.clone(), *term, tcopy))
        },
        SExpParseState::OpenList(pl) => {
            match this_char as char {
                ')' => emit(Rc::new(SExp::Nil(pl.ext(&loc))),SExpParseState::Empty),
                '.' => error(loc, &"Dot can't appear directly after begin paren".to_string()),
                _ => {
                    match parse_sexp_step(loc.clone(), &SExpParseState::Empty, this_char) {
                        SExpParseResult::PEmit(o,p) => {
                            resume(SExpParseState::ParsingList(pl.ext(&loc), Rc::new(p), vec!(o)))
                        },
                        SExpParseResult::PResume(p) => {
                            resume(SExpParseState::ParsingList(pl.ext(&loc), Rc::new(p), Vec::new()))
                        },
                        SExpParseResult::PError(l,e) => SExpParseResult::PError(l,e)
                    }
                }
            }
        },
        SExpParseState::ParsingList(pl, pp, list_content) => {
            match (this_char as char, pp.borrow()) {
                ('.', SExpParseState::Empty) => resume(SExpParseState::TermList(pl.ext(&loc), Rc::new(SExpParseState::Empty), list_content.to_vec())),
                (')', SExpParseState::Empty) => emit(Rc::new(enlist(pl.clone(), list_content.to_vec())), SExpParseState::Empty),
                (')', SExpParseState::Bareword(l,t)) => {
                    let parsed_atom = make_atom(l.clone(),t.to_vec());
                    let mut updated_list = list_content.to_vec();
                    updated_list.push(Rc::new(parsed_atom));
                    emit(Rc::new(enlist(pl.clone(), updated_list)), SExpParseState::Empty)
                },
                (_, _) => {
                    match parse_sexp_step(loc.clone(), pp.borrow(), this_char) {
                        SExpParseResult::PEmit(o,p) => {
                            let result = SExpParseState::ParsingList(pl.ext(&loc), Rc::new(p), vec!(o));
                            resume(result)
                        },
                        SExpParseResult::PResume(rp) =>
                            resume(SExpParseState::ParsingList(pl.ext(&loc), Rc::new(rp), list_content.to_vec())),
                        SExpParseResult::PError(l,e) => SExpParseResult::PError(l,e)
                    }
                }
            }
        },
        SExpParseState::TermList(pl, pp, list_content) => {
            match (this_char as char, pp.borrow()) {
                ('.', SExpParseState::Empty) => {
                    error(loc, &"Multiple dots in list notation are illegal".to_string())
                },
                (')', SExpParseState::Empty) =>
                    emit(Rc::new(enlist(pl.clone(), list_content.to_vec())), SExpParseState::Empty),
                (')', SExpParseState::Bareword (l,t)) => {
                    let parsed_atom = make_atom(l.clone(), t.to_vec());
                    let mut list_copy = list_content.to_vec();
                    match list_copy.pop() {
                        Some(v) => {
                            let new_tail = make_cons(v, Rc::new(parsed_atom));
                            if list_copy.len() == 0 {
                                emit(Rc::new(new_tail), SExpParseState::Empty)
                            } else {
                                list_copy.push(Rc::new(new_tail));
                                let new_list = enlist(pl.ext(&l), list_copy);
                                emit(Rc::new(new_list), SExpParseState::Empty)
                            }
                        },
                        None => {
                            error(loc, &"Dot as first element of list?".to_string())
                        }
                    }
                },
                (_, _) => {
                    match parse_sexp_step(loc.clone(), pp.borrow(), this_char) {
                        SExpParseResult::PEmit (o,p) => {
                            let mut list_copy = list_content.to_vec();
                            match list_copy.pop() {
                                Some(v) => {
                                    let new_tail = make_cons(v, o);
                                    list_copy.push(Rc::new(new_tail));
                                    resume(SExpParseState::ParsingList(pl.ext(&loc), Rc::new(p), list_copy))
                                },
                                None => {
                                    error(loc, &"Dot as first element of list?".to_string())
                                }
                            }
                        },
                        SExpParseResult::PResume(p) => resume(SExpParseState::TermList(pl.ext(&loc), Rc::new(p), list_content.to_vec())),
                        SExpParseResult::PError(l,e) => SExpParseResult::PError(l,e)
                    }
                }
            }
        }
    }
}

fn parse_sexp_inner(start_: Srcloc, p_: SExpParseState, n_: usize, s: &Vec<u8>) -> Result<Vec<Rc<SExp>>, (Srcloc, String)> {
    let mut start = start_;
    let mut p = p_;
    let mut n = n_;
    let mut res = Vec::new();

    loop {
        if n >= s.len() {
            match p {
                SExpParseState::Empty => { return Ok(res); },
                SExpParseState::Bareword(l,t) => {
                    return Ok(vec!(Rc::new(make_atom(l,t))));
                },
                SExpParseState::CommentText(_,_) => { return Ok(res); },
                SExpParseState::QuotedText(l, _, _) => {
                    return Err((l, "unterminated quoted string".to_string()));
                },
                SExpParseState::QuotedEscaped(l, _, _) => {
                    return Err((l, "unterminated quoted string with escape".to_string()));
                },
                SExpParseState::OpenList(l) => {
                    return Err((l, "Unterminated list (empty)".to_string()));
                },
                SExpParseState::ParsingList(l, _, _) => {
                    return Err((l, "Unterminated mid list".to_string()));
                },
                SExpParseState::TermList(l, _, _) => {
                    return Err((l, "Unterminated tail list".to_string()));
                }
            }
        } else {
            let this_char = s[n];
            let next_location = start.clone().advance(this_char);

            match parse_sexp_step(start.clone(), p.borrow(), this_char) {
                SExpParseResult::PError(l,e) => { return Err((l,e)); },
                SExpParseResult::PResume(np) => {
                    start = next_location;
                    p = np;
                    n = n + 1;
                },
                SExpParseResult::PEmit(o,np) => {
                    p = np;
                    n = n + 1;
                    res.push(o);
                }
            }
        }
    }
}

pub fn parse_sexp(start: Srcloc, input: &String) -> Result<Vec<Rc<SExp>>, (Srcloc, String)> {
    parse_sexp_inner(start, SExpParseState::Empty, 0, &input.as_bytes().to_vec())
}
