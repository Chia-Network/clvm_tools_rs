#[cfg(test)]
use rand::distributions::Standard;
#[cfg(test)]
use rand::prelude::Distribution;
#[cfg(test)]
use rand::Rng;

use std::borrow::Borrow;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::string::String;

use binascii::{bin2hex, hex2bin};
use num_traits::{zero, Num};

use crate::classic::clvm::__type_compatibility__::{bi_zero, Bytes, BytesFromType};
use crate::classic::clvm::casts::{bigint_from_bytes, bigint_to_bytes_clvm, TConvertOption};
use crate::compiler::prims::prims;
use crate::compiler::srcloc::Srcloc;
use crate::util::{number_from_u8, u8_from_number, Number};

pub const MAX_SEXP_COST: usize = 15;

// Compiler view of SExp
#[derive(Clone, Debug)]
pub enum SExp {
    Nil(Srcloc),
    Cons(Srcloc, Rc<SExp>, Rc<SExp>),
    Integer(Srcloc, Number),
    QuotedString(Srcloc, u8, Vec<u8>),
    Atom(Srcloc, Vec<u8>),
}

#[cfg(test)]
pub fn random_atom_name<R: Rng + ?Sized>(rng: &mut R, min_size: usize) -> Vec<u8> {
    let mut bytevec: Vec<u8> = Vec::new();
    let mut len = 0;
    loop {
        let mut n: u8 = rng.gen();
        n %= 40;
        len += 1;
        if n < 26 || len < min_size {
            bytevec.push((n % 26) + 97); // lowercase a
        } else {
            break;
        }
    }
    bytevec
}

#[cfg(test)]
pub fn random_atom<R: Rng + ?Sized>(rng: &mut R) -> SExp {
    SExp::Atom(Srcloc::start("*rng*"), random_atom_name(rng, 1))
}

#[cfg(test)]
pub fn random_sexp<R: Rng + ?Sized>(rng: &mut R, remaining: usize) -> SExp {
    if remaining < 2 {
        random_atom(rng)
    } else {
        let loc = || Srcloc::start("*rng*");
        let alternative: usize = rng.gen_range(0..=2);
        match alternative {
            0 => {
                // list
                let length = rng.gen_range(1..=remaining);
                let costs = vec![remaining / length; length];
                enlist(
                    loc(),
                    costs
                        .iter()
                        .map(|c| Rc::new(random_sexp(rng, *c)))
                        .collect(),
                )
            }
            1 => {
                // cons
                let left_cost = rng.gen_range(1..=remaining);
                let right_cost = remaining - left_cost;
                SExp::Cons(
                    loc(),
                    Rc::new(random_sexp(rng, left_cost)),
                    Rc::new(random_sexp(rng, right_cost)),
                )
            }
            _ => {
                // atom
                random_atom(rng)
            }
        }
    }
}

// Thanks: https://stackoverflow.com/questions/48490049/how-do-i-choose-a-random-value-from-an-enum
#[cfg(test)]
impl Distribution<SExp> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        random_sexp(rng, MAX_SEXP_COST)
    }
}

impl Eq for SExp {}

impl PartialEq for SExp {
    fn eq(&self, other: &Self) -> bool {
        self.equal_to(other)
    }
}

impl Display for SExp {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            SExp::Nil(_) => {
                formatter.write_str("()")?;
            }
            SExp::Cons(_, a, b) => {
                formatter.write_str("(")?;
                formatter.write_str(&list_no_parens(a, b))?;
                formatter.write_str(")")?;
            }
            SExp::Integer(_, v) => {
                formatter.write_str(&v.to_string())?;
            }
            SExp::QuotedString(_, q, s) => {
                if printable(s) {
                    formatter.write_str("\"")?;
                    formatter.write_str(&escape_quote(*q, s))?;
                    formatter.write_str("\"")?;
                } else {
                    let vlen = s.len() * 2;
                    let mut outbuf = vec![0; vlen];
                    bin2hex(s, &mut outbuf).map_err(|_e| std::fmt::Error::default())?;
                    formatter.write_str("0x")?;
                    formatter.write_str(
                        std::str::from_utf8(&outbuf).expect("only hex digits expected"),
                    )?;
                }
            }
            SExp::Atom(l, a) => {
                if a.is_empty() {
                    formatter.write_str("()")?;
                } else if printable(a) {
                    formatter.write_str(&decode_string(a))?;
                } else {
                    formatter
                        .write_str(&SExp::Integer(l.clone(), number_from_u8(a)).to_string())?;
                }
            }
        }

        Ok(())
    }
}

impl Hash for SExp {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        match self {
            SExp::Nil(l) => {
                SExp::Atom(l.clone(), Vec::new()).hash(state);
            }
            SExp::Cons(_, a, b) => {
                a.hash(state);
                b.hash(state);
            }
            SExp::Atom(_, a) => {
                a.hash(state);
            }
            SExp::QuotedString(_, _, a) => {
                a.hash(state);
            }
            SExp::Integer(_, i) => {
                u8_from_number(i.clone()).hash(state);
            }
        }
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
    TermList(Srcloc, Rc<SExpParseState>, Vec<Rc<SExp>>),
}

#[derive(Debug)]
enum SExpParseResult {
    Resume(SExpParseState),
    Emit(Rc<SExp>, SExpParseState),
    Error(Srcloc, String),
}

#[derive(Debug)]
enum Integral {
    Decimal,
    Hex,
    NotIntegralValue,
}

fn is_hex(s: &[u8]) -> bool {
    s.len() >= 2 && s[0] == b'0' && s[1] == b'x'
}

fn is_dec(s: &[u8]) -> bool {
    let mut first = true;
    let mut dec = true;

    for ch in s {
        if first && *ch == b'-' {
            // Nothing
        } else if !(*ch >= b'0' && *ch <= b'9') {
            dec = false;
            break;
        }
        first = false;
    }

    dec && *s != vec![b'-']
}

fn matches_integral(s: &[u8]) -> Integral {
    if is_hex(s) {
        Integral::Hex
    } else if is_dec(s) {
        Integral::Decimal
    } else {
        Integral::NotIntegralValue
    }
}

fn normalize_int(v: Vec<u8>, base: u32) -> Number {
    let s = Bytes::new(Some(BytesFromType::Raw(v))).decode();
    Number::from_str_radix(&s, base).unwrap()
}

// Hex values are _not_ numbers, they're byte strings expressed in hexadecimal
// while they correspond numerically, integral constants are byte-padded to the
// left to retain their sign and hex constants are considered unsigned so _not_
// padded.
fn from_hex(l: Srcloc, v: &[u8]) -> SExp {
    let mut result = vec![0; (v.len() - 2) / 2];
    hex2bin(&v[2..], &mut result).expect("should convert from hex");
    SExp::QuotedString(l, b'"', result)
}

fn make_atom(l: Srcloc, v: Vec<u8>) -> SExp {
    let alen = v.len();
    if alen > 1 && v[0] == b'#' {
        // Search prims for appropriate primitive
        let want_name = v[1..].to_vec();
        for p in prims() {
            if want_name == p.0 {
                return p.1;
            }
        }

        // Fallback (probably)
        SExp::Atom(l, v[1..].to_vec())
    } else {
        match matches_integral(&v) {
            Integral::Hex => from_hex(l, &v),
            Integral::Decimal => {
                let intval = normalize_int(v, 10);
                if intval == bi_zero() {
                    SExp::Nil(l)
                } else {
                    SExp::Integer(l, intval)
                }
            }
            Integral::NotIntegralValue => SExp::Atom(l, v),
        }
    }
}

pub fn enlist(l: Srcloc, v: Vec<Rc<SExp>>) -> SExp {
    let mut result = SExp::Nil(l);
    for i_reverse in 0..v.len() {
        let i = v.len() - i_reverse - 1;
        result = make_cons(v[i].clone(), Rc::new(result));
    }
    result
}

fn emit(a: Rc<SExp>, p: SExpParseState) -> SExpParseResult {
    SExpParseResult::Emit(a, p)
}

fn error(l: Srcloc, t: &str) -> SExpParseResult {
    SExpParseResult::Error(l, t.to_string())
}

fn resume(p: SExpParseState) -> SExpParseResult {
    SExpParseResult::Resume(p)
}

fn escape_quote(q: u8, s: &[u8]) -> String {
    let mut res: Vec<char> = Vec::new();
    let _: Vec<()> = s
        .iter()
        .map(|ch| {
            if *ch == q as u8 {
                res.push('\\');
            }
            res.push(*ch as char);
        })
        .collect();
    res.into_iter().collect()
}

fn list_no_parens(a: &SExp, b: &SExp) -> String {
    if b.nilp() {
        a.to_string()
    } else {
        match b {
            SExp::Cons(_, b, c) => a.to_string() + " " + &list_no_parens(b, c),
            _ => a.to_string() + " . " + &b.to_string(),
        }
    }
}

pub fn decode_string(v: &[u8]) -> String {
    return String::from_utf8_lossy(v).as_ref().to_string();
}

fn printable(a: &[u8]) -> bool {
    for ch in a.iter() {
        if (*ch as char).is_control() || !(*ch as char).is_ascii() {
            return false;
        }
    }

    true
}

impl SExp {
    pub fn loc(&self) -> Srcloc {
        match self {
            SExp::Nil(l) => l.clone(),
            SExp::Cons(l, _, _) => l.clone(),
            SExp::Integer(l, _) => l.clone(),
            SExp::QuotedString(l, _, _) => l.clone(),
            SExp::Atom(l, _) => l.clone(),
        }
    }

    pub fn with_loc(&self, loc: Srcloc) -> SExp {
        match self {
            SExp::Nil(_) => SExp::Nil(loc),
            SExp::Cons(_, a, b) => SExp::Cons(loc, a.clone(), b.clone()),
            SExp::Integer(_, i) => SExp::Integer(loc, i.clone()),
            SExp::QuotedString(_, q, s) => SExp::QuotedString(loc, *q, s.clone()),
            SExp::Atom(_, a) => SExp::Atom(loc, a.clone()),
        }
    }

    pub fn atom_from_string(loc: Srcloc, s: &str) -> SExp {
        SExp::Atom(loc, s.as_bytes().to_vec())
    }

    pub fn atom_from_vec(loc: Srcloc, s: &[u8]) -> SExp {
        SExp::Atom(loc, s.to_vec())
    }

    pub fn quoted_from_string(loc: Srcloc, s: &str) -> SExp {
        SExp::QuotedString(loc, b'\"', s.as_bytes().to_vec())
    }

    pub fn nilp(&self) -> bool {
        let bizero: Number = zero();
        match self {
            SExp::Nil(_) => true,
            SExp::QuotedString(_, _, v) => v.is_empty(),
            SExp::Integer(_, i) => *i == bizero,
            SExp::Atom(_, a) => a.is_empty(),
            _ => false,
        }
    }

    pub fn listp(&self) -> bool {
        matches!(self, SExp::Nil(_) | SExp::Cons(_, _, _))
    }

    pub fn cons_fst(&self) -> Rc<SExp> {
        match self {
            SExp::Cons(_, a, _) => a.clone(),
            _ => Rc::new(SExp::Nil(self.loc())),
        }
    }

    pub fn cons_snd(&self) -> Rc<SExp> {
        match self {
            SExp::Cons(_, _, b) => b.clone(),
            _ => Rc::new(SExp::Nil(self.loc())),
        }
    }

    pub fn encode_mut(&self, v: &mut Vec<u8>) {
        match self {
            SExp::Nil(_) => v.push(0x80),
            SExp::Cons(_, a, b) => {
                v.push(0xff);
                a.encode_mut(v);
                b.encode_mut(v);
            }
            SExp::Integer(_, i) => {
                let mut bi_bytes = bigint_to_bytes_clvm(i).data().to_vec();

                v.append(&mut bi_bytes);
            }
            SExp::QuotedString(l, _, s) => {
                SExp::Integer(l.clone(), number_from_u8(s)).encode_mut(v);
            }
            SExp::Atom(l, a) => {
                SExp::Integer(l.clone(), number_from_u8(a)).encode_mut(v);
            }
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        self.encode_mut(&mut v);
        v
    }

    pub fn to_bigint(&self) -> Option<Number> {
        match self {
            SExp::Nil(_) => Some(zero()),
            SExp::Integer(_, v) => Some(v.clone()),
            SExp::QuotedString(_, _, v) => Some(bigint_from_bytes(
                &Bytes::new(Some(BytesFromType::Raw(v.to_vec()))),
                Some(TConvertOption { signed: true }),
            )),
            SExp::Atom(_, v) => Some(bigint_from_bytes(
                &Bytes::new(Some(BytesFromType::Raw(v.to_vec()))),
                Some(TConvertOption { signed: true }),
            )),
            _ => None,
        }
    }

    pub fn equal_to(&self, other: &SExp) -> bool {
        if self.nilp() && other.nilp() {
            true
        } else if self.nilp() || other.nilp() {
            false
        } else {
            match (self, other) {
                (SExp::Cons(_, r, s), SExp::Cons(_, t, u)) => r.equal_to(t) && s.equal_to(u),
                (SExp::Cons(_, _, _), _) => false,
                (_, SExp::Cons(_, _, _)) => false,
                (SExp::Integer(l, a), b) => SExp::Atom(l.clone(), u8_from_number(a.clone())) == *b,
                (SExp::QuotedString(l, _, a), b) => SExp::Atom(l.clone(), a.clone()) == *b,
                (SExp::Nil(l), b) => SExp::Atom(l.clone(), Vec::new()) == *b,
                (SExp::Atom(_, _), SExp::Integer(_, _)) => other == self,
                (SExp::Atom(_, _), SExp::QuotedString(_, _, _)) => other == self,
                (SExp::Atom(_, _), SExp::Nil(_)) => other == self,
                (SExp::Atom(_, a), SExp::Atom(_, b)) => a == b,
            }
        }
    }

    pub fn proper_list(&self) -> Option<Vec<SExp>> {
        let mut res = Vec::new();
        let mut track = Rc::new(self.clone());

        loop {
            if track.nilp() {
                return Some(res);
            } else {
                match track.borrow() {
                    SExp::Cons(_, l, r) => {
                        let borrowed: &SExp = l.borrow();
                        let cloned: SExp = borrowed.clone();
                        res.push(cloned);
                        track = r.clone();
                    }
                    _ => {
                        return None;
                    }
                }
            }
        }
    }

    pub fn get_number(&self) -> Result<Number, (Srcloc, String)> {
        match self {
            SExp::Integer(_, i) => Ok(i.clone()),
            SExp::Atom(_, v) => Ok(number_from_u8(v)),
            SExp::QuotedString(_, _, v) => Ok(number_from_u8(v)),
            SExp::Nil(_) => Ok(bi_zero()),
            _ => Err((self.loc(), format!("wanted atom got cons cell {}", self))),
        }
    }
}

fn parse_sexp_step(loc: Srcloc, p: &SExpParseState, this_char: u8) -> SExpParseResult {
    match p {
        SExpParseState::Empty => match this_char as char {
            '(' => resume(SExpParseState::OpenList(loc)),
            '\n' => resume(SExpParseState::Empty),
            ';' => resume(SExpParseState::CommentText(loc, Vec::new())),
            ')' => error(loc, "Too many close parens"),
            '"' => resume(SExpParseState::QuotedText(loc, b'"', Vec::new())),
            '\'' => resume(SExpParseState::QuotedText(loc, b'\'', Vec::new())),
            ch => {
                if char::is_whitespace(ch) {
                    resume(SExpParseState::Empty)
                } else {
                    resume(SExpParseState::Bareword(loc, vec![this_char]))
                }
            }
        },
        SExpParseState::CommentText(pl, t) => match this_char as char {
            '\r' => resume(SExpParseState::CommentText(pl.clone(), t.to_vec())),
            '\n' => resume(SExpParseState::Empty),
            _ => {
                let mut tcopy = t.to_vec();
                tcopy.push(this_char);
                resume(SExpParseState::CommentText(pl.ext(&loc), tcopy))
            }
        },
        SExpParseState::Bareword(pl, a) => {
            if char::is_whitespace(this_char as char) {
                emit(
                    Rc::new(make_atom(pl.clone(), a.to_vec())),
                    SExpParseState::Empty,
                )
            } else {
                let mut acopy = a.to_vec();
                acopy.push(this_char);
                resume(SExpParseState::Bareword(pl.ext(&loc), acopy))
            }
        }
        SExpParseState::QuotedText(pl, term, t) => {
            if this_char == b'\\' {
                resume(SExpParseState::QuotedEscaped(pl.clone(), *term, t.to_vec()))
            } else if this_char == *term {
                emit(
                    Rc::new(SExp::QuotedString(pl.ext(&loc), *term, t.to_vec())),
                    SExpParseState::Empty,
                )
            } else {
                let mut tcopy = t.to_vec();
                tcopy.push(this_char);
                resume(SExpParseState::QuotedText(pl.clone(), *term, tcopy))
            }
        }
        SExpParseState::QuotedEscaped(pl, term, t) => {
            let mut tcopy = t.to_vec();
            tcopy.push(this_char);
            resume(SExpParseState::QuotedText(pl.clone(), *term, tcopy))
        }
        SExpParseState::OpenList(pl) => match this_char as char {
            ')' => emit(Rc::new(SExp::Nil(pl.ext(&loc))), SExpParseState::Empty),
            '.' => error(loc, "Dot can't appear directly after begin paren"),
            _ => match parse_sexp_step(loc.clone(), &SExpParseState::Empty, this_char) {
                SExpParseResult::Emit(o, p) => resume(SExpParseState::ParsingList(
                    pl.ext(&loc),
                    Rc::new(p),
                    vec![o],
                )),
                SExpParseResult::Resume(p) => resume(SExpParseState::ParsingList(
                    pl.ext(&loc),
                    Rc::new(p),
                    Vec::new(),
                )),
                SExpParseResult::Error(l, e) => SExpParseResult::Error(l, e),
            },
        },
        SExpParseState::ParsingList(pl, pp, list_content) => {
            match (this_char as char, pp.borrow()) {
                ('.', SExpParseState::Empty) => resume(SExpParseState::TermList(
                    pl.ext(&loc),
                    Rc::new(SExpParseState::Empty),
                    list_content.to_vec(),
                )),
                (')', SExpParseState::Empty) => emit(
                    Rc::new(enlist(pl.ext(&loc), list_content.to_vec())),
                    SExpParseState::Empty,
                ),
                (')', SExpParseState::Bareword(l, t)) => {
                    let parsed_atom = make_atom(l.clone(), t.to_vec());
                    let mut updated_list = list_content.to_vec();
                    updated_list.push(Rc::new(parsed_atom));
                    emit(
                        Rc::new(enlist(pl.ext(&loc), updated_list)),
                        SExpParseState::Empty,
                    )
                }
                (_, _) => match parse_sexp_step(loc.clone(), pp.borrow(), this_char) {
                    SExpParseResult::Emit(o, p) => {
                        let mut list_copy = list_content.clone();
                        list_copy.push(o);
                        let result =
                            SExpParseState::ParsingList(pl.ext(&loc), Rc::new(p), list_copy);
                        resume(result)
                    }
                    SExpParseResult::Resume(rp) => resume(SExpParseState::ParsingList(
                        pl.ext(&loc),
                        Rc::new(rp),
                        list_content.to_vec(),
                    )),
                    SExpParseResult::Error(l, e) => SExpParseResult::Error(l, e),
                },
            }
        }
        SExpParseState::TermList(pl, pp, list_content) => match (this_char as char, pp.borrow()) {
            ('.', SExpParseState::Empty) => {
                error(loc, "Multiple dots in list notation are illegal")
            }
            (')', SExpParseState::Empty) => {
                if list_content.len() == 1 {
                    emit(list_content[0].clone(), SExpParseState::Empty)
                } else {
                    emit(
                        Rc::new(enlist(pl.ext(&loc), list_content.to_vec())),
                        SExpParseState::Empty,
                    )
                }
            }
            (')', SExpParseState::Bareword(l, t)) => {
                let parsed_atom = make_atom(l.clone(), t.to_vec());
                let mut list_copy = list_content.to_vec();
                match list_copy.pop() {
                    Some(v) => {
                        let new_tail = make_cons(v, Rc::new(parsed_atom));
                        if list_copy.is_empty() {
                            emit(Rc::new(new_tail), SExpParseState::Empty)
                        } else {
                            list_copy.push(Rc::new(new_tail));
                            let new_list = enlist(pl.ext(&loc), list_copy);
                            emit(Rc::new(new_list), SExpParseState::Empty)
                        }
                    }
                    None => error(loc, "Dot as first element of list?"),
                }
            }
            (_, _) => match parse_sexp_step(loc.clone(), pp.borrow(), this_char) {
                SExpParseResult::Emit(o, p) => {
                    let mut list_copy = list_content.to_vec();
                    match list_copy.pop() {
                        Some(v) => {
                            let new_tail = make_cons(v, o);
                            list_copy.push(Rc::new(new_tail));
                            resume(SExpParseState::TermList(
                                pl.ext(&loc),
                                Rc::new(p),
                                list_copy,
                            ))
                        }
                        None => error(loc, "Dot as first element of list?"),
                    }
                }
                SExpParseResult::Resume(p) => resume(SExpParseState::TermList(
                    pl.ext(&loc),
                    Rc::new(p),
                    list_content.to_vec(),
                )),
                SExpParseResult::Error(l, e) => SExpParseResult::Error(l, e),
            },
        },
    }
}

fn parse_sexp_inner<I>(
    start_: Srcloc,
    p_: SExpParseState,
    s: I,
) -> Result<Vec<Rc<SExp>>, (Srcloc, String)>
where
    I: Iterator<Item = u8>,
{
    let mut start = start_;
    let mut p = p_;
    let mut res = Vec::new();

    for this_char in s {
        let next_location = start.clone().advance(this_char);

        match parse_sexp_step(start.clone(), p.borrow(), this_char) {
            SExpParseResult::Error(l, e) => {
                return Err((l, e));
            }
            SExpParseResult::Resume(np) => {
                start = next_location;
                p = np;
            }
            SExpParseResult::Emit(o, np) => {
                start = next_location;
                p = np;
                res.push(o);
            }
        }
    }

    match p {
        SExpParseState::Empty => Ok(res),
        SExpParseState::Bareword(l, t) => Ok(vec![Rc::new(make_atom(l, t))]),
        SExpParseState::CommentText(_, _) => Ok(res),
        SExpParseState::QuotedText(l, _, _) => Err((l, "unterminated quoted string".to_string())),
        SExpParseState::QuotedEscaped(l, _, _) => {
            Err((l, "unterminated quoted string with escape".to_string()))
        }
        SExpParseState::OpenList(l) => Err((l, "Unterminated list (empty)".to_string())),
        SExpParseState::ParsingList(l, _, _) => Err((l, "Unterminated mid list".to_string())),
        SExpParseState::TermList(l, _, _) => Err((l, "Unterminated tail list".to_string())),
    }
}

pub fn parse_sexp<I>(start: Srcloc, input: I) -> Result<Vec<Rc<SExp>>, (Srcloc, String)>
where
    I: Iterator<Item = u8>,
{
    parse_sexp_inner(start, SExpParseState::Empty, input)
}
