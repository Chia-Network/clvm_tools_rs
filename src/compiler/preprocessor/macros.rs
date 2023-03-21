use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;
use num_bigint::ToBigInt;
use num_traits::ToPrimitive;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};

use crate::compiler::clvm::truthy;
use crate::compiler::comptypes::{BodyForm, CompileErr};
use crate::compiler::evaluate::{EvalExtension, Evaluator};
use crate::compiler::preprocessor::dequote;
use crate::compiler::sexp::{SExp, decode_string};
use crate::compiler::srcloc::{Srcloc};
use crate::util::{Number, number_from_u8};

// If the bodyform represents a constant, only match a quoted string.
fn match_quoted_string(body: Rc<BodyForm>) -> Result<Option<(Srcloc, Vec<u8>)>, CompileErr> {
    let is_string =
        match body.borrow() {
            BodyForm::Quoted(SExp::QuotedString(_,b'x',_)) => {
                None
            }
            BodyForm::Quoted(SExp::QuotedString(al,_,an)) => {
                Some((al.clone(), an.clone()))
            }
            BodyForm::Value(SExp::QuotedString(_,b'x',_)) => {
                None
            }
            BodyForm::Value(SExp::QuotedString(al,_,an)) => {
                Some((al.clone(), an.clone()))
            }
            BodyForm::Quoted(_) => {
                None
            }
            _ => {
                return Ok(None);
            }
        };

    if let Some((loc, s)) = is_string {
        Ok(Some((loc, s)))
    } else {
        Err(CompileErr(body.loc(), "string required".to_string()))
    }
}

fn match_atom(body: Rc<BodyForm>) -> Result<Option<(Srcloc, Vec<u8>)>, CompileErr> {
    if let BodyForm::Quoted(SExp::Atom(al,an)) = body.borrow() {
        Ok(Some((al.clone(),an.clone())))
    } else if let BodyForm::Quoted(_) = body.borrow() {
        Err(CompileErr(body.loc(), "atom required".to_string()))
    } else {
        Ok(None)
    }
}

enum MatchedNumber {
    MatchedInt(Srcloc, Number),
    MatchedHex(Srcloc, Vec<u8>)
}

fn match_number(body: Rc<BodyForm>) -> Result<Option<MatchedNumber>, CompileErr> {
    match body.borrow() {
        BodyForm::Quoted(SExp::Integer(il,n)) => {
            Ok(Some(MatchedNumber::MatchedInt(il.clone(), n.clone())))
        }
        BodyForm::Quoted(SExp::QuotedString(ql,b'x',b)) => {
            Ok(Some(MatchedNumber::MatchedHex(ql.clone(), b.clone())))
        }
        BodyForm::Quoted(SExp::Nil(il)) => {
            Ok(Some(MatchedNumber::MatchedInt(il.clone(), bi_zero())))
        }
        BodyForm::Quoted(_) => {
            Err(CompileErr(body.loc(), "number required".to_string()))
        }
        _ => Ok(None)
    }
}

fn numeric_value(body: Rc<BodyForm>) -> Result<Number, CompileErr> {
    match match_number(body.clone())? {
        Some(MatchedNumber::MatchedInt(_, n)) => Ok(n.clone()),
        Some(MatchedNumber::MatchedHex(_, h)) => Ok(number_from_u8(&h)),
        _ => Err(CompileErr(body.loc(), "Not a number".to_string()))
    }
}

fn usize_value(body: Rc<BodyForm>) -> Result<usize, CompileErr> {
    let n = numeric_value(body.clone())?;
    if let Some(res) = n.to_usize() {
        Ok(res)
    } else {
        Err(CompileErr(body.loc(), "Value out of range".to_string()))
    }
}

fn reify_args(
    evaluator: &Evaluator,
    prog_args: Rc<SExp>,
    env: &HashMap<Vec<u8>, Rc<BodyForm>>,
    args: &[Rc<BodyForm>]
) -> Result<Vec<Rc<BodyForm>>, CompileErr> {
    let mut allocator = Allocator::new();
    let mut converted_args = Vec::new();
    for a in args.iter() {
        let shrunk = evaluator.shrink_bodyform(
            &mut allocator,
            prog_args.clone(),
            env,
            a.clone(),
            false,
            None
        )?;
        converted_args.push(shrunk);
    }
    Ok(converted_args)
}

/// A container for a function to evaluate in advanced preprocessor macros.
/// We use this trait (which is very similar to the extension trait in Evaluator)
/// as a definite handler for a specific named form, so optional returns aren't
/// needed.  These are held in a collection and looked up.  To be maximally
/// conservative with typing and lifetime, we hold these via Rc<dyn ...>.
pub trait ExtensionFunction {
    fn want_interp(&self) -> bool { true }
    fn required_args(&self) -> Option<usize>;
    fn try_eval(
        &self,
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr>;
}

struct StringQ { }

impl StringQ {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(StringQ { }) }
}

impl ExtensionFunction for StringQ {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let res =
            match match_quoted_string(args[0].clone()) {
                Ok(Some(_)) => {
                    SExp::Integer(loc.clone(), bi_one())
                }
                Ok(None) => {
                    return Ok(body.clone());
                }
                Err(_) => {
                    SExp::Nil(loc.clone())
                }
            };

        Ok(Rc::new(BodyForm::Quoted(res)))
    }
}

struct NumberQ { }

impl NumberQ {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(NumberQ { }) }
}

impl ExtensionFunction for NumberQ {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let res =
            match match_number(args[0].clone()) {
                Ok(Some(_)) => {
                    SExp::Integer(loc.clone(), bi_one())
                }
                Ok(None) => {
                    return Ok(body.clone());
                }
                Err(_) => {
                    SExp::Nil(loc.clone())
                }
            };

        Ok(Rc::new(BodyForm::Quoted(res)))
    }
}

struct SymbolQ { }

impl SymbolQ {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(SymbolQ { }) }
}

impl ExtensionFunction for SymbolQ {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let res =
            match match_atom(args[0].clone()) {
                Ok(Some(_)) => {
                    SExp::Integer(loc.clone(), bi_one())
                }
                Ok(None) => {
                    return Ok(body.clone());
                }
                Err(_) => {
                    SExp::Nil(loc.clone())
                }
            };

        Ok(Rc::new(BodyForm::Quoted(res)))
    }
}

struct SymbolToString { }

impl SymbolToString {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(SymbolToString { }) }
}

impl ExtensionFunction for SymbolToString {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let Some((loc, value)) = match_atom(args[0].clone())? {
            return Ok(Rc::new(BodyForm::Quoted(SExp::QuotedString(loc,b'\"',value))));
        } else {
            return Ok(body.clone());
        }
    }
}

struct StringToSymbol { }

impl StringToSymbol {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(StringToSymbol { }) }
}

impl ExtensionFunction for StringToSymbol {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let Some((loc, value)) = match_quoted_string(args[0].clone())? {
            return Ok(Rc::new(BodyForm::Quoted(SExp::Atom(loc,value))));
        } else {
            return Ok(body.clone());
        }
    }
}

struct StringAppend { }

impl StringAppend {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(StringAppend { }) }
}

impl ExtensionFunction for StringAppend {
    fn required_args(&self) -> Option<usize> { None }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut out_vec = Vec::new();
        let mut out_loc = None;
        for a in args.iter() {
            if let Some((loc, mut value)) = match_quoted_string(a.clone())? {
                if out_loc.is_none() {
                    out_loc = Some(loc);
                }
                out_vec.append(&mut value);
            } else {
                return Ok(body.clone());
            }
        }
        return Ok(Rc::new(BodyForm::Quoted(SExp::QuotedString(out_loc.unwrap_or_else(|| body.loc()),b'\"',out_vec))));
    }
}

struct NumberToString { }

impl NumberToString {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(NumberToString { }) }
}

impl ExtensionFunction for NumberToString {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let match_res = match_number(args[0].clone())?;
        let (use_loc, int_val) =
            match &match_res {
                Some(MatchedNumber::MatchedInt(l,i)) => { (l.clone(), i.clone()) }
                Some(MatchedNumber::MatchedHex(l,h)) => {
                    (l.clone(), number_from_u8(&h))
                }
                _ => {
                    return Ok(body.clone());
                }
            };
        Ok(Rc::new(BodyForm::Quoted(SExp::QuotedString(use_loc, b'\"', int_val.to_string().as_bytes().to_vec()))))
    }
}

struct StringToNumber { }

impl StringToNumber {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(StringToNumber { }) }
}

impl ExtensionFunction for StringToNumber {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        _body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let Some((loc, value)) = match_quoted_string(args[0].clone())? {
            if let Ok(cvt_bi) = decode_string(&value).parse::<Number>() {
                Ok(Rc::new(BodyForm::Quoted(SExp::Integer(loc.clone(), cvt_bi))))
            } else {
                Err(CompileErr(loc.clone(), "bad number".to_string()))
            }
        } else {
            Err(CompileErr(loc.clone(), "should be given a string".to_string()))
        }
    }
}

struct StringLength { }

impl StringLength {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(StringLength { }) }
}

impl ExtensionFunction for StringLength {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let Some((loc, value)) = match_quoted_string(args[0].clone())? {
            if let Some(len_bi) = value.len().to_bigint() {
                Ok(Rc::new(BodyForm::Quoted(SExp::Integer(loc.clone(), len_bi))))
            } else {
                Err(CompileErr(loc.clone(), "Error getting string length".to_string()))
            }
        } else {
            Ok(body.clone())
        }
    }
}


struct Substring { }

impl Substring {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(Substring { }) }
}

impl ExtensionFunction for Substring {
    fn required_args(&self) -> Option<usize> { Some(3) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let start_element = usize_value(args[1].clone())?;
        let end_element = usize_value(args[2].clone())?;

        match args[0].borrow() {
            BodyForm::Quoted(SExp::QuotedString(l,ch,s)) => {
                if start_element > end_element || start_element > s.len() || end_element > s.len() {
                    return Err(CompileErr(l.clone(), "start greater than end in substring".to_string()));
                }
                let result_value: Vec<u8> =
                    s.iter().take(end_element).skip(start_element).copied().collect();
                Ok(Rc::new(BodyForm::Quoted(SExp::QuotedString(l.clone(), *ch, result_value))))
            }
            BodyForm::Quoted(_) => {
                Err(CompileErr(body.loc(), "Not a string".to_string()))
            }
            _ => {
                Ok(body.clone())
            }
        }
    }
}

struct List { }

impl List {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(List { }) }
}

impl ExtensionFunction for List {
    fn required_args(&self) -> Option<usize> { None }

    fn try_eval(
        &self,
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        _body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut allocator = Allocator::new();
        let mut res = Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone())));
        for a in args.iter().rev() {
            res = Rc::new(BodyForm::Call(
                loc.clone(),
                vec![
                    Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), b"c".to_vec()))),
                    a.clone(),
                    res
                ]
            ));
        }
        evaluator.shrink_bodyform(
            &mut allocator,
            prog_args.clone(),
            env,
            res,
            false,
            None
        )
    }
}

struct Cons { }

impl Cons {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(Cons { }) }
}

impl ExtensionFunction for Cons {
    fn required_args(&self) -> Option<usize> { Some(2) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let (BodyForm::Quoted(a), BodyForm::Quoted(b)) = (args[0].borrow(), args[1].borrow()) {
            Ok(Rc::new(BodyForm::Quoted(SExp::Cons(loc.clone(), Rc::new(a.clone()), Rc::new(b.clone())))))
        } else {
            Ok(body.clone())
        }
    }
}

struct First { }

impl First {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(First { }) }
}

impl ExtensionFunction for First {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let BodyForm::Quoted(SExp::Cons(_,a,_)) = args[0].borrow() {
            let a_borrowed: &SExp = a.borrow();
            Ok(Rc::new(BodyForm::Quoted(a_borrowed.clone())))
        } else if let BodyForm::Quoted(_) = args[0].borrow() {
            Err(CompileErr(loc.clone(), "bad cons in first".to_string()))
        } else {
            Ok(body.clone())
        }
    }
}

struct Rest { }

impl Rest {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(Rest { }) }
}

impl ExtensionFunction for Rest {
    fn required_args(&self) -> Option<usize> { Some(1) }

    fn try_eval(
        &self,
        _evaluator: &Evaluator,
        _prog_args: Rc<SExp>,
        _env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let BodyForm::Quoted(SExp::Cons(_,_,b)) = args[0].borrow() {
            let a_borrowed: &SExp = b.borrow();
            Ok(Rc::new(BodyForm::Quoted(a_borrowed.clone())))
        } else if let BodyForm::Quoted(_) = args[0].borrow() {
            Err(CompileErr(loc.clone(), "bad cons in rest".to_string()))
        } else {
            Ok(body.clone())
        }
    }
}

struct If { }

impl If {
    fn new() -> Rc<dyn ExtensionFunction> { Rc::new(If { }) }
}

impl ExtensionFunction for If {
    fn want_interp(&self) -> bool { false }

    fn required_args(&self) -> Option<usize> { Some(3) }

    fn try_eval(
        &self,
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        _loc: &Srcloc,
        _name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut allocator = Allocator::new();
        let cond_result =
            evaluator.shrink_bodyform(
                &mut allocator,
                prog_args.clone(),
                env,
                args[0].clone(),
                false,
                None
            )?;

        if let Ok(unquoted) = dequote(body.loc(), cond_result) {
            if truthy(unquoted) {
                evaluator.shrink_bodyform(
                    &mut allocator,
                    prog_args.clone(),
                    env,
                    args[1].clone(),
                    false,
                    None
                )
            } else {
                evaluator.shrink_bodyform(
                    &mut allocator,
                    prog_args.clone(),
                    env,
                    args[2].clone(),
                    false,
                    None
                )
            }
        } else {
            Ok(body.clone())
        }
    }
}

/// An evaluator extension for the preprocessor.
///
/// Implements scheme like conversion functions for handling chialisp programs and
/// bits of them.
///
/// These functions are provided:
///
/// Enhanced versions of builtin macros:
///
/// if   -- first class short circuiting, no round trip to CLVM space
/// list -- simple own implementation
/// c    -- cons preserving exact input values
/// f    -- first and rest exactly preserving part of cons.
/// r    --
///
/// Queries
///
/// string?
/// number?
/// symbol?
///
/// Basic conversion
///
/// string->symbol
/// symbol->string
/// string->number
/// number->string
///
/// Working with values
///
/// string-append s0 s1 ...
/// string-length
/// substring s start end
///
pub struct PreprocessorExtension {
    extfuns: HashMap<Vec<u8>, Rc<dyn ExtensionFunction>>
}

impl PreprocessorExtension {
    pub fn new() -> Self {
        let extfuns = [
            (b"if".to_vec(), If::new()),
            (b"list".to_vec(), List::new()),
            (b"c".to_vec(), Cons::new()),
            (b"f".to_vec(), First::new()),
            (b"r".to_vec(), Rest::new()),

            (b"string?".to_vec(), StringQ::new()),
            (b"number?".to_vec(), NumberQ::new()),
            (b"symbol?".to_vec(), SymbolQ::new()),

            (b"string->symbol".to_vec(), StringToSymbol::new()),
            (b"symbol->string".to_vec(), SymbolToString::new()),
            (b"string->number".to_vec(), StringToNumber::new()),
            (b"number->string".to_vec(), NumberToString::new()),

            (b"string-append".to_vec(), StringAppend::new()),
            (b"string-length".to_vec(), StringLength::new()),
            (b"substring".to_vec(), Substring::new()),
        ];
        PreprocessorExtension { extfuns: HashMap::from(extfuns) }
    }
}

impl EvalExtension for PreprocessorExtension {
    fn try_eval(
        &self,
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
        raw_args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Option<Rc<BodyForm>>, CompileErr> {
        if let Some(extfun) = self.extfuns.get(name) {
            if let Some(n) = extfun.required_args() {
                if raw_args.len() != n {
                    return Err(CompileErr(loc.clone(), format!("{} requires {} args", decode_string(name), n)));
                }
            }

            eprintln!("try function {}", body.to_sexp());
            for (n,v) in env.iter() {
                eprintln!("- {} = {}", decode_string(&n), v.to_sexp());
            }
            let args =
                if extfun.want_interp() {
                    reify_args(
                        evaluator,
                        prog_args.clone(),
                        env,
                        raw_args
                    )?
                } else {
                    raw_args.to_vec()
                };
            Ok(Some(extfun.try_eval(
                evaluator,
                prog_args,
                env,
                loc,
                name,
                &args,
                body
            )?))
        } else {
            Ok(None)
        }
    }
}
