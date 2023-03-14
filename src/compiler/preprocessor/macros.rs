use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;

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
            BodyForm::Quoted(SExp::QuotedString(al,b'x',an)) => {
                None
            }
            BodyForm::Quoted(SExp::QuotedString(al,_,an)) => {
                Some((al.clone(), an.clone()))
            }
            BodyForm::Value(SExp::QuotedString(al,b'x',an)) => {
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
    if let BodyForm::Quoted(SExp::Integer(il,n)) = body.borrow() {
        Ok(Some(MatchedNumber::MatchedInt(il.clone(), n.clone())))
    } else if let BodyForm::Quoted(SExp::QuotedString(ql,b'x',b)) = body.borrow() {
        Ok(Some(MatchedNumber::MatchedHex(ql.clone(), b.clone())))
    } else if let BodyForm::Quoted(_) = body.borrow() {
        Err(CompileErr(body.loc(), "number required".to_string()))
    } else {
        Ok(None)
    }
}

fn reify_args(
    evaluator: &Evaluator,
    prog_args: Rc<SExp>,
    env: &HashMap<Vec<u8>, Rc<BodyForm>>,
    loc: &Srcloc,
    args: &[Rc<BodyForm>]
) -> Result<Vec<Rc<BodyForm>>, CompileErr> {
    let mut allocator = Allocator::new();
    let mut converted_args = Vec::new();
    for a in args.iter() {
        eprintln!("shrink {}", a.to_sexp());
        for (n,e) in env.iter() {
            eprintln!("- {} = {}", decode_string(&n), e.to_sexp());
        }
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        if let Some((loc, value)) = match_quoted_string(args[0].clone())? {
            return Ok(Rc::new(BodyForm::Quoted(SExp::Atom(loc,value))));
        } else {
            eprintln!("pp helper returned {}", decode_string(name));
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
                eprintln!("pp helper returned {}", decode_string(name));
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        todo!();
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
        evaluator: &Evaluator,
        prog_args: Rc<SExp>,
        env: &HashMap<Vec<u8>, Rc<BodyForm>>,
        loc: &Srcloc,
        name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        todo!();
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
        name: &[u8],
        args: &[Rc<BodyForm>],
        body: Rc<BodyForm>,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let mut res = SExp::Nil(loc.clone());
        for (n,e) in env.iter() {
            eprintln!("- {} = {}", decode_string(&n), e.to_sexp());
        }
        for a in args.iter().rev() {
            eprintln!("list arg {}", a.to_sexp());
            if let Ok(unquoted) = dequote(loc.clone(), a.clone()) {
                res = SExp::Cons(
                    loc.clone(),
                    unquoted,
                    Rc::new(res)
                );
            } else {
                return Ok(body.clone());
            }
        }
        let list_res = BodyForm::Quoted(res);
        eprintln!("list_res {}", list_res.to_sexp());
        Ok(Rc::new(list_res))
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
        loc: &Srcloc,
        name: &[u8],
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
            eprintln!("unquoted {}", unquoted);
            if truthy(unquoted) {
                eprintln!("truthy, expand {}", args[1].to_sexp());
                evaluator.shrink_bodyform(
                    &mut allocator,
                    prog_args.clone(),
                    env,
                    args[1].clone(),
                    false,
                    None
                )
            } else {
                eprintln!("falsey, expand {}", args[2].to_sexp());
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
            eprintln!("can't reduce if {}", body.to_sexp());
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
/// Queries
///
/// pair?
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
/// substring s start end
pub struct PreprocessorExtension {
    extfuns: HashMap<Vec<u8>, Rc<dyn ExtensionFunction>>
}

impl PreprocessorExtension {
    pub fn new() -> Self {
        let extfuns = [
            (b"if".to_vec(), If::new()),
            (b"list".to_vec(), List::new()),

            (b"string?".to_vec(), StringQ::new()),
            (b"number?".to_vec(), NumberQ::new()),
            (b"symbol?".to_vec(), SymbolQ::new()),

            (b"string->symbol".to_vec(), StringToSymbol::new()),
            (b"symbol->string".to_vec(), SymbolToString::new()),
            (b"string->number".to_vec(), StringToNumber::new()),
            (b"number->string".to_vec(), NumberToString::new()),

            (b"string-append".to_vec(), StringAppend::new()),
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
            let args =
                if extfun.want_interp() {
                    reify_args(
                        evaluator,
                        prog_args.clone(),
                        env,
                        loc,
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
