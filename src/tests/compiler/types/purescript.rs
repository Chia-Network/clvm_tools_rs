#[cfg(test)]
use rand::prelude::*;
#[cfg(test)]
use rand;
#[cfg(test)]
use rand_chacha::ChaCha8Rng;

use num_bigint::ToBigInt;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{BodyForm, CompileForm, CompilerOpts, HelperForm};
use crate::compiler::sexp::{SExp, decode_string};
use crate::compiler::frontend::frontend;
use crate::compiler::fuzzer::FuzzProgram;
use crate::compiler::typechia::type_level_macro_transform;
use crate::util::Number;

lazy_static! {
    pub static ref PURESCRIPT_PREFIX: String = indoc!{"
module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)

data Atom = Atom
data Atom32 = Atom32
data Nullable a = EmptyNullable
data Pair a b = Pair
data Exec x = Exec
data ChiaFun a b = ChiaFun
data Any = Any

class Default x where
  default :: x

instance defaultAtom :: Default Atom where
  default = Atom

instance defaultAtom32 :: Default Atom32 where
  default = Atom32

instance defaultNullableA :: (Default a) => Default (Nullable a) where
  default = EmptyNullable

instance defaultPairAB :: (Default a, Default b) => Default (Pair a b) where
  default = Pair

instance defaultExecX :: (Default x) => Default (Exec x) where
  default = Exec

instance defaultChiaFunAB :: (Default a, Default b) => Default (ChiaFun a b) where
  default = ChiaFun

instance defaultAny :: Default Any where
  default = Any

-- The following constraints are used to implement the basic subtype ladder.
class Convert x y where
  cvt :: x -> y

instance cvtUnitUnit :: Convert Unit Unit where
  cvt _ = unit

instance cvtAnyUnit :: Convert Any Unit where
  cvt _ = unit

instance cvtNullableXUnit :: Convert (Nullable x) Unit where
  cvt _ = unit

instance cvtXNullableX :: Convert x (Nullable x) where
  cvt x = EmptyNullable

instance cvtUnitAny :: Convert Unit Any where
  cvt _ = Any

instance cvtAtomAny :: Convert Atom Any where
  cvt _ = Any

instance cvtAtom32Any :: Convert Atom32 Any where
  cvt _ = Any

instance cvtNullableXAny :: (Convert x Any) => Convert (Nullable x) Any where
  cvt _ = Any

instance cvtPairABAny :: (Convert a Any, Convert b Any) => Convert (Pair a b) Any where
  cvt Pair = Any

instance cvtAnyAny :: Convert Any Any where
  cvt _ = Any

instance cvtAtomAtom :: Convert Atom Atom where
  cvt Atom = Atom

instance cvtAtom32Atom :: Convert Atom32 Atom where
  cvt Atom32 = Atom

instance cvtUnitAtom :: Convert Unit Atom where
  cvt _ = Atom

instance cvtAnyAtom :: Convert Any Atom where
  cvt _ = Atom

instance cvtAtom32Atom32 :: Convert Atom32 Atom32 where
  cvt Atom32 = Atom32

instance cvtAnyAtom32 :: Convert Any Atom32 where
  cvt _ = Atom32

instance cvtPairABPairXY :: (Convert a x, Convert b y) => Convert (Pair a b) (Pair x y) where
  cvt Pair = Pair

instance cvtAnyPairAB :: (Convert Any a, Convert Any b) => Convert Any (Pair a b) where
  cvt x = Pair

instance cvtAnyExecX :: (Convert Any x) => Convert Any (Exec x) where
  cvt x = Exec

instance cvtAnyChiaFunAB :: Convert Any (ChiaFun a b) where
  cvt _ = ChiaFun

newtype List a = L1 (Nullable a)

instance cvtUnitList :: (Convert Any a) => Convert Unit (List a) where
  cvt _ = L1 EmptyNullable

instance cvtPairABList :: (Convert b (List a)) => Convert (Pair a b) (List a) where
  cvt _ = L1 EmptyNullable

sha256 :: List Atom -> Atom32
sha256 _ = Atom32

f :: forall f0 r0. (Default f0) => (Pair (Pair f0 r0) Unit) -> f0
f Pair = default
"}.to_string();

    pub static ref PURESCRIPT_SUFFIX: String = indoc!{"
main :: Effect Unit
main = do
  log \"compiled\"
"}.to_string();

    pub static ref PRIM_TO_CALL_MAP: HashMap<Vec<u8>, Vec<u8>> = {
        let mut op_dict = HashMap::new();

        op_dict.insert(b"-".to_vec(), b"subtract".to_vec());

        op_dict
    };
}

fn do_indent(indent: usize) -> String {
    let mut s = Vec::new();
    for _ in 0..=indent {
        s.push(b' ');
    }
    return decode_string(&s);
}

fn find_callable(prog: &CompileForm, name: &[u8]) -> Option<HelperForm> {
    for h in prog.helpers.iter() {
        if h.name() == name {
            match h {
                HelperForm::Defmacro(loc, name, macargs, macbody) => {
                    return Some(h.clone());
                },
                HelperForm::Defun(_, _, _, _, _, _) => {
                    // function call
                    return Some(h.clone());
                },
                _ => {
                    return None;
                }
            }
        }
    }

    PRIM_TO_CALL_MAP.get(name).map(|prim| {
        let l = prog.exp.to_sexp().loc();
        let nil = SExp::Nil(prog.exp.to_sexp().loc());
        HelperForm::Defun(
            l.clone(),
            prim.to_vec(),
            true,
            Rc::new(nil.clone()),
            Rc::new(BodyForm::Quoted(nil)),
            None
        )
    })
}

fn produce_body(opts: Rc<dyn CompilerOpts>, result_vec: &mut Vec<String>, prog: &CompileForm, indent: usize, body: &BodyForm) {
    eprintln!("-- produce_body {}", body.to_sexp());
    match body {
        BodyForm::Let(_, _, bindings, letbody) => {
            for b in bindings.iter() {
                result_vec.push(format!("{}{} <-", do_indent(indent), decode_string(&b.name)));
                produce_body(opts.clone(), result_vec, prog, indent + 2, letbody.borrow());
            }
        },
        BodyForm::Call(_, elts) => {
            if elts.is_empty() {
                result_vec.push(format!("{}pure unit", do_indent(indent)));
                return;
            }

            if let BodyForm::Value(SExp::Atom(_,n)) = elts[0].borrow() {
                eprintln!("call {}", decode_string(&n));
                if let Some(callable) = find_callable(prog, n) {
                    eprintln!("callable {}", callable.to_sexp());
                    if let HelperForm::Defun(_, _, _, _, _, _) = callable {
                        for (i,a) in elts.iter().skip(1).enumerate() {
                            result_vec.push(format!("{}arg_{} <-", do_indent(indent), i));
                            produce_body(opts.clone(), result_vec, prog, indent + 2, a);
                        }
                    } else if let HelperForm::Defmacro(loc, name, macargs, macbody) = callable {
                        // expand macro as in type synthesis.
                        let expanded_expression = type_level_macro_transform(
                            prog,
                            macbody.clone(),
                            loc.clone(),
                            &elts
                        ).unwrap();
                        produce_body(opts, result_vec, prog, indent, expanded_expression.borrow());
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            } else {
                todo!("{}", body.to_sexp())
            }
        },
        BodyForm::Quoted(SExp::Cons(_,a,b)) => {
            result_vec.push(format!("{}(cvt (Pair", do_indent(indent)));
            let borrowed_a: &SExp = a.borrow();
            let borrowed_b: &SExp = b.borrow();
            produce_body(opts.clone(), result_vec, prog, indent + 2, &BodyForm::Quoted(borrowed_a.clone()));
            produce_body(opts, result_vec, prog, indent + 2, &BodyForm::Quoted(borrowed_b.clone()));
            result_vec.push(format!("{}  )", do_indent(indent)));
        },
        BodyForm::Quoted(SExp::Nil(_)) => {
            result_vec.push(format!("{}(cvt unit)", do_indent(indent)));
        },
        BodyForm::Quoted(_) => {
            result_vec.push(format!("{}(cvt Atom)", do_indent(indent)));
        },
        BodyForm::Value(SExp::Nil(_)) => {
            result_vec.push(format!("{}(cvt unit)", do_indent(indent)));
        },
        BodyForm::Value(SExp::Cons(_,_,_)) => {
            result_vec.push(format!("{}(cvt Pair)", do_indent(indent)));
        },
        BodyForm::Value(SExp::Atom(_,n)) => {
            result_vec.push(format!("{}{}", do_indent(indent), decode_string(&n)));
        },
        BodyForm::Value(_) => {
            result_vec.push(format!("{}(cvt Atom)", do_indent(indent)));
        }
    }
}

fn collect_args_inner(args: &mut Vec<(Number, Vec<u8>)>, path: Number, mask: Number, val: Rc<SExp>) {
    let next_mask = mask.clone() * 2_u32.to_bigint().unwrap();

    match val.borrow() {
        SExp::Atom(_,n) => {
            args.push((path | mask, n.clone()));
        },
        SExp::Cons(_,a,b) => {
            let right_path = path.clone() | next_mask.clone();
            collect_args_inner(args, path, next_mask.clone(), a.clone());
            collect_args_inner(args, right_path, next_mask.clone(), b.clone());
        },
        _ => { }
    }
}

fn collect_args(sexp: Rc<SExp>) -> Vec<(Number, Vec<u8>)> {
    let mut collection = Vec::new();
    collect_args_inner(&mut collection, bi_zero(), bi_one(), sexp);
    return collection;
}

fn choose_path(target_path: Number, mask: Number, expression: String) -> String {
    "@@@@".to_string()
}

// Produce a checkable purescript program from our chialisp.
// Between prefix and suffix, we can add function definitions for our
// chialisp functions, ending in __chia__main.
pub fn chialisp_to_purescript(opts: Rc<dyn CompilerOpts>, prog: &CompileForm) -> String {
    let mut result_vec = Vec::new();
    // Spill constants
    for h in prog.helpers.iter() {
        if let HelperForm::Defconstant(_, name, val, ty) = h.borrow() {
            result_vec.push(format!("{} = do", decode_string(&name)));
            produce_body(opts.clone(), &mut result_vec, prog, 2, val);
        }
    }

    // Spill functions
    for h in prog.helpers.iter() {
        if let HelperForm::Defun(_, _, _, defargs, defbody, ty) = h.borrow() {
            let mut result_vec = Vec::new();
            let name = decode_string(&h.name());
            result_vec.push(format!("{} args = do", name));

            let args = collect_args(defargs.clone());
            if !args.is_empty() {
                for (path, a) in args.iter() {
                    result_vec.push(format!("  {} <- {}", decode_string(&a), choose_path(path.clone(), bi_one(), "args".to_string())));
                }
            }
            produce_body(opts.clone(), &mut result_vec, prog, 2, defbody.borrow());
        }
    }

    // Write out main
    result_vec.push("chia_main args = do".to_string());
    produce_body(opts, &mut result_vec, prog, 2, prog.exp.borrow());

    let prefix_str: &String = &PURESCRIPT_PREFIX;
    eprintln!("{}", prefix_str);
    for line in result_vec.iter() {
        eprintln!("{}", line);
    }
    let suffix_str: &String = &PURESCRIPT_SUFFIX;
    eprintln!("{}", suffix_str);

    todo!();
}

#[test]
fn test_basic_purescript_typing_from_chialisp() {
    let mut rng = ChaCha8Rng::from_entropy();
    let prog: FuzzProgram = rng.gen();
    let serialized = prog.to_sexp();
    eprintln!("-- program {}", serialized);
    let opts = Rc::new(DefaultCompilerOpts::new("*random*"));
    let parsed = frontend(opts.clone(), vec![Rc::new(serialized)]).unwrap();
    let program = chialisp_to_purescript(opts, &parsed);
    eprintln!("program {}", program);
}
