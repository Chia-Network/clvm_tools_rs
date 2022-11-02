use num_bigint::ToBigInt;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::comptypes::{BodyForm, CompileForm, CompilerOpts, HelperForm};
use crate::compiler::evaluate::dequote;
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::{SExp, decode_string};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::typechia::{standard_type_context, type_level_macro_transform};
use crate::util::Number;

lazy_static! {
    pub static ref PURESCRIPT_PREFIX: String = indoc!{"
module Main where

import Prelude
import Data.Maybe
import Data.Tuple
import Effect (Effect)
import Effect.Console (log)

data ChiaPrim = ChiaAtom String | ChiaCons ChiaPrim ChiaPrim

{- These are type level representations, but the actual data is a chia value
 - This simulates the conversion of the program from typed to untyped.
 -}
data Nil = Nil ChiaPrim
data Atom = Atom ChiaPrim
data Atom32 = Atom32 ChiaPrim
data Nullable a = Nullable ChiaPrim
data Pair a b = Pair ChiaPrim
data Exec x = Exec ChiaPrim
data Any = Any ChiaPrim
data ChiaFun a b = ChiaFun ChiaPrim

-- Monad for chia
data ChiaOutcome t = ChiaResult t | ChiaException ChiaPrim

instance chiaOutcomeFunctor :: Functor ChiaOutcome where
  map :: forall a b. (a -> b) -> ChiaOutcome a -> ChiaOutcome b
  map f (ChiaResult v) = ChiaResult $ (f v)
  map _ (ChiaException e) = ChiaException e

instance chiaOutcomeApplicative :: Applicative ChiaOutcome where
  pure :: forall a. a -> ChiaOutcome a
  pure x = ChiaResult x

instance chiaOutcomeApply :: Apply ChiaOutcome where
  apply :: forall a b. ChiaOutcome (a -> b) -> ChiaOutcome a -> ChiaOutcome b
  apply (ChiaResult f) (ChiaResult a) = ChiaResult $ f a
  apply (ChiaException e) _ = ChiaException e
  apply _ (ChiaException e) = ChiaException e

instance chiaOutcomeBind :: Bind ChiaOutcome where
  bind :: forall m b a. m a -> (a -> m b) -> m b
  bind (ChiaResult v) f = f v
  bind (ChiaException e) _ = ChiaException e

class HasValue t where
  getValue :: t -> ChiaPrim

instance chiaPrimHasValue :: HasValue ChiaPrim where
  getValue p = p

instance chiaNilHasValue :: HasValue Nil where
  getValue (Nil v) = v

instance chiaAtomHasValue :: HasValue Atom where
  getValue (Atom v) = v

instance chiaAtom32HasValue :: HasValue Atom32 where
  getValue (Atom32 v) = v

instance chiaNullableHasValue :: HasValue (Nullable a) where
  getValue (Nullable v) = v

instance chiaPairHasValue :: HasValue (Pair a b) where
  getValue (Pair v) = v

instance chiaExecHasValue :: HasValue (Exec x) where
  getValue (Exec v) = v

instance chiaAnyHasValue :: HasValue Any where
  getValue (Any v) = v

instance chiaFunHasValue :: HasValue (ChiaFun a b) where
  getValue (ChiaFun v) = v

class FromValue t where
  fromValue :: ChiaPrim -> t

instance chiaPrimFromValue :: FromValue ChiaPrim where
  fromValue p = p

instance chiaNilFromValue :: FromValue Nil where
  fromValue p = Nil p

instance chiaAtomFromValue :: FromValue Atom where
  fromValue p = Atom p

instance chiaAtom32FromValue :: FromValue Atom32 where
  fromValue p = Atom32 p

instance chiaNullableFromValue :: FromValue (Nullable a) where
  fromValue p = Nullable p

instance chiaPairFromValue :: FromValue (Pair a b) where
  fromValue p = Pair p

instance chiaExecFromValue :: FromValue (Exec x) where
  fromValue p = Exec p

instance chiaAnyFromValue :: FromValue Any where
  fromValue p = Any p

instance chiaFunFromValue :: FromValue (ChiaFun a b) where
  fromValue p = ChiaFun p

-- The following constraints are used to implement the basic subtype ladder.
class Convert x y where
  cvt :: x -> y

instance cvtNilNil :: Convert Nil Nil where
  cvt (Nil x) = Nil x

instance cvtAnyNil :: Convert Any Nil where
  cvt (Any x) = Nil x

instance cvtNullableXNil :: Convert (Nullable x) Nil where
  cvt (Nullable x) = Nil x

instance cvtXNullableX :: (HasValue x) => Convert x (Nullable x) where
  cvt x = Nullable (getValue x)

instance cvtNilAny :: Convert Nil Any where
  cvt (Nil x) = Any x

instance cvtAtomAny :: Convert Atom Any where
  cvt (Atom x) = Any x

instance cvtAtom32Any :: Convert Atom32 Any where
  cvt (Atom32 x) = Any x

instance cvtNullableXAny :: (Convert x Any) => Convert (Nullable x) Any where
  cvt (Nullable x) = Any x

instance cvtPairABAny :: (Convert a Any, Convert b Any) => Convert (Pair a b) Any where
  cvt (Pair x) = Any x

instance cvtAnyAny :: Convert Any Any where
  cvt (Any x) = Any x

instance cvtAtomAtom :: Convert Atom Atom where
  cvt (Atom x) = Atom x

instance cvtAtom32Atom :: Convert Atom32 Atom where
  cvt (Atom32 x) = Atom x

instance cvtNilAtom :: Convert Nil Atom where
  cvt (Nil x) = Atom x

instance cvtAnyAtom :: Convert Any Atom where
  cvt (Any x) = Atom x

instance cvtAtom32Atom32 :: Convert Atom32 Atom32 where
  cvt (Atom32 x) = Atom32 x

instance cvtAnyAtom32 :: Convert Any Atom32 where
  cvt (Any x) = Atom32 x

instance cvtPairABPairXY :: (Convert a x, Convert b y) => Convert (Pair a b) (Pair x y) where
  cvt (Pair x) = Pair x

instance cvtAnyPairAB :: (Convert Any a, Convert Any b) => Convert Any (Pair a b) where
  cvt (Any x) = Pair x

instance cvtAnyExecX :: (Convert Any x) => Convert Any (Exec x) where
  cvt (Any x) = Exec x

instance cvtAnyChiaFunAB :: Convert Any (ChiaFun a b) where
  cvt (Any x) = ChiaFun x

class ListOfAtoms x where
  unroll :: x -> Maybe (Tuple Atom x)

instance listOfAtomsNil :: ListOfAtoms Nil where
  unroll (Nil x) = Nothing

instance listOfAtomsNullable :: (ListOfAtoms x, FromValue x) => ListOfAtoms (Nullable x) where
  unroll (Nullable v) = unroll (fromValue v)

instance listOfAtomsPair :: (FromValue b, ListOfAtoms b) => ListOfAtoms (Pair a b) where
  unroll (Pair (ChiaCons x y)) = Just (Tuple (fromValue x) (fromValue y))
  unroll (Pair _) = Nothing

sha256 :: forall x. (ListOfAtoms x) => x -> ChiaOutcome Atom32
sha256 _ = ChiaResult $ Atom32 (ChiaAtom \"\")

multiply :: forall x. (ListOfAtoms x) => x -> ChiaOutcome Atom
multiply _ = ChiaResult $ Atom (ChiaAtom \"\")

subtract :: Pair Atom (Pair Atom Unit) -> ChiaOutcome Atom
subtract _ = ChiaResult $ Atom (ChiaAtom \"\")

truthy :: ChiaPrim -> Boolean
truthy _ = false

f :: forall f0 r0. (FromValue f0) => (Pair (Pair f0 r0) Nil) -> ChiaOutcome f0
f (Pair (ChiaCons (ChiaCons a b) _)) = ChiaResult (fromValue a)
f x = ChiaException (getValue x)

r :: forall f0 r0. (FromValue r0) => (Pair (Pair f0 r0) Nil) -> ChiaOutcome r0
r (Pair (ChiaCons (ChiaCons a b) _)) = ChiaResult (fromValue b)
r x = ChiaException (getValue x)

a :: forall a b c. (HasValue (Exec (ChiaFun a b))) => (FromValue b) => (Pair (Exec (ChiaFun a b)) (Pair b c)) -> ChiaOutcome b
a x = pure $ fromValue (getValue x)

i :: forall c a b q x.  (FromValue a) => (FromValue b) => (Convert a x) => (Convert b x) => (Convert c Any) => (Pair c (Pair a (Pair b q))) -> ChiaOutcome x
i (Pair (ChiaCons c (ChiaCons a (ChiaCons b _)))) =
  let
    a_converted :: a
    a_converted = fromValue a

    b_converted :: b
    b_converted = fromValue b
  in
  pure $ if truthy c then cvt a_converted else cvt b_converted
i x = ChiaException (getValue x)

"}.to_string();

    pub static ref PURESCRIPT_SUFFIX: String = indoc!{"

main :: Effect Unit
main = do
  log \"compiled\"
"}.to_string();

    pub static ref PRIM_TO_CALL_MAP: HashMap<Vec<u8>, Vec<u8>> = {
        let mut op_dict = HashMap::new();

        op_dict.insert(b"-".to_vec(), b"subtract".to_vec());
        op_dict.insert(b"*".to_vec(), b"multiply".to_vec());
        op_dict.insert(b"sha256".to_vec(), b"sha256".to_vec());
        op_dict.insert(b"c".to_vec(), b"c".to_vec());
        op_dict.insert(b"a".to_vec(), b"a".to_vec());
        op_dict.insert(b"i".to_vec(), b"i".to_vec());

        op_dict
    };
}

fn un_dollar(s: &[u8]) -> Vec<u8> {
    s.iter().map(|ch| if *ch == b'$' { b'_' } else { *ch }).collect()
}

fn do_indent(indent: usize) -> String {
    let mut s = Vec::new();
    for _ in 0..indent {
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
    result_vec.push(format!("-- produce_body {}", body.to_sexp()));
    match body {
        BodyForm::Let(_, _, bindings, letbody) => {
            result_vec.push(format!("{}do", do_indent(indent)));
            for b in bindings.iter() {
                result_vec.push(format!("{}{} <-", do_indent(indent + 2), decode_string(&un_dollar(&b.name))));
                produce_body(opts.clone(), result_vec, prog, indent + 4, b.body.borrow());
            }
            produce_body(opts.clone(), result_vec, prog, indent + 2, letbody.borrow());
        },
        BodyForm::Call(cl, elts) => {
            if elts.is_empty() {
                result_vec.push(format!("{}pure unit", do_indent(indent)));
                return;
            }

            if let BodyForm::Value(SExp::Atom(_,n)) = elts[0].borrow() {
                if n == b"com" {
                    // Compile code in this context and emit it.
                    // The type of a "com" expression where the expression
                    // returns x is is Exec (Any -> x)
                    let exp_serialized = elts[1].to_sexp();
                    result_vec.push(format!("-- com {}", exp_serialized));
                    let compiled =
                        frontend(opts.clone(), vec![exp_serialized]).unwrap();
                    produce_body(
                        opts.clone(),
                        result_vec,
                        prog,
                        indent + 2,
                        compiled.exp.borrow()
                    );
                } else if let Some(callable) = find_callable(prog, n) {
                    if let HelperForm::Defun(_, defname, _, _, _, _) = callable {
                        result_vec.push(format!("{}do", do_indent(indent)));
                        for (i,a) in elts.iter().skip(1).enumerate() {
                            result_vec.push(format!("{}farg_{} <- getValue <$> do", do_indent(indent + 2), i));
                            produce_body(opts.clone(), result_vec, prog, indent + 4, a);
                        }
                        result_vec.push(format!("{}cvt <$> {} (Pair $ ", do_indent(indent + 2), decode_string(&defname)));
                        for (i,_) in elts.iter().skip(1).enumerate() {
                            result_vec.push(format!("{}ChiaCons (getValue farg_{}) $", do_indent(indent + 4), i));
                        }
                        result_vec.push(format!("{}ChiaAtom \"\"", do_indent(indent + 4)));
                        result_vec.push(format!("{})", do_indent(indent + 2)));
                    } else if let HelperForm::Defmacro(loc, name, macargs, macbody) = callable {
                        // expand macro as in type synthesis.
                        let expanded_expression = type_level_macro_transform(
                            prog,
                            macbody.clone(),
                            loc.clone(),
                            &elts
                        ).unwrap();
                        let unquoted_expr = dequote(loc.clone(), expanded_expression).unwrap();
                        let reparsed = frontend(opts.clone(), vec![unquoted_expr]).unwrap();
                        produce_body(opts, result_vec, prog, indent, &reparsed.exp);
                    } else {
                        todo!("{}", body.to_sexp())
                    }
                } else {
                    todo!("{}", body.to_sexp())
                }
            } else {
                todo!("{}", body.to_sexp())
            }
        },
        BodyForm::Quoted(SExp::Cons(_,a,b)) => {
            result_vec.push(format!("{}pure $ (cvt $ Pair $ ChiaAtom \"\")", do_indent(indent)));
        },
        BodyForm::Quoted(SExp::Nil(_)) => {
            result_vec.push(format!("{}pure $ (cvt $ Nil $ ChiaAtom \"\")", do_indent(indent)));
        },
        BodyForm::Quoted(_) => {
            result_vec.push(format!("{}pure $ (cvt $ Atom $ ChiaAtom \"\")", do_indent(indent)));
        },
        BodyForm::Value(SExp::Nil(_)) => {
            result_vec.push(format!("{}pure $ (cvt $ Nil $ ChiaAtom \"\")", do_indent(indent)));
        },
        BodyForm::Value(SExp::Cons(_,_,_)) => {
            result_vec.push(format!("{}pure $ (cvt $ Pair $ ChiaAtom \"\")", do_indent(indent)));
        },
        BodyForm::Value(SExp::Atom(_,n)) => {
            if n == b"@" {
                result_vec.push(format!("{}pure $ {}- @ -{} (cvt $ Nil $ ChiaAtom \"\")", do_indent(indent), "{", "}"));
            } else {
                result_vec.push(format!("{}pure $ (cvt {})", do_indent(indent), decode_string(&un_dollar(&n))));
            }
        },
        BodyForm::Value(_) => {
            result_vec.push(format!("{}pure $ (cvt $ Atom $ ChiaAtom \"\")", do_indent(indent)));
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
            let right_path = path.clone() | mask.clone();
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

fn choose_path(target_path: Number, expression: String) -> String {
    if target_path == bi_one() {
        expression
    } else {
        let apply_function =
            if target_path.clone() & bi_one() == bi_one() {
                "r"
            } else {
                "f"
            };
        choose_path(
            target_path >> 1,
            format!(
                "{} =<< {}",
                apply_function,
                expression
            )
        )
    }
}

// Produce a checkable purescript program from our chialisp.
// Between prefix and suffix, we can add function definitions for our
// chialisp functions, ending in __chia__main.
pub fn chialisp_to_purescript(opts: Rc<dyn CompilerOpts>, prog: &CompileForm) -> Result<String, String> {
    let context = standard_type_context();
    let (_, type_of_program) = context.compute_program_type(opts.clone(), prog).map_err(|e| format!("{}: {}", e.0, e.1))?;

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
        result_vec.push(format!("-- produce helper {}", h.to_sexp()));
        if let HelperForm::Defun(_, _, _, defargs, defbody, ty) = h.borrow() {
            let name = decode_string(&h.name());
            result_vec.push(format!("{} args = do", name));

            let args = collect_args(defargs.clone());
            result_vec.push("-- produce args".to_string());
            if !args.is_empty() {
                for (path, a) in args.iter() {
                    result_vec.push(format!("  {} <- {}", decode_string(&un_dollar(&a)), choose_path(path.clone(), "pure (cvt args)".to_string())));
                }
            }

            result_vec.push(format!("-- produce body for {}", name));
            produce_body(opts.clone(), &mut result_vec, prog, 2, defbody.borrow());
        }
    }

    // Write out main
    result_vec.push("chia_main args = do".to_string());

    let args = collect_args(prog.args.clone());
    result_vec.push("-- produce args".to_string());
    if !args.is_empty() {
        for (path, a) in args.iter() {
            result_vec.push(format!("  {} <- {}", decode_string(&a), choose_path(path.clone(), "pure (cvt args)".to_string())));
        }
    }
    produce_body(opts, &mut result_vec, prog, 2, prog.exp.borrow());

    let mut result_bytes = Vec::new();
    let prefix_str: &String = &PURESCRIPT_PREFIX;
    result_bytes.append(&mut prefix_str.as_bytes().to_vec());
    for line in result_vec.iter() {
        result_bytes.push(b'\n');
        result_bytes.append(&mut line.as_bytes().to_vec());
    }
    result_bytes.push(b'\n');
    let suffix_str: &String = &PURESCRIPT_SUFFIX;
    result_bytes.append(&mut suffix_str.as_bytes().to_vec());

    Ok(decode_string(&result_bytes))
}
