use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{
    CompileErr
};
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::typechia::{
    context_from_args_and_type,
    standard_type_context
};
use crate::compiler::types::ast::{
    Polytype,
    Type,
    TypeVar
};
use crate::compiler::types::theory::TypeTheory;
use crate::tests::compiler::types::types::{
    check_expression_against_type_with_context,
    flatten_exists
};

#[test]
fn test_chialisp_context_from_args_and_type_empty() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Nil(loc.clone())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "()",
        "Unit",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_atom_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any_pair() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_arg_with_list_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TApp(
            Rc::new(Type::TAtom(loc.clone(), None)),
            Rc::new(Type::TVar(TypeVar("List".to_string(), loc.clone())))
        ),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "(Atom List)",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_with_pair_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TPair(
            Rc::new(Type::TAtom(loc.clone(), None)),
            Rc::new(Type::TUnit(loc.clone()))
        ),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "Atom",
        false
    );
}

fn test_chialisp_program_typecheck(s: &str, flatten: bool) -> Result<Polytype, CompileErr> {
    let testname = "*test*".to_string();
    let loc = Srcloc::start(&testname);
    let context = standard_type_context();
    let opts = DefaultCompilerOpts::new(&testname);
    let pre_forms = parse_sexp(loc.clone(), &s.to_string()).
        map_err(|e| CompileErr(e.0, e.1))?;
    let compileform = frontend(Rc::new(opts), pre_forms)?;
    println!("compileform ty {:?}", compileform.ty);
    let mut fcount: usize = 0;
    let mut held = HashMap::new();
    let target_type = context.typecheck_chialisp_program(&compileform)?;
    if flatten {
        Ok(flatten_exists(&context.reify(&target_type), &mut held, &mut fcount))
    } else {
        Ok(context.reify(&target_type))
    }
}

#[test]
fn test_chialisp_program_returning_unit_no_anno() {
    let ty = test_chialisp_program_typecheck(
        "(mod () ())",
        false
    ).expect("should type check");
    assert_eq!(ty, Type::TAny(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_unit_annotation() {
    let ty = test_chialisp_program_typecheck(
        "(mod () : (Unit -> Unit) ())",
        false
    ).expect("should type check");
    assert_eq!(ty, Type::TUnit(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_one_atom_annotation() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X) : ((Pair Atom Unit) -> Atom) X)",
        false
    ).expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_chialisp_program_doing_cons() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X) : (forall t0 ((Pair t0 Unit) -> (Pair t0 Unit))) (c X ()))",
        true
    ).expect("should type check");
    assert_eq!(
        ty,
        Type::TPair(
            Rc::new(Type::TVar(TypeVar("t0".to_string(), ty.loc()))),
            Rc::new(Type::TUnit(ty.loc()))
        )
    );
}

#[test]
fn test_chialisp_program_doing_plus() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X Y) : ((Pair Atom (Pair Atom Unit)) -> Atom) (+ X Y))",
        true
    ).expect("should type check");
    assert_eq!(
        ty,
        Type::TAtom(ty.loc(), None)
    );
}

#[test]
fn test_chialisp_defun_sha256() {
    let ty = test_chialisp_program_typecheck(
        indoc!{"
(mod (X) : ((Pair Atom Unit) -> (Atom 32))
  (defun F (X) : ((Pair Atom Unit) -> (Atom 32))
    (sha256 1 X)
    )

  (F X)
  )"
        },
        true
    ).expect("should type check");
    assert_eq!(
        ty,
        Type::TAtom(ty.loc(), Some(32))
    );
}

#[test]
fn test_chialisp_defun_sha256_bad() {
    let ty = test_chialisp_program_typecheck(
        indoc!{"
(mod (X) : ((Pair Atom Unit) -> (Atom 32))
  (defun F (X) : ((Pair (Atom 32) Unit) -> (Atom 32))
    (sha256 1 X)
    )

  (F X)
  )"
        },
        false
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_defun_sha256_good() {
    let ty = test_chialisp_program_typecheck(
        indoc!{"
(mod (X) : ((Pair (Atom 32) Unit) -> (Atom 32))
  (defun F (X) : ((Pair (Atom 32) Unit) -> (Atom 32))
    (sha256 1 X)
    )

  (F X)
  )"
        },
        false
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_chialisp_with_arg_type_smoke_test() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : Atom)) -> Atom (+ X 1))",
        false
    ).expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_chialisp_with_arg_type_first_should_not_check() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : Atom)) -> Atom (f X))",
        false
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_with_arg_type_first_should_check() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : (Pair Atom Unit))) -> Atom (f X))",
        false
    );
    println!("ty {:?}", ty);
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_chialisp_with_arg_type_doesnt_check_not_atom32() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : (Pair Atom Unit))) -> (Atom 32) (+ 1 X))",
        false
    );
    println!("ty {:?}", ty);
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_with_arg_type_doesnt_checks_atom32() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : (Pair Atom Unit))) -> (Atom 32) (sha256 1 X))",
        false
    );
    println!("ty {:?}", ty);
    assert_eq!(ty.is_err(), false);
}
