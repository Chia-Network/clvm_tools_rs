use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::{parse_expr_sexp, parse_type_sexp, TheoryToSExp};
use crate::compiler::typechia::standard_type_context;
use crate::compiler::types::ast::{Context, ContextElim, Monotype, Polytype, Type, TypeVar};
use crate::compiler::types::theory::TypeTheory;

fn resolve_test_var(held: &mut HashMap<TypeVar, TypeVar>, n: &mut usize, v: &TypeVar) -> TypeVar {
    if let Some(prev) = held.get(v) {
        prev.clone()
    } else {
        let this_var = n.clone();
        *n += 1;
        let tv = TypeVar(format!("t{}", this_var), v.loc());
        held.insert(v.clone(), tv.clone());
        tv
    }
}

pub fn flatten_exists<const A: usize>(
    t: &Type<A>,
    held: &mut HashMap<TypeVar, TypeVar>,
    n: &mut usize,
) -> Type<A> {
    match t {
        Type::TUnit(_) => t.clone(),
        Type::TAny(_) => t.clone(),
        Type::TAtom(_, _) => t.clone(),
        Type::TVar(v) => Type::TVar(v.clone()),
        Type::TExists(v) => Type::TExists(resolve_test_var(held, n, v)),
        Type::TForall(v, t) => Type::TForall(
            resolve_test_var(held, n, v),
            Rc::new(flatten_exists(t.borrow(), held, n)),
        ),
        Type::TFun(t1, t2) => Type::TFun(
            Rc::new(flatten_exists(t1.borrow(), held, n)),
            Rc::new(flatten_exists(t2.borrow(), held, n)),
        ),
        Type::TNullable(t) => Type::TNullable(Rc::new(flatten_exists(t.borrow(), held, n))),
        Type::TExec(t) => Type::TExec(Rc::new(flatten_exists(t.borrow(), held, n))),
        Type::TPair(t1, t2) => Type::TPair(
            Rc::new(flatten_exists(t1.borrow(), held, n)),
            Rc::new(flatten_exists(t2.borrow(), held, n)),
        ),
        Type::TAbs(v, t) => Type::TAbs(v.clone(), Rc::new(flatten_exists(t.borrow(), held, n))),
        Type::TApp(t1, t2) => Type::TApp(
            Rc::new(flatten_exists(t1.borrow(), held, n)),
            Rc::new(flatten_exists(t2.borrow(), held, n)),
        ),
    }
}

pub fn check_expression_against_type_with_context(
    incontext: &Context,
    e: &str,
    t: &str,
    flatten: bool,
) {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let tloc = Srcloc::start(&"*type*".to_string());
    let esexp = parse_sexp(eloc, e.bytes()).unwrap();
    let tsexp = parse_sexp(tloc, t.bytes()).unwrap();
    let eid = parse_expr_sexp(esexp[0].clone()).unwrap();
    let expected: Polytype = parse_type_sexp(tsexp[0].clone()).unwrap();
    let (polytype, context) = incontext.typesynth(&eid).expect("should type check");
    let mut fcount: usize = 0;
    let mut held = HashMap::new();
    let usetype = if flatten {
        flatten_exists(&context.reify(&polytype, None), &mut held, &mut fcount)
    } else {
        context.reify(&polytype, None)
    };
    assert_eq!(
        expected.to_sexp().to_string(),
        usetype.to_sexp().to_string()
    );
}

pub fn check_increase_specificity(incontext: &Context, t1: &str, t2: &str, result: &str) {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let tloc = Srcloc::start(&"*type*".to_string());
    let t1sexp = parse_sexp(eloc, t1.bytes()).unwrap();
    let t2sexp = parse_sexp(tloc, t2.bytes()).unwrap();
    let t1type: Monotype = parse_type_sexp(t1sexp[0].clone()).unwrap();
    let t2type: Monotype = parse_type_sexp(t2sexp[0].clone()).unwrap();
    let (usetype, _) = incontext
        .increase_type_specificity(&t1type, &t2type)
        .expect("should widen");
    assert_eq!(usetype.to_sexp().to_string(), result);
}

pub fn check_subtype(incontext: &Context, t1: &str, t2: &str) -> Result<Box<Context>, CompileErr> {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let tloc = Srcloc::start(&"*type*".to_string());
    let t1sexp = parse_sexp(eloc, t1.bytes())?;
    let t2sexp = parse_sexp(tloc, t2.bytes())?;
    let t1type: Polytype = parse_type_sexp(t1sexp[0].clone())?;
    let t2type: Polytype = parse_type_sexp(t2sexp[0].clone())?;
    incontext.subtype(&t1type, &t2type)
}

fn check_expression_against_type(e: &str, t: &str, flatten: bool) {
    check_expression_against_type_with_context(&standard_type_context(), e, t, flatten)
}

fn check_expression_type_fails(e: &str) {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let esexp = parse_sexp(eloc, e.bytes()).unwrap();
    let eid = parse_expr_sexp(esexp[0].clone()).unwrap();
    let res = standard_type_context().typesynth(&eid);
    assert_eq!(res.is_err(), true);
}

#[test]
fn test_simple_type_id_lambda_with_annotation() {
    check_expression_against_type(
        "((lambda x x) : (forall t (t -> t)))",
        "(forall t (t -> t))",
        false,
    );
}

#[test]
fn test_atom_type() {
    check_expression_against_type("1", "Atom", false);
}

#[test]
fn test_unit_type() {
    check_expression_against_type("()", "Unit", false);
}

#[test]
fn test_atom_is_not_function() {
    check_expression_type_fails("(1 : (forall x (x -> x)))");
}

#[test]
fn test_nullable_atom() {
    check_expression_against_type("(some 1)", "(Nullable Atom)", false);
}

#[test]
fn test_lambda_type_with_constant_result() {
    check_expression_against_type(
        "(lambda x (some 1))",
        "((exists t0) -> (Nullable Atom))",
        true,
    );
}

#[test]
fn test_lambda_type_with_constant_unit_output() {
    check_expression_against_type("(lambda x ())", "((exists t0) -> ())", true);
}

#[test]
fn test_lambda_type_with_constant_unit_output_as_nullable() {
    check_expression_against_type(
        "((lambda x ()) : (forall t (t -> (Nullable Atom))))",
        "(forall t (t -> (Nullable Atom)))",
        false,
    );
}

#[test]
fn test_lambda_identity_type_with_annotation() {
    check_expression_against_type(
        "((lambda x x) : (forall t (t -> t)))",
        "(forall t (t -> t))",
        false,
    );
}

#[test]
fn test_lambda_identity_no_annotation() {
    check_expression_against_type("(lambda x x)", "((exists t0) -> (exists t0))", true);
}

#[test]
fn test_lambda_nullable_annotation() {
    check_expression_against_type(
        "((lambda x (some x)) : (forall t (t -> (Nullable t))))",
        "(forall t (t -> (Nullable t)))",
        false,
    );
}

#[test]
fn test_lambda_nullable_const_no_annotation() {
    check_expression_against_type(
        "(lambda x (some 1))",
        "((exists t0) -> (Nullable Atom))",
        true,
    );
}

#[test]
fn test_lambda_nullable_no_annotation() {
    check_expression_against_type(
        "(lambda x (some x))",
        "((exists t0) -> (Nullable (exists t0)))",
        true,
    );
}

#[test]
fn test_lambda_nullable_apply() {
    check_expression_against_type("((lambda x (some x)) 1)", "(Nullable Atom)", false);
}

#[test]
fn test_lambda_pair_apply() {
    check_expression_against_type("((lambda x (cons x ())) 1)", "(Pair Atom ())", false);
}

#[test]
fn test_first_of_pair() {
    check_expression_against_type("(f^ (cons 1 ()))", "Atom", false);
}

#[test]
fn test_rest_of_pair() {
    check_expression_against_type("(r^ (cons 1 ()))", "()", false);
}

#[test]
fn test_type_exec_with_anno() {
    check_expression_against_type(
        "((lambda x ((a^ x) 1)) : ((Exec (Atom -> Atom)) -> Atom))",
        "((Exec (Atom -> Atom)) -> Atom)",
        false,
    );
}

#[test]
fn test_list_unit_with_anno() {
    check_expression_against_type("(() : (List Atom))", "(List Atom)", false);
}

#[test]
fn test_list_content_with_anno() {
    check_expression_against_type(
        "((cons 1 (cons 2 (cons 3 ()))) : (List Atom))",
        "(List Atom)",
        false,
    );
}

#[test]
fn test_sized_atom() {
    check_expression_against_type("(sha256 (cons 3 ()))", "Atom32", false);
}

#[test]
fn test_nullable_simple_1() {
    check_expression_against_type("(() : (Nullable Atom))", "(Nullable Atom)", false);
}

#[test]
fn test_nullable_simple_2() {
    check_increase_specificity(
        &standard_type_context(),
        "Atom",
        "(Nullable Atom)",
        "(Nullable Atom)",
    );
}

#[test]
fn test_subtype_1() {
    check_subtype(
        &standard_type_context(),
        "(forall t (t -> Atom))",
        "(forall t (t -> (Nullable Atom)))",
    )
    .unwrap();
}

#[test]
fn test_subtype_2() {
    let loc = Srcloc::start("*type*");
    let typevar_u = TypeVar("u".to_string(), loc.clone());
    let type_context = standard_type_context().snoc(ContextElim::CExists(typevar_u.clone()));
    let t1: Polytype = Type::TExists(typevar_u.clone());
    let tc2 = check_subtype(&type_context, "(exists u)", "(exists u)").unwrap();
    assert!(tc2.typewf(&t1));
}

#[test]
fn test_subtype_3() {
    let loc = Srcloc::start("*type*");
    let typevar_u = TypeVar("u".to_string(), loc.clone());
    let type_context = standard_type_context()
        .snoc(ContextElim::CForall(typevar_u.clone()))
        .snoc(ContextElim::CExistsSolved(
            typevar_u.clone(),
            Type::TAtom(loc.clone(), None),
        ));
    let tc2 = check_subtype(&type_context, "u", "(exists u)");
    assert!(tc2.is_err());
}

#[test]
fn test_subtype_4() {
    let loc = Srcloc::start("*type*");
    let typevar_u = TypeVar("u".to_string(), loc.clone());
    let type_context = standard_type_context()
        .snoc(ContextElim::CForall(typevar_u.clone()))
        .snoc(ContextElim::CExistsSolved(
            typevar_u.clone(),
            Type::TAtom(loc.clone(), None),
        ));
    let tc2 = check_subtype(&type_context, "(exists u)", "u");
    assert!(tc2.is_err());
}

#[test]
fn test_subtype_5() {
    let loc = Srcloc::start("*type*");
    let typevar_u = TypeVar("u".to_string(), loc.clone());
    let typevar_v = TypeVar("v".to_string(), loc.clone());
    let type_context = standard_type_context()
        .snoc(ContextElim::CExists(typevar_u.clone()))
        .snoc(ContextElim::CExistsSolved(
            typevar_v.clone(),
            Type::TAtom(loc.clone(), None),
        ));
    // Verify good result.
    check_subtype(&type_context, "(exists u)", "(Exec v)").expect("should typecheck");
}

#[test]
fn test_subtype_6() {
    let loc = Srcloc::start("*type*");
    let typevar_u = TypeVar("u".to_string(), loc.clone());
    let type_context = standard_type_context().snoc(ContextElim::CExists(typevar_u.clone()));
    // Verify good result.
    let res = check_subtype(
        &type_context,
        "(exists u)",
        "(forall t (Exec (Nullable t)))",
    )
    .expect("should typecheck");
}

#[test]
fn test_reify_equal_types() {
    let loc = Srcloc::start("*type*");
    let parsedt1 = parse_sexp(loc.clone(), "Atom".bytes()).expect("should parse");
    let t1: Polytype = parse_type_sexp(parsedt1[0].clone()).expect("should work");
    let t2: Polytype = t1.clone();
    assert_eq!(standard_type_context().reify(&t1, Some(t2)), t1);
}
