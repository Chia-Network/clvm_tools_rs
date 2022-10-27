use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::{parse_expr_sexp, parse_type_sexp, TheoryToSExp};
use crate::compiler::typechia::standard_type_context;
use crate::compiler::types::ast::{Context, Polytype, Type, TypeVar};
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
