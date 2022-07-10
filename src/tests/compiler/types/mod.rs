use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::{
    parse_expr_sexp,
    parse_type_sexp,
    standard_type_context
};
use crate::compiler::types::ast::{TypeVar, Type};
use crate::compiler::types::theory::{TypeTheory};

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

fn flatten_exists<const A: usize>(t: &Type<A>, held: &mut HashMap<TypeVar, TypeVar>, n: &mut usize) -> Type<A> {
    match t {
        Type::TUnit(l) => Type::TUnit(l.clone()),
        Type::TAny(l) => Type::TAny(l.clone()),
        Type::TAtom(l) => Type::TAtom(l.clone()),
        Type::TVar(v) => Type::TVar(v.clone()),
        Type::TExists(v) => {
            Type::TExists(resolve_test_var(held, n, v))
        },
        Type::TForall(v,t) => {
            Type::TForall(resolve_test_var(held, n, v), Rc::new(flatten_exists(t.borrow(), held, n)))
        },
        Type::TFun(t1,t2) => {
            Type::TFun(
                Rc::new(flatten_exists(t1.borrow(), held, n)),
                Rc::new(flatten_exists(t2.borrow(), held, n))
            )
        },
        Type::TNullable(t) => {
            Type::TNullable(Rc::new(flatten_exists(t.borrow(), held, n)))
        },
        Type::TPair(t1,t2) => {
            Type::TPair(
                Rc::new(flatten_exists(t1.borrow(), held, n)),
                Rc::new(flatten_exists(t2.borrow(), held, n))
            )
        }
    }
}

fn check_expression_against_type(
    e: &str,
    t: &str,
    flatten: bool
) {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let tloc = Srcloc::start(&"*type*".to_string());
    let esexp = parse_sexp(eloc, &e.to_string()).unwrap();
    let tsexp = parse_sexp(tloc, &t.to_string()).unwrap();
    let eid = parse_expr_sexp(esexp[0].clone()).unwrap();
    let expected = parse_type_sexp(tsexp[0].clone()).unwrap();
    let (polytype, context) =
        standard_type_context().typesynth(&eid).expect("should type check");
    let mut fcount: usize = 0;
    let mut held = HashMap::new();
    let usetype =
        if flatten {
            flatten_exists(&polytype, &mut held, &mut fcount)
        } else {
            polytype
        };
    assert_eq!(expected, usetype);
}

fn check_expression_type_fails(e: &str) {
    let eloc = Srcloc::start(&"*expr*".to_string());
    let esexp = parse_sexp(eloc, &e.to_string()).unwrap();
    let eid = parse_expr_sexp(esexp[0].clone()).unwrap();
    let res = standard_type_context().typesynth(&eid);
    assert_eq!(res.is_err(), true);
}

#[test]
fn test_simple_type_id_lambda_with_annotation() {
    check_expression_against_type(
        "((lambda x x) : (forall t (t -> t)))",
        "(forall t (t -> t))",
        false
    );
}

#[test]
fn test_atom_type() {
    check_expression_against_type(
        "1",
        "Atom",
        false
    );
}

#[test]
fn test_unit_type() {
    check_expression_against_type(
        "()",
        "Unit",
        false
    );
}

#[test]
fn test_atom_is_not_function() {
    check_expression_type_fails(
        "(1 : (forall x (x -> x)))"
    );
}

#[test]
fn test_nullable_atom() {
    check_expression_against_type(
        "(some 1)",
        "(Nullable Atom)",
        false
    );
}

#[test]
fn test_lambda_type_with_constant_result() {
    check_expression_against_type(
        "(lambda x (some 1))",
        "((exists t0) -> (Nullable Atom))",
        true
    );
}

#[test]
fn test_lambda_type_with_constant_unit_output() {
    check_expression_against_type(
        "(lambda x ())",
        "((exists t0) -> Unit)",
        true
    );
}

#[test]
fn test_lambda_type_with_constant_unit_output_as_nullable() {
    check_expression_against_type(
        "((lambda x ()) : (forall t (t -> (Nullable Atom))))",
        "(forall t (t -> (Nullable Atom)))",
        false
    );
}

#[test]
fn test_lambda_identity_type_with_annotation() {
    check_expression_against_type(
        "((lambda x x) : (forall t (t -> t)))",
        "(forall t (t -> t))",
        false
    );
}

#[test]
fn test_lambda_identity_no_annotation() {
    check_expression_against_type(
        "(lambda x x)",
        "(forall t0 ((exists t1) -> (exists t1)))",
        true
    );
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
        true
    );
}

/*
#[test]
fn test_lambda_nullable_no_annotation() {
    check_expression_against_type(
        "(lambda x (some x))",
        "((exists t0) -> (Nullable (exists t0)))",
        true
    );
}
*/
