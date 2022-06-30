// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::comptypes::{CompileErr, HelperForm, BodyForm};

use crate::compiler::types::ast::{TYPE_POLY, Monotype, Polytype, TypeVar, Type};

fn tunit<const A: usize>() -> Type<A> { Type::TUnit }
fn tvar<const A: usize>(s: String) -> Type<A> { Type::TVar(TypeVar(s)) }
fn exists<const A: usize>(s: String) -> Type<A> { Type::TExists(TypeVar(s)) }

fn tforalls(types: Vec<TypeVar>, pt_: Polytype) -> Polytype {
    let mut pt = pt_;
    for t in types.iter().rev() {
        pt = Type::TForall(t.clone(),Rc::new(pt.clone()));
    }
    pt
}

pub fn monotype<const A: usize>(typ: &Type<A>) -> Option<Monotype> {
    match typ {
        Type::TUnit => Some(Type::TUnit),
        Type::TVar(v) => Some(Type::TVar(v.clone())),
        Type::TForall(_,_) => None,
        Type::TExists(v) => Some(Type::TExists(v.clone())),
        Type::TFun(t1,t2) => {
            monotype(t2.borrow()).and_then(|t2m| {
                monotype(t1).map(|t1m| {
                    Type::TFun(Rc::new(t1m.clone()),Rc::new(t2m.clone()))
                })
            })
        }
    }
}

pub fn polytype<const A: usize>(typ: &Type<A>) -> Polytype {
    match typ {
        Type::TUnit => Type::TUnit,
        Type::TVar(v) => Type::TVar(v.clone()),
        Type::TForall(v,t) => Type::TForall(v.clone(),t.clone()),
        Type::TExists(v) => Type::TExists(v.clone()),
        Type::TFun(t1,t2) => Type::TFun(Rc::new(polytype(t1)),Rc::new(polytype(t2)))
    }
}

pub fn free_tvars<const A: usize>(typ: &Type<A>) -> HashSet<TypeVar> {
    let mut res = HashSet::new();
    match typ {
        Type::TUnit => res,
        Type::TVar(v) => {
            res.insert(v.clone());
            res
        },
        Type::TForall(v,t) => {
            res = free_tvars(t.borrow());
            res.remove(v);
            res
        },
        Type::TExists(v) => {
            res.insert(v.clone());
            res
        },
        Type::TFun(t1,t2) => {
            free_tvars(t1).union(&free_tvars(t2.borrow())).map(|x| x.clone()).collect()
        }
    }
}

pub fn typeSubst<const A: usize>(tprime: &Type<A>, v: &TypeVar, typ: &Type<A>) -> Type<A> {
    match typ {
        Type::TUnit => Type::TUnit,
        Type::TVar(vprime) => {
            if *vprime == *v {
                tprime.clone()
            } else {
                Type::TVar(vprime.clone())
            }
        },
        Type::TForall(vprime,t) => {
            if *vprime == *v {
                Type::TForall(vprime.clone(), t.clone())
            } else {
                let t_borrowed: &Type<TYPE_POLY> = t.borrow();
                Type::TForall(vprime.clone(), Rc::new(typeSubst(&polytype(tprime), v, t_borrowed)))
            }
        },
        Type::TExists(vprime) => {
            if *vprime == *v {
                tprime.clone()
            } else {
                Type::TExists(vprime.clone())
            }
        },
        Type::TFun(t1,t2) => {
            Type::TFun(Rc::new(typeSubst(tprime,v,t1)), Rc::new(typeSubst(tprime,v,t2)))
        }
    }
}

pub fn typeSubsts<const A: usize>(substs: Vec<(Type<A>, TypeVar)>, t_: Type<A>) -> Type<A> {
    let mut t = t_;
    for type_tv in substs.iter().rev() {
        t = typeSubst(&type_tv.0, &type_tv.1, &t.clone());
    }
    t
}

// Monoid, Semigroup
