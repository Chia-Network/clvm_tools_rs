// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use crate::compiler::types::ast::{Monotype, Polytype, Type, TypeVar, TYPE_POLY};

pub fn tforalls(types: Vec<TypeVar>, pt_: Polytype) -> Polytype {
    let mut pt = pt_;
    for t in types.iter().rev() {
        pt = Type::TForall(t.clone(), Rc::new(pt.clone()));
    }
    pt
}

pub fn monotype<const A: usize>(typ: &Type<A>) -> Option<Monotype> {
    match typ {
        Type::TUnit(l) => Some(Type::TUnit(l.clone())),
        Type::TAny(l) => Some(Type::TAny(l.clone())),
        Type::TAtom(l, m) => Some(Type::TAtom(l.clone(), m.clone())),
        Type::TVar(v) => Some(Type::TVar(v.clone())),
        Type::TForall(_, _) => None,
        Type::TExists(v) => Some(Type::TExists(v.clone())),
        Type::TNullable(t) => monotype(t.borrow()).map(|tm| Type::TNullable(Rc::new(tm))),
        Type::TExec(t) => monotype(t.borrow()).map(|tm| Type::TExec(Rc::new(tm))),
        Type::TFun(t1, t2) => monotype(t2.borrow())
            .and_then(|t2m| monotype(t1).map(|t1m| Type::TFun(Rc::new(t1m), Rc::new(t2m.clone())))),
        Type::TPair(a, b) => monotype(a.borrow())
            .and_then(|am| monotype(b).map(|bm| Type::TPair(Rc::new(am.clone()), Rc::new(bm)))),
        Type::TAbs(v, t) => monotype(t.borrow()).map(|tm| Type::TAbs(v.clone(), Rc::new(tm))),
        Type::TApp(a, b) => monotype(a.borrow())
            .and_then(|am| monotype(b).map(|bm| Type::TApp(Rc::new(am), Rc::new(bm)))),
    }
}

pub fn polytype<const A: usize>(typ: &Type<A>) -> Polytype {
    match typ {
        Type::TUnit(l) => Type::TUnit(l.clone()),
        Type::TAny(l) => Type::TAny(l.clone()),
        Type::TAtom(l, m) => Type::TAtom(l.clone(), m.clone()),
        Type::TVar(v) => Type::TVar(v.clone()),
        Type::TForall(v, t) => Type::TForall(v.clone(), t.clone()),
        Type::TExists(v) => Type::TExists(v.clone()),
        Type::TNullable(t) => Type::TNullable(Rc::new(polytype(t))),
        Type::TExec(t) => Type::TExec(Rc::new(polytype(t))),
        Type::TFun(t1, t2) => Type::TFun(Rc::new(polytype(t1)), Rc::new(polytype(t2))),
        Type::TPair(t1, t2) => Type::TPair(Rc::new(polytype(t1)), Rc::new(polytype(t2))),
        Type::TAbs(v, t) => Type::TAbs(v.clone(), Rc::new(polytype(t))),
        Type::TApp(t1, t2) => Type::TApp(Rc::new(polytype(t1)), Rc::new(polytype(t2))),
    }
}

pub fn free_tvars<const A: usize>(typ: &Type<A>) -> HashSet<TypeVar> {
    let mut res = HashSet::new();
    match typ {
        Type::TUnit(_) => res,
        Type::TAny(_) => res,
        Type::TAtom(_, _) => res,
        Type::TVar(v) => {
            res.insert(v.clone());
            res
        }
        Type::TForall(v, t) => {
            res = free_tvars(t.borrow());
            res.remove(v);
            res
        }
        Type::TExists(v) => {
            res.insert(v.clone());
            res
        }
        Type::TNullable(t) => free_tvars(t.borrow()),
        Type::TExec(t) => free_tvars(t.borrow()),
        Type::TFun(t1, t2) => free_tvars(t1)
            .union(&free_tvars(t2.borrow()))
            .cloned()
            .collect(),
        Type::TPair(t1, t2) => free_tvars(t1)
            .union(&free_tvars(t2.borrow()))
            .cloned()
            .collect(),
        Type::TAbs(v, t) => {
            let mut res = free_tvars(t.borrow());
            res.remove(v);
            res
        }
        Type::TApp(t1, t2) => free_tvars(t1)
            .union(&free_tvars(t2.borrow()))
            .cloned()
            .collect(),
    }
}

pub fn type_subst<const A: usize>(tprime: &Type<A>, v: &TypeVar, typ: &Type<A>) -> Type<A> {
    match typ {
        Type::TUnit(_) => typ.clone(),
        Type::TAny(_) => typ.clone(),
        Type::TAtom(_, _) => typ.clone(),
        Type::TVar(vprime) => {
            if *vprime == *v {
                tprime.clone()
            } else {
                Type::TVar(vprime.clone())
            }
        }
        Type::TForall(vprime, t) => {
            if *vprime == *v {
                Type::TForall(vprime.clone(), t.clone())
            } else {
                let t_borrowed: &Type<TYPE_POLY> = t.borrow();
                Type::TForall(
                    vprime.clone(),
                    Rc::new(type_subst(&polytype(tprime), v, t_borrowed)),
                )
            }
        }
        Type::TExists(vprime) => {
            if *vprime == *v {
                tprime.clone()
            } else {
                Type::TExists(vprime.clone())
            }
        }
        Type::TNullable(t) => {
            let t_borrowed: &Type<A> = t.borrow();
            Type::TNullable(Rc::new(type_subst(tprime, v, t_borrowed)))
        }
        Type::TExec(t) => {
            let t_borrowed: &Type<A> = t.borrow();
            Type::TExec(Rc::new(type_subst(tprime, v, t_borrowed)))
        }
        Type::TFun(t1, t2) => Type::TFun(
            Rc::new(type_subst(tprime, v, t1)),
            Rc::new(type_subst(tprime, v, t2)),
        ),
        Type::TPair(t1, t2) => Type::TPair(
            Rc::new(type_subst(tprime, v, t1)),
            Rc::new(type_subst(tprime, v, t2)),
        ),
        Type::TAbs(v, t) => Type::TAbs(v.clone(), Rc::new(type_subst(tprime, v, t))),
        Type::TApp(t1, t2) => Type::TApp(
            Rc::new(type_subst(tprime, v, t1)),
            Rc::new(type_subst(tprime, v, t2)),
        ),
    }
}

pub fn type_substs<const A: usize>(substs: Vec<(Type<A>, TypeVar)>, t_: Type<A>) -> Type<A> {
    let mut t = t_;
    for type_tv in substs.iter().rev() {
        t = type_subst(&type_tv.0, &type_tv.1, &t.clone());
    }
    t
}

pub fn unrecurse<const A: usize>(
    target: &TypeVar,
    applied_type: &Type<A>,
    applied_to: &Type<A>,
    in_definition: &Type<A>,
) -> Option<Type<A>> {
    match in_definition {
        Type::TApp(ta, tb) => {
            let ta_borrowed: &Type<A> = ta.borrow();
            let tb_borrowed: &Type<A> = tb.borrow();
            let tamatch = ta_borrowed == applied_type;
            let tbmatch = tb_borrowed == applied_to;
            if tamatch && tbmatch {
                let tv = Type::TExists(target.clone());
                Some(tv)
            } else {
                unrecurse(target, applied_type, applied_to, ta.borrow()).and_then(|replaced_in_a| {
                    unrecurse(target, applied_type, applied_to, tb.borrow()).map(|replaced_in_b| {
                        Type::TApp(Rc::new(replaced_in_a), Rc::new(replaced_in_b))
                    })
                })
            }
        }
        Type::TForall(v, t) => unrecurse(
            target,
            &polytype(applied_type),
            &polytype(applied_to),
            &polytype(t),
        )
        .map(|replaced| Type::TForall(v.clone(), Rc::new(replaced))),
        Type::TAbs(v, t) => unrecurse(target, applied_type, applied_to, t.borrow())
            .map(|replaced| Type::TAbs(v.clone(), Rc::new(replaced))),
        Type::TNullable(t) => unrecurse(target, applied_type, applied_to, t.borrow())
            .map(|replaced| Type::TNullable(Rc::new(replaced))),
        Type::TPair(ta, tb) => {
            unrecurse(target, applied_type, applied_to, ta.borrow()).and_then(|replaced_in_a| {
                unrecurse(target, applied_type, applied_to, tb.borrow()).map(|replaced_in_b| {
                    Type::TPair(Rc::new(replaced_in_a), Rc::new(replaced_in_b))
                })
            })
        }
        Type::TExec(t) => unrecurse(target, applied_type, applied_to, t.borrow())
            .map(|replaced| Type::TExec(Rc::new(replaced))),
        Type::TFun(ta, tb) => {
            unrecurse(target, applied_type, applied_to, ta.borrow()).and_then(|replaced_in_a| {
                unrecurse(target, applied_type, applied_to, tb.borrow())
                    .map(|replaced_in_b| Type::TFun(Rc::new(replaced_in_a), Rc::new(replaced_in_b)))
            })
        }
        _ => Some(in_definition.clone()),
    }
}

// Monoid, Semigroup
