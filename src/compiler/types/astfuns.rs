// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::comptypes::{CompileErr, HelperForm, BodyForm};

use crate::compiler::types::ast;

fn tunit<A>() -> Type<A> { TUnit }
fn tvar<A>(s: String) -> Type<A> { TVar(TypeVar(s)) }
fn exists<A>(s: String) -> Type<A> ( TExists(TypeVar(s)) }
fn tforall<A>(s: String) -> Polytype { TForall(TypeVar(s)) }
fn funarrow<A>(t1: Type<A>, t2: Type<A>) -> Type<A> { TFun(t1,t2) }

fn tforalls(types: Vec<TVar>, pt_: Polytype) -> Polytype {
    let mut pt = pt_;
    for t in types.iter().rev() {
        pt = TForall(t,pt);
    }
    pt
}

fn monotype<A>(typ: Type<A>) -> Option<Monotype> {
    match typ {
        TUnit => Some(TUnit),
        TVar(v) => Some(TVar(v)),
        TForall(_,_) => Nothing,
        TExists(v) => Some(TExists(v)),
        TFun(t1,t2) => {
            monotype(t2).and_then(|t2m| {
                monotype(t1).map(|t1m| {
                    TFun(t1m,t2m)
                })
            })
        }
    }
}

fn polytype<A>(typ: Type<A>) -> Polytype {
    match typ {
        TUnit => TUnit,
        TVar(v) => TVar(v.clone()),
        TForall(v,t) => TForall(v.clone(),t.clone()),
        TExists(v) => TExists(v.clone()),
        TFun(t1,t2) => TFun(polytype(t1),polytype(t2))
    }
}

fn freeTVars<A>(typ: Type<A>) -> HashSet<TVar> {
    let mut res = HashSet::new();
    match typ {
        TUnit => res,
        TVar(v) => {
            res.insert(v.clone());
            res
        },
        TForall(v,t) => {
            res = freeTVars(t);
            res.remove(v);
            res
        },
        TExists(v) => {
            res.insert(v.clone());
            res
        },
        TFun(t1,t2) => {
            freeTVars(t1).union(freeTVars(t2))
        }
    }
}

fn typeSubst<A>(tprime: Type<A>, v: TVar, typ: Type<A>) -> Type<A> {
    match typ {
        TUnit => TUnit,
        TVar(vprime) => {
            if vprime == v {
                tprime
            } else {
                TVar(vprime)
            }
        },
        TForall(vprime,t) => {
            if vprime == v {
                TForall(vprime, t)
            } else {
                TForall(vprime, typeSubst(tprime, v, t))
            }
        },
        TExists(vprime) => {
            if vprime == v {
                tprime
            } else {
                TExists(vprime)
            }
        },
        TFun(t1,t2) => {
            TFun(typeSubst(tprime,v,t1), typeSubst(tprime, v, t2))
        }
    }
}

fn typeSubsts<A>(substs: Vec<(Type<A>, TVar)>, t_: Type<A>) -> Type<A> {
    let mut t = t_;
    for type_tv in substs.iter().rev() {
        t = typeSubst(type_tv.0, type_tv.1, t);
    }
    t
}

// Monoid, Semigroup
