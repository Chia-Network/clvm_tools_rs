// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi
// Pseudo AST for typing
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use log::debug;

use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::util::Number;

pub const CONTEXT_COMPLETE: usize = 0;
pub const CONTEXT_INCOMPLETE: usize = 1;

pub const TYPE_MONO: usize = 0;
pub const TYPE_POLY: usize = 1;

#[derive(Clone, Debug)]
pub struct Var(pub String, pub Srcloc);

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Var {}

impl Hash for Var {
    fn hash<H>(&self, h: &mut H)
    where
        H: Hasher,
    {
        self.0.hash(h)
    }
}

impl HasLoc for Var {
    fn loc(&self) -> Srcloc {
        self.1.clone()
    }
}

#[derive(Clone, Debug)]
pub struct TypeVar(pub String, pub Srcloc);

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TypeVar {}

impl Hash for TypeVar {
    fn hash<H>(&self, h: &mut H)
    where
        H: Hasher,
    {
        self.0.hash(h);
    }
}

impl HasLoc for TypeVar {
    fn loc(&self) -> Srcloc {
        self.1.clone()
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    EVar(Var),
    EUnit(Srcloc),
    EAbs(Var, Rc<Expr>),
    EApp(Rc<Expr>, Rc<Expr>),
    EAnno(Rc<Expr>, Polytype),
    ELit(Srcloc, Number),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::EVar(v1), Expr::EVar(v2)) => v1 == v2,
            (Expr::EUnit(_), Expr::EUnit(_)) => true,
            (Expr::EAbs(v1, x1), Expr::EAbs(v2, x2)) => v1 == v2 && x1 == x2,
            (Expr::EApp(ea1, eb1), Expr::EApp(ea2, eb2)) => ea1 == ea2 && eb1 == eb2,
            (Expr::EAnno(x1, t1), Expr::EAnno(x2, t2)) => x1 == x2 && t1 == t2,
            _ => false,
        }
    }
}

impl Eq for Expr {}

impl HasLoc for Expr {
    fn loc(&self) -> Srcloc {
        match self {
            Expr::EVar(v) => v.loc(),
            Expr::EUnit(l) => l.clone(),
            Expr::EAbs(_, e) => e.loc(),
            Expr::EApp(e1, e2) => e1.loc().ext(&e2.loc()),
            Expr::EAnno(e, t) => e.loc().ext(&t.loc()),
            Expr::ELit(l, _) => l.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Type<const T: usize> {
    TUnit(Srcloc),
    TAny(Srcloc),
    TAtom(Srcloc, Option<Number>),
    TVar(TypeVar),
    TExists(TypeVar),
    TForall(TypeVar, Rc<Type<TYPE_POLY>>),
    TFun(Rc<Type<T>>, Rc<Type<T>>),
    TNullable(Rc<Type<T>>),
    TPair(Rc<Type<T>>, Rc<Type<T>>),
    TExec(Rc<Type<T>>),
    TApp(Rc<Type<T>>, Rc<Type<T>>),
    TAbs(TypeVar, Rc<Type<T>>),
}

impl<const T: usize> PartialEq for Type<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::TUnit(_), Type::TUnit(_)) => true,
            (Type::TAny(_), Type::TAny(_)) => true,
            (Type::TAtom(_, m), Type::TAtom(_, n)) => m == n,
            (Type::TVar(v1), Type::TVar(v2)) => v1 == v2,
            (Type::TExists(v1), Type::TExists(v2)) => v1 == v2,
            (Type::TForall(v1, t1), Type::TForall(v2, t2)) => v1 == v2 && t1 == t2,
            (Type::TFun(ta1, tb1), Type::TFun(ta2, tb2)) => ta1 == ta2 && tb1 == tb2,
            (Type::TNullable(t1), Type::TNullable(t2)) => t1 == t2,
            (Type::TPair(f1, r1), Type::TPair(f2, r2)) => f1 == f2 && r1 == r2,
            (Type::TExec(a1), Type::TExec(a2)) => a1 == a2,
            (Type::TAbs(v1, a1), Type::TAbs(v2, a2)) => v1 == v2 && a1 == a2,
            (Type::TApp(a1, b1), Type::TApp(a2, b2)) => a1 == a2 && b1 == b2,
            _ => false,
        }
    }
}

impl<const T: usize> Hash for Type<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.to_sexp().hash(state)
    }
}

impl<const T: usize> Eq for Type<T> {}

impl<const T: usize> HasLoc for Type<T> {
    fn loc(&self) -> Srcloc {
        match self {
            Type::TUnit(l) => l.clone(),
            Type::TAny(l) => l.clone(),
            Type::TAtom(l, _) => l.clone(),
            Type::TVar(v) => v.loc(),
            Type::TExists(v) => v.loc(),
            Type::TForall(v, t) => v.loc().ext(&t.loc()),
            Type::TFun(t1, t2) => t1.loc().ext(&t2.loc()),
            Type::TNullable(t) => t.loc(),
            Type::TPair(f, r) => f.loc().ext(&r.loc()),
            Type::TExec(t1) => t1.loc(),
            Type::TAbs(v, t) => v.loc().ext(&t.loc()),
            Type::TApp(t1, t2) => t1.loc().ext(&t2.loc()),
        }
    }
}

pub type Polytype = Type<TYPE_POLY>;
pub type Monotype = Type<TYPE_MONO>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ContextElim<const K: usize> {
    CForall(TypeVar),
    CVar(Var, Polytype),
    CExists(TypeVar),
    CExistsSolved(TypeVar, Monotype),
    CMarker(TypeVar),
}

impl<const K: usize> HasLoc for ContextElim<K> {
    fn loc(&self) -> Srcloc {
        match self {
            ContextElim::CForall(v) => v.loc(),
            ContextElim::CVar(v, t) => v.loc().ext(&t.loc()),
            ContextElim::CExists(t) => t.loc(),
            ContextElim::CExistsSolved(t, m) => t.loc().ext(&m.loc()),
            ContextElim::CMarker(v) => v.loc(),
        }
    }
}

pub trait ExtractContext<const A: usize> {
    fn extract(self) -> GContext<A>;
}

impl<const A: usize> ExtractContext<A> for GContext<A> {
    fn extract(self) -> GContext<A> {
        self
    }
}

impl<const A: usize> ExtractContext<A> for Box<GContext<A>> {
    fn extract(self) -> GContext<A> {
        let borrowed: &GContext<A> = self.borrow();
        borrowed.clone()
    }
}

#[derive(Clone, Debug)]
pub struct GContext<const A: usize>(pub Vec<ContextElim<A>>);
pub type Context = GContext<CONTEXT_INCOMPLETE>;

fn instantiates_tvar<const A: usize>(m: &TypeVar, c: &ContextElim<A>) -> bool {
    match c {
        ContextElim::CExists(v) => v == m,
        ContextElim::CExistsSolved(v, _) => v == m,
        _ => false,
    }
}

impl<const A: usize> GContext<A> {
    pub fn snoc(&self, elem: ContextElim<A>) -> GContext<A> {
        let mut newvec = self.0.clone();
        newvec.insert(0, elem);
        GContext(newvec)
    }

    pub fn appends(&self, elems_: Vec<ContextElim<A>>) -> GContext<A> {
        let mut elems = elems_;
        let mut scopy = self.0.clone();
        elems.append(&mut scopy);
        GContext(elems)
    }

    pub fn new(elems: Vec<ContextElim<A>>) -> GContext<A> {
        GContext(elems)
    }

    pub fn drop_context(&self, m: ContextElim<A>) -> GContext<A> {
        self.0
            .iter()
            .position(|e| *e == m)
            .map(|idx| GContext(self.0[idx + 1..].to_vec()))
            .unwrap_or_else(|| GContext(self.0.clone()))
    }

    pub fn inspect_context(&self, m: &TypeVar) -> (GContext<A>, GContext<A>) {
        self.0
            .iter()
            .position(|e| instantiates_tvar(m, e))
            .map(|idx| {
                (
                    GContext(self.0[idx + 1..].to_vec()),
                    GContext(self.0[..idx].to_vec()),
                )
            })
            .unwrap_or_else(|| (GContext(self.0.clone()), GContext(Vec::new())))
    }

    pub fn break_marker<E, X, F>(
        &self,
        m: ContextElim<A>,
        f: F,
    ) -> Result<(GContext<A>, GContext<A>), E>
    where
        F: FnOnce(GContext<A>) -> Result<X, E>,
        X: ExtractContext<A>,
    {
        let marked = self.appends(vec![m.clone()]);
        let res: GContext<A> = f(marked).map(|x| x.extract())?;
        Ok(res
            .0
            .iter()
            .position(|e| *e == m)
            .map(|idx| {
                let res = (
                    GContext(res.0[..idx].to_vec()),
                    GContext(res.0[idx + 1..].to_vec()),
                );
                debug!(
                    "break_marker {} {} from {}",
                    m.to_sexp().to_string(),
                    res.0.to_sexp().to_string(),
                    res.1.to_sexp().to_string()
                );
                res
            })
            .unwrap_or_else(|| (GContext(Vec::new()), GContext(res.0.clone()))))
    }
}
