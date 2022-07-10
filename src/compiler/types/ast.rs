// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi
// Pseudo AST for typing
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use crate::compiler::srcloc::{HasLoc, Srcloc};
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

impl Eq for Var {
}

impl Hash for Var {
    fn hash<H>(&self, h: &mut H) where H: Hasher { self.0.hash(h) }
}

impl HasLoc for Var {
    fn loc(&self) -> Srcloc { self.1.clone() }
}

#[derive(Clone, Debug)]
pub struct TypeVar(pub String, pub Srcloc);

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}

impl Eq for TypeVar {
}

impl Hash for TypeVar {
    fn hash<H>(&self, h: &mut H) where H: Hasher {
        self.0.hash(h);
    }
}

impl HasLoc for TypeVar {
    fn loc(&self) -> Srcloc { self.1.clone() }
}

#[derive(Clone, Debug)]
pub enum Expr {
    EVar(Var),
    EUnit(Srcloc),
    EAbs(Var,Rc<Expr>),
    EApp(Rc<Expr>,Rc<Expr>),
    EAnno(Rc<Expr>,Polytype),
    ELit(Srcloc,Number),
    ESome(Rc<Expr>),
    ECons(Rc<Expr>,Rc<Expr>)
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::EVar(v1), Expr::EVar(v2)) => v1 == v2,
            (Expr::EUnit(_), Expr::EUnit(_)) => true,
            (Expr::EAbs(v1,x1), Expr::EAbs(v2,x2)) => v1 == v2 && x1 == x2,
            (Expr::EApp(ea1,eb1), Expr::EApp(ea2, eb2)) => ea1 == ea2 && eb1 == eb2,
            (Expr::EAnno(x1,t1), Expr::EAnno(x2,t2)) => x1 == x2 && t1 == t2,
            (Expr::ESome(e1), Expr::ESome(e2)) => e1 == e2,
            (Expr::ECons(e1,e2), Expr::ECons(e3,e4)) => e1 == e3 && e2 == e4,
            _ => false
        }
    }
}

impl Eq for Expr { }

impl HasLoc for Expr {
    fn loc(&self) -> Srcloc {
        match self {
            Expr::EVar(v) => v.loc(),
            Expr::EUnit(l) => l.clone(),
            Expr::EAbs(v,e) => e.loc(),
            Expr::EApp(e1,e2) => e1.loc().ext(&e2.loc()),
            Expr::EAnno(e,t) => e.loc().ext(&t.loc()),
            Expr::ELit(l,_) => l.clone(),
            Expr::ESome(e) => e.loc(),
            Expr::ECons(e1,e2) => e1.loc().ext(&e2.loc())
        }
    }
}

#[derive(Clone, Debug)]
pub enum Type<const T: usize> {
    TUnit(Srcloc),
    TAny(Srcloc),
    TAtom(Srcloc),
    TVar(TypeVar),
    TExists(TypeVar),
    TForall(TypeVar, Rc<Type<TYPE_POLY>>),
    TFun(Rc<Type<T>>,Rc<Type<T>>),
    TNullable(Rc<Type<T>>),
    TPair(Rc<Type<T>>,Rc<Type<T>>),
}

impl<const T: usize> PartialEq for Type<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::TUnit(_), Type::TUnit(_)) => true,
            (Type::TAny(_), Type::TAny(_)) => true,
            (Type::TAtom(_), Type::TAtom(_)) => true,
            (Type::TVar(v1), Type::TVar(v2)) => v1 == v2,
            (Type::TExists(v1), Type::TExists(v2)) => v1 == v2,
            (Type::TForall(v1,t1), Type::TForall(v2,t2)) => v1 == v2 && t1 == t2,
            (Type::TFun(ta1,tb1), Type::TFun(ta2,tb2)) => ta1 == ta2 && tb1 == tb2,
            (Type::TNullable(t1), Type::TNullable(t2)) => t1 == t2,
            (Type::TPair(f1,r1), Type::TPair(f2,r2)) => f1 == f2 && r1 == r2,
            _ => false
        }
    }
}

impl<const T: usize> Eq for Type<T> { }

impl<const T: usize> HasLoc for Type<T> {
    fn loc(&self) -> Srcloc {
        match self {
            Type::TUnit(l) => l.clone(),
            Type::TAny(l) => l.clone(),
            Type::TAtom(l) => l.clone(),
            Type::TVar(v) => v.loc(),
            Type::TExists(v) => v.loc(),
            Type::TForall(v, t) => v.loc().ext(&t.loc()),
            Type::TFun(t1, t2) => t1.loc().ext(&t2.loc()),
            Type::TNullable(t) => t.loc(),
            Type::TPair(f,r) => f.loc().ext(&r.loc()),
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
    CExistsSolved(TypeVar,Monotype),
    CMarker(TypeVar)
}

impl<const K: usize> HasLoc for ContextElim<K> {
    fn loc(&self) -> Srcloc {
        match self {
            ContextElim::CForall(v) => v.loc(),
            ContextElim::CVar(v,t) => v.loc().ext(&t.loc()),
            ContextElim::CExists(t) => t.loc(),
            ContextElim::CExistsSolved(t,m) => t.loc().ext(&m.loc()),
            ContextElim::CMarker(v) => v.loc()
        }
    }
}

#[derive(Clone, Debug)]
pub struct GContext<const A: usize>(pub Vec<ContextElim<A>>);
type CompleteContext = GContext<CONTEXT_COMPLETE>;
pub type Context = GContext<CONTEXT_INCOMPLETE>;

impl<const A: usize> GContext<A> {
    pub fn snoc(&self, elem: ContextElim<A>) -> GContext<A> {
        let mut newvec = self.0.clone();
        newvec.insert(0, elem);
        GContext(newvec)
    }

    pub fn appends(&self, elems_: Vec<ContextElim<A>>) -> GContext<A> {
        let mut newvec = self.0.clone();
        let mut elems = elems_;
        newvec.append(&mut elems);
        GContext(newvec)
    }

    pub fn new(elems: Vec<ContextElim<A>>) -> GContext<A> {
        GContext(elems)
    }

    pub fn drop_marker(&self, m: ContextElim<A>) -> GContext<A> {
        self.0.iter().position(|e| *e == m).map(|idx| {
            GContext(self.0[idx+1..].iter().map(|x| x.clone()).collect())
        }).unwrap_or_else(|| {
            GContext(Vec::new())
        })
    }

    pub fn break_marker(&self, m: ContextElim<A>) -> (GContext<A>, GContext<A>) {
        self.0.iter().position(|e| *e == m).map(|idx| {
            ( GContext(self.0[idx+1..].iter().map(|x| x.clone()).collect())
            , GContext(self.0[..idx].iter().map(|x| x.clone()).collect())
            )
        }).unwrap_or_else(|| {
            ( GContext(self.0.clone())
            , GContext(Vec::new())
            )
        })
    }
}
