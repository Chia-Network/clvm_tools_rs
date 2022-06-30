// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi
// Pseudo AST for typing
use std::rc::Rc;
use crate::compiler::srcloc::{HasLoc, Srcloc};

pub const CONTEXT_COMPLETE: usize = 0;
pub const CONTEXT_INCOMPLETE: usize = 1;

pub const TYPE_MONO: usize = 0;
pub const TYPE_POLY: usize = 1;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Var(pub String);
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct TypeVar(pub String);

impl HasLoc for TypeVar {
    fn loc(&self) -> Srcloc { todo!("typevar") }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    EVar(Var),
    EUnit,
    EAbs(Var,Rc<Expr>),
    EApp(Rc<Expr>,Rc<Expr>),
    EAnno(Rc<Expr>,Polytype)
}

impl HasLoc for Expr {
    fn loc(&self) -> Srcloc { todo!("todo") }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type<const T: usize> {
    TUnit,
    TVar(TypeVar),
    TExists(TypeVar),
    TForall(TypeVar, Rc<Type<TYPE_POLY>>),
    TFun(Rc<Type<T>>,Rc<Type<T>>)
}

impl<const T: usize> HasLoc for Type<T> {
    fn loc(&self) -> Srcloc { todo!("todo") }
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
    fn loc(&self) -> Srcloc { todo!("todo") }
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

    pub fn dropMarker(&self, m: ContextElim<A>) -> GContext<A> {
        self.0.iter().position(|e| *e == m).map(|idx| {
            GContext(self.0[idx+1..].iter().map(|x| x.clone()).collect())
        }).unwrap_or_else(|| {
            GContext(Vec::new())
        })
    }

    pub fn breakMarker(&self, m: ContextElim<A>) -> (GContext<A>, GContext<A>) {
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
