// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi
// Pseudo AST for typing
use crate::compiler::srcloc::{HasLoc, Srcloc};

pub struct Var(String);
pub struct TVar(String);

pub enum Expr {
    EVar(Var),
    EUnit,
    EAbs(Var,Rc<Expr>),
    EApp(Rc<Expr>,Rc<Expr>),
    EAnno(Rc<Expr>,Polytype)
};

impl HasLoc for Expr {
    pub fn loc(&self) -> Srcloc { todo!("todo") }
}

pub enum Type<T> {
    TUnit,
    TVar(TVar),
    TExists(TVar),
    TForall(TVar),
    TFun(Rc<Type<T>>,Rc<Type<T>>)
};

impl HasLoc Type<T> {
    pub fn loc(&self) -> Srcloc { todo!("todo") }
}

// Type level markers and runtime representations for parameterizing
// Polytype and Monotype.
pub enum TypeKind {
    MonoKind,
    PolyKind
};

pub struct Mono();
pub struct Poly();

pub struct Polytype(Type<Poly>);
pub struct Monotype(Type<Mono>);

pub enum ContextKind {
    Complete,
    Incomplete
}

pub struct ContextElimComplete();
pub struct ContextElimIncomplete();

pub enum ContextElim<K> {
    CForall(TVar),
    CVar(Var, Polytype),
    CExists(TVar,ContextElim<ContextElimIncomplete>),
    CExistsSolved(TVar,Monotype),
    CMarker(TVar)
}

impl HasLoc for ContextElim<K> {
    fn loc(&self) -> Srcloc { todo!("todo") }
}

struct GContext<A>(Vec<ContextElem<A>));
type CompleteContext = GContext<ContextElimComplete>;
type Context = GContext<ContextElimIncomplete>;

impl GContext<A> {
    pub fn snoc(&self, elem: ContextElem<A>) -> GContext<A> {
        let mut newvec = self.0.clone();
        newvec.insert(0, elem);
        GContext(newvec)
    }

    pub fn appends<A>(&self, elems_: Vec<ContextElem<A>>) -> GContext<A> {
        let mut newvec = self.0.clone();
        let mut elems = elems_;
        newvec.append(&mut elems);
        GContext(newvec)
    }

    pub fn new<A>(elems: Vec<ContextElem<A>>) -> GContext<A> {
        GContext(elems)
    }

    pub fn dropMarker<A>(&self, m: ContextElem<A>) -> GContext<A> {
        self.0.find(|e| e == m).map(|idx| {
            GContext(self.0[idx+1..].iter().map(|x| x.clone()).collect())
        }).unwrap_or_else(|| {
            GContext(Vec::new())
        })
    }

    pub fn breakMarker<A>(&self, m: ContextElem<A>) -> (GContext<A>, GContext<A>) {
        self.0.find(|e| e == m).map(|idx| {
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
