// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::rc::Rc;
use log::debug;

use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::comptypes::CompileErr;
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{
    CONTEXT_INCOMPLETE,
    Context,
    ContextElim,
    Expr,
    ExtractContext,
    GContext,
    Monotype,
    Polytype,
    TypeVar,
    Type,
    Var
};
use crate::compiler::types::astfuns::{polytype};

// | subst e' x e = [e'/x]e
pub fn subst(eprime: &Expr, x: Var, expr: &Expr) -> Expr {
    match expr {
        Expr::EVar(xprime) => {
            if *xprime == x {
                return eprime.clone();
            } else {
                return Expr::EVar(xprime.clone());
            }
        },

        Expr::EUnit(l) => Expr::EUnit(l.clone()),

        Expr::ELit(l,n) => Expr::ELit(l.clone(),n.clone()),

        Expr::EAbs(xprime, e) => {
            if *xprime == x {
                return Expr::EAbs(xprime.clone(), e.clone());
            } else {
                return Expr::EAbs(xprime.clone(), Rc::new(subst(eprime, x.clone(), e)));
            }
        },

        Expr::EApp(e1, e2) => Expr::EApp(Rc::new(subst(eprime, x.clone(), e1)), Rc::new(subst(eprime, x.clone(), e2))),

        Expr::EAnno(e, t) => Expr::EAnno(Rc::new(subst(eprime, x.clone(), e)), t.clone())
    }
}

fn existentials_aux<const K: usize>(ce: &ContextElim<K>) -> Option<&TypeVar> {
    match ce {
        ContextElim::CExists(alpha) => Some(alpha),
        ContextElim::CExistsSolved(alpha,_) => Some(alpha),
        _ => None
    }
}

pub trait HasElem {
    type Item;
    fn elem(&self, i: &<Self as HasElem>::Item) -> bool;
}

impl<X: Eq> HasElem for Vec<X> {
    type Item = X;
    fn elem(&self, i: &X) -> bool {
        !self.iter().position(|a| a == i).is_none()
    }
}

impl Context {
    // TODO: Convert these to iter
    pub fn existentials(&self) -> Vec<TypeVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let Some(r) = existentials_aux(gamma_elem) {
                res.push(r.clone());
            }
        }
        res
    }

    pub fn unsolved(&self) -> Vec<TypeVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let ContextElim::CExists(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    pub fn vars(&self) -> Vec<Var> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let ContextElim::CVar(x,_) = gamma_elem {
                res.push(x.clone());
            }
        }
        res
    }

    pub fn foralls(&self) -> Vec<TypeVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let ContextElim::CForall(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    pub fn markers(&self) -> Vec<TypeVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let ContextElim::CMarker(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    // Well-formedness of contexts
    // wf Gamma <=> Gamma ctx
    pub fn wf_(&self) -> bool {
        if self.0.is_empty() {
            return true;
        }

        let c = self.0[0].clone();
        let cs = self.0.iter().skip(1).map(|x| x.clone()).collect();
        // Do not use new_wf here... we're already checking well-formedness
        let gamma = Context::new(cs);

        match c {
            ContextElim::CForall(alpha) => !gamma.foralls().elem(&alpha),
            ContextElim::CVar(x,a) => !gamma.vars().elem(&x) && gamma.typewf(&a),
            ContextElim::CExists(alpha) => !gamma.existentials().elem(&alpha),
            ContextElim::CExistsSolved(alpha,tau) => !gamma.existentials().elem(&alpha) &&
                gamma.typewf(&tau),
            ContextElim::CMarker(alpha) => !gamma.markers().elem(&alpha) &&
                !gamma.existentials().elem(&alpha)
        }
    }

    pub fn wf(&self) -> bool {
        let well = self.wf_();
        debug!("wf {} => {}", self.to_sexp().to_string(), well);
        well
    }

    pub fn typewf<const A: usize>(&self, typ: &Type<A>) -> bool {
        match typ {
            Type::TVar(alpha) => self.foralls().elem(&alpha),
            Type::TUnit(_) => true,
            Type::TAny(_) => true,
            Type::TAtom(_) => true,
            Type::TNullable(t) => self.typewf(t.clone().borrow()),
            Type::TExec(t) => self.typewf(t.clone().borrow()),
            Type::TFun(a,b) => self.typewf(a.clone().borrow()) && self.typewf(b.clone().borrow()),
            Type::TPair(a,b) => self.typewf(a.clone().borrow()) && self.typewf(b.clone().borrow()),
            Type::TForall(alpha,a) => self.snoc_wf(ContextElim::CForall(alpha.clone())).typewf(a),
            Type::TExists(alpha) => self.existentials().elem(alpha),
        }
    }

    pub fn checkwf(&self, loc: Srcloc) -> Result<(), CompileErr> {
        if self.wf() {
            return Ok(());
        }


        Err(CompileErr(loc, format!("Malformed context: {}", self.to_sexp().to_string())))
    }

    pub fn checkwftype(&self, a: &Polytype) -> Result<(), CompileErr> {
        if self.typewf(a) {
            return self.checkwf(a.loc());
        }

        Err(CompileErr(a.loc(), format!("Malformed type: {} in {}", a.to_sexp().to_string(), self.to_sexp().to_string())))
    }

    pub fn find_solved(&self, v: &TypeVar) -> Option<Monotype> {
        for t in self.0.iter() {
            if let ContextElim::CExistsSolved(vprime,t) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn find_var_type(&self, v: &Var) -> Option<Polytype> {
        for t in self.0.iter() {
            if let ContextElim::CVar(vprime,t) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn solve(&self, alpha: &TypeVar, tau: &Monotype) -> Option<Context> {
        let (gamma_l, gamma_r) = self.inspect_context(&ContextElim::CExists(alpha.clone()));
        if gamma_l.typewf(&tau) {
            let mut gammaprime = gamma_l.0.clone();
            let mut gamma_r_copy = gamma_r.0.clone();
            gammaprime.push(ContextElim::CExistsSolved(alpha.clone(), tau.clone()));
            gammaprime.append(&mut gamma_r_copy);
            Some(Context::new_wf(gammaprime))
        } else {
            None
        }
    }

    pub fn insert_at(&self, c: ContextElim<CONTEXT_INCOMPLETE>, theta: Context) -> Context {
        let (gamma_l, gamma_r) = self.inspect_context(&c);
        let mut result_list = gamma_l.0.clone();
        let mut theta_copy = theta.0.clone();
        let mut gamma_r_copy = gamma_r.0.clone();
        result_list.append(&mut theta_copy);
        result_list.append(&mut gamma_r_copy);
        Context::new_wf(result_list)
    }

    pub fn apply_(&self, typ: &Polytype) -> Polytype {
        match typ {
            Type::TUnit(l) => Type::TUnit(l.clone()),
            Type::TAny(l) => Type::TAny(l.clone()),
            Type::TAtom(l) => Type::TAtom(l.clone()),
            Type::TVar(v) => Type::TVar(v.clone()),
            Type::TForall(v,t) => Type::TForall(v.clone(),t.clone()),
            Type::TExists(v) => {
                debug!("apply texists {}: context is {}", v.to_sexp().to_string(), self.to_sexp().to_string());
                self.find_solved(v).map(|v| {
                    self.apply(&polytype(&v))
                }).unwrap_or_else(|| Type::TExists(v.clone()))
            },
            Type::TNullable(t) => Type::TNullable(Rc::new(self.apply(t))),
            Type::TExec(t) => Type::TExec(Rc::new(self.apply(t))),
            Type::TFun(t1,t2) => Type::TFun(Rc::new(self.apply(t1)), Rc::new(self.apply(t2))),
            Type::TPair(t1,t2) => Type::TPair(Rc::new(self.apply(t1)), Rc::new(self.apply(t2)))
        }
    }

    pub fn apply(&self, typ: &Polytype) -> Polytype {
        let res = self.apply_(typ);
        debug!("apply {} in {} => {}", typ.to_sexp().to_string(), self.to_sexp().to_string(), res.to_sexp().to_string());
        res
    }

    pub fn ordered(&self, alpha: &TypeVar, beta: &TypeVar) -> bool {
        let gamma_l = self.drop_context(ContextElim::CExists(beta.clone()));
        gamma_l.existentials().elem(alpha)
    }
}

impl GContext<CONTEXT_INCOMPLETE> {
    pub fn appends_wf(&self, v: Vec<ContextElim<CONTEXT_INCOMPLETE>>) -> GContext<CONTEXT_INCOMPLETE> {
        let gamma = self.appends(v);
        if !gamma.wf() {
            panic!("not well formed");
        }
        gamma
    }

    pub fn snoc_wf(&self, c: ContextElim<CONTEXT_INCOMPLETE>) -> GContext<CONTEXT_INCOMPLETE> {
        let gamma = self.snoc(c);
        if !gamma.wf() {
            panic!("not well formed");
        }
        gamma
    }

    pub fn new_wf(elems: Vec<ContextElim<CONTEXT_INCOMPLETE>>) -> GContext<CONTEXT_INCOMPLETE> {
        let ctx = GContext(elems);
                if !ctx.wf() {
            panic!("not well formed {}", ctx.to_sexp().to_string());
        }
        ctx
    }

    pub fn drop_marker<E,X,F>(
        &self,
        m: ContextElim<CONTEXT_INCOMPLETE>,
        f: F
    ) -> Result<GContext<CONTEXT_INCOMPLETE>, E>
    where
        F: FnOnce(GContext<CONTEXT_INCOMPLETE>) -> Result<X, E>,
        X: ExtractContext<CONTEXT_INCOMPLETE>
    {
        let marked = self.snoc_wf(m.clone());
        let res: GContext<CONTEXT_INCOMPLETE> = f(marked).map(|x| x.extract())?;
        Ok(res.0.iter().position(|e| *e == m).map(|idx| {
            GContext(res.0[idx+1..].iter().map(|x| x.clone()).collect())
        }).unwrap_or_else(|| {
            GContext(Vec::new())
        }))
    }
}
