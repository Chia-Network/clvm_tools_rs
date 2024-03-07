// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{
    Context, ContextElim, Expr, ExtractContext, GContext, Monotype, Polytype, Type, TypeVar, Var,
    CONTEXT_INCOMPLETE,
};
use crate::compiler::types::astfuns::{monotype, polytype, type_subst, unrecurse};
use crate::compiler::types::namegen::fresh_tvar;

// | subst e' x e = [e'/x]e
pub fn subst(eprime: &Expr, x: Var, expr: &Expr) -> Expr {
    match expr {
        Expr::EVar(xprime) => {
            if *xprime == x {
                eprime.clone()
            } else {
                Expr::EVar(xprime.clone())
            }
        }

        Expr::EUnit(l) => Expr::EUnit(l.clone()),

        Expr::ELit(l, n) => Expr::ELit(l.clone(), n.clone()),

        Expr::EAbs(xprime, e) => {
            if *xprime == x {
                Expr::EAbs(xprime.clone(), e.clone())
            } else {
                Expr::EAbs(xprime.clone(), Rc::new(subst(eprime, x, e)))
            }
        }

        Expr::EApp(e1, e2) => Expr::EApp(
            Rc::new(subst(eprime, x.clone(), e1)),
            Rc::new(subst(eprime, x, e2)),
        ),

        Expr::EAnno(e, t) => Expr::EAnno(Rc::new(subst(eprime, x, e)), t.clone()),
    }
}

fn existentials_aux<const K: usize>(ce: &ContextElim<K>) -> Option<&TypeVar> {
    match ce {
        ContextElim::CExists(alpha) => Some(alpha),
        ContextElim::CExistsSolved(alpha, _) => Some(alpha),
        _ => None,
    }
}

pub trait HasElem {
    type Item;
    fn elem(&self, i: &<Self as HasElem>::Item) -> bool;
}

impl<X: Eq> HasElem for Vec<X> {
    type Item = X;
    fn elem(&self, i: &X) -> bool {
        self.iter().any(|a| a == i)
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

    pub fn solved(&self) -> Vec<TypeVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let ContextElim::CExistsSolved(alpha, _) = gamma_elem {
                res.push(alpha.clone());
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
            if let ContextElim::CVar(x, _) = gamma_elem {
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
        let cs = self.0.iter().skip(1).cloned().collect();
        // Do not use new_wf here... we're already checking well-formedness
        let mut gamma = Context::new(cs);

        match c {
            ContextElim::CForall(alpha) => !gamma.foralls().elem(&alpha),
            ContextElim::CVar(x, a) => !gamma.vars().elem(&x) && gamma.typewf(&a),
            ContextElim::CExists(alpha) => !gamma.existentials().elem(&alpha),
            ContextElim::CExistsSolved(alpha, tau) => {
                // alpha must not exist to the right of the solution but...
                let no_existentials = !gamma.existentials().elem(&alpha);
                // If tau is a simple recursive definition then alpha should
                // appear in it.  Backstop alpha free in tau.
                gamma.0.insert(0, ContextElim::CExists(alpha));
                no_existentials && gamma.typewf(&tau)
            }
            ContextElim::CMarker(alpha) => {
                !gamma.markers().elem(&alpha) && !gamma.existentials().elem(&alpha)
            }
        }
    }

    pub fn wf(&self) -> bool {
        self.wf_()
    }

    pub fn newtype<const A: usize>(
        &self,
        t1: &Polytype,
        t2: &Polytype,
    ) -> Option<(Type<A>, Context)> {
        if let Type::TVar(v) = t1 {
            if let Some(solved) = self.find_solved(v) {
                return if let Type::TAbs(v, t) = solved {
                    let tpoly = polytype(t.borrow());
                    let new_tvar = fresh_tvar(v.loc());
                    let finished_type_rec = type_subst(t2, &v, &tpoly);
                    unrecurse(&new_tvar, t1, t2, &finished_type_rec)
                        .and_then(|finished_type| monotype(&finished_type))
                        .map(|tmono| {
                            let new_ctx = self.appends_wf(vec![ContextElim::CExistsSolved(
                                new_tvar.clone(),
                                tmono,
                            )]);

                            (Type::TExists(new_tvar), new_ctx)
                        })
                } else {
                    None
                };
            }
        }

        None
    }

    pub fn typewf<const A: usize>(&self, typ: &Type<A>) -> bool {
        match typ {
            Type::TVar(alpha) => self.foralls().elem(alpha) || self.solved().elem(alpha),
            Type::TUnit(_) => true,
            Type::TAny(_) => true,
            Type::TAtom(_, _) => true,
            Type::TNullable(t) => self.typewf(t.borrow()),
            Type::TExec(t) => self.typewf(t.borrow()),
            Type::TFun(a, b) => self.typewf(a.borrow()) && self.typewf(b.borrow()),
            Type::TPair(a, b) => self.typewf(a.borrow()) && self.typewf(b.borrow()),
            Type::TForall(alpha, a) => self.snoc_wf(ContextElim::CForall(alpha.clone())).typewf(a),
            Type::TExists(alpha) => self.existentials().elem(alpha),
            Type::TAbs(s, t) => {
                let checktype: Type<A> = Type::TForall(s.clone(), Rc::new(polytype(t.borrow())));
                self.typewf(&checktype)
            }
            Type::TApp(t1, t2) => {
                if !self.typewf(t1.borrow()) {
                    return false;
                }

                let t1poly = polytype(t1.borrow());
                let t2poly = polytype(t2.borrow());
                if let Some((nt, ctx)) = self.newtype::<A>(&t1poly, &t2poly) {
                    ctx.typewf(&nt)
                } else {
                    false
                }
            }
        }
    }

    pub fn checkwf(&self, loc: Srcloc) -> Result<(), CompileErr> {
        if self.wf() {
            return Ok(());
        }

        Err(CompileErr(
            loc,
            format!("Malformed context: {}", self.to_sexp()),
        ))
    }

    pub fn checkwftype(&self, a: &Polytype) -> Result<(), CompileErr> {
        if self.typewf(a) {
            return self.checkwf(a.loc());
        }

        Err(CompileErr(
            a.loc(),
            format!("Malformed type: {} in {}", a.to_sexp(), self.to_sexp()),
        ))
    }

    pub fn find_solved(&self, v: &TypeVar) -> Option<Monotype> {
        for t in self.0.iter() {
            if let ContextElim::CExistsSolved(vprime, t) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn find_var_type(&self, v: &Var) -> Option<Polytype> {
        for t in self.0.iter() {
            if let ContextElim::CVar(vprime, t) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn insert_at(&self, c: &TypeVar, theta: Context) -> Context {
        let (gamma_l, gamma_r) = self.inspect_context(c);
        let mut result_list = gamma_r.0;
        let mut theta_copy = theta.0;
        let mut gamma_l_copy = gamma_l.0;
        result_list.append(&mut theta_copy);
        result_list.append(&mut gamma_l_copy);
        let res = Context::new_wf(result_list);
        res
    }

    pub fn apply_(&self, visited: &mut HashSet<Polytype>, typ: &Polytype) -> Polytype {
        // Defeat recursion.
        if visited.contains(typ) {
            return typ.clone();
        }

        visited.insert(typ.clone());

        match typ {
            Type::TUnit(_) => typ.clone(),
            Type::TAny(_) => typ.clone(),
            Type::TAtom(_, _) => typ.clone(),
            Type::TVar(_) => typ.clone(),
            Type::TForall(v, t) => Type::TForall(v.clone(), t.clone()),
            Type::TExists(v) => self
                .find_solved(v)
                .map(|v| self.apply_(visited, &polytype(&v)))
                .unwrap_or_else(|| Type::TExists(v.clone())),
            Type::TNullable(t) => Type::TNullable(Rc::new(self.apply_(visited, t))),
            Type::TExec(t) => Type::TExec(Rc::new(self.apply_(visited, t))),
            Type::TFun(t1, t2) => Type::TFun(
                Rc::new(self.apply_(visited, t1)),
                Rc::new(self.apply_(visited, t2)),
            ),
            Type::TPair(t1, t2) => Type::TPair(
                Rc::new(self.apply_(visited, t1)),
                Rc::new(self.apply_(visited, t2)),
            ),
            Type::TAbs(v, t) => Type::TAbs(v.clone(), Rc::new(self.apply_(visited, t))),
            Type::TApp(t1, t2) => Type::TApp(
                Rc::new(self.apply_(visited, t1)),
                Rc::new(self.apply_(visited, t2)),
            ),
        }
    }

    pub fn apply(&self, typ: &Polytype) -> Polytype {
        let mut visited = HashSet::new();
        self.apply_(&mut visited, typ)
    }

    pub fn ordered(&self, alpha: &TypeVar, beta: &TypeVar) -> bool {
        let gamma_l = self.drop_context(ContextElim::CExists(beta.clone()));
        gamma_l.existentials().elem(alpha)
    }
}

impl GContext<CONTEXT_INCOMPLETE> {
    pub fn appends_wf(
        &self,
        v: Vec<ContextElim<CONTEXT_INCOMPLETE>>,
    ) -> GContext<CONTEXT_INCOMPLETE> {
        self.appends(v)
    }

    pub fn snoc_wf(&self, c: ContextElim<CONTEXT_INCOMPLETE>) -> GContext<CONTEXT_INCOMPLETE> {
        self.snoc(c)
    }

    pub fn new_wf(elems: Vec<ContextElim<CONTEXT_INCOMPLETE>>) -> GContext<CONTEXT_INCOMPLETE> {
        GContext(elems)
    }

    pub fn drop_marker<E, X, F>(
        &self,
        m: ContextElim<CONTEXT_INCOMPLETE>,
        f: F,
    ) -> Result<GContext<CONTEXT_INCOMPLETE>, E>
    where
        F: FnOnce(GContext<CONTEXT_INCOMPLETE>) -> Result<X, E>,
        X: ExtractContext<CONTEXT_INCOMPLETE>,
    {
        let marked = self.snoc_wf(m.clone());
        let res: GContext<CONTEXT_INCOMPLETE> = f(marked).map(|x| x.extract())?;
        Ok(res
            .0
            .iter()
            .position(|e| *e == m)
            .map(|idx| {
                GContext(res.0[idx + 1..].to_vec())
            })
            .unwrap_or_else(|| {
                GContext(Vec::new())
            }))
    }
}
