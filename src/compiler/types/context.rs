// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::comptypes::{CompileErr, HelperForm, BodyForm};

use crate::compiler::types::ast;
use crate::compiler::types::astfuns;

fn existentials_aux<K>(ce: &ContextElim<K>) -> Option<&TVar> {
    match ce {
        CExists(alpha) => Some(alpha),
        CExistsSolved(alpha,_) => Some(alpha),
        _ => None
    }
}

trait HasElem {
    type Item;
    fn elem(&self, i: &HasElem::Item) -> bool;
}

impl HasElem for Vec<X> where Eq<X> {
    type Item = X;
    fn elem(&self, i: &X) -> bool {
        !self.find(|a| a == i).is_none()
    }
}

impl Context {
    pub fn new() -> Self { Context(vec![]) }

    // TODO: Convert these to iter
    pub fn existentials(&self) -> Vec<TVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let Some(r) = existentials_aux(gamma_elem) {
                res.push(r.clone());
            }
        }
        res
    }

    pub fn unsolved(&self) -> Vec<TVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let CExists(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    pub fn vars(&self) -> Vec<Var> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let CVar(x,_) = gamma_elem {
                res.push(x.clone());
            }
        }
        res
    }

    pub fn foralls(&self) -> Vec<TVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let CForall(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    pub fn markers(&self) -> Vec<TVar> {
        let mut res = Vec::new();
        for gamma_elem in self.0.iter() {
            if let CMarker(alpha) = gamma_elem {
                res.push(alpha.clone());
            }
        }
        res
    }

    pub fn elem<A>(&self, typ: Type<A>) -> Bool {
        !self.0.find(|a| a == typ).is_none()
    }

    // Well-formedness of contexts
    // wf Gamma <=> Gamma ctx
    pub fn wf(&self) -> Bool {
        if self.0.is_empty() {
            return True;
        }

        let c = self.0[0].clone();
        let cs = self.0.skip(1).collect();
        let gamma = Context(cs);

        match c {
            CForall(alpha) => !gamma.foralls().elem(alpha),
            CVar(x,a) => !gamma.vars().elem(x) && gamma.typewf(a),
            CExists(alpha) => !gamma.existentials().elem(x),
            CExistsSolved(alpha,tau) => !gamma.existentials().elem(alpha) &&
                gamma.typewf(tau),
            CMarker(alpha) => !gamma.markers().elem(alpha) &&
                !gamma.existentials().elem(alpha)
        }
    }

    pub fn typefw<A>(&self, typ: Type<A>) -> Bool {
        match typ {
            TVar(alpha) => self.foralls().elem(alpha),
            TUnit => true,
            TFun(a,b) => self.typewf(a) && self.typewf(b),
            TForall(alpha,a) => gamma.snoc(CForall(alpha)).typewf(a),
            TExists(alpha) => gamma.existentials().elem(alpha)
        }
    }

    pub fn checkwf(&self) -> Result<(), CompileErr> {
        if self.wf() {
            return Ok(());
        }


        Err(CompileErr(x.loc(), format!("Malformed context: {:?}", self)))
    }

    pub fn checkwftype(&self, a: Polytype) -> Result<(), CompileErr> {
        if self.typewf(a) {
            return self.checkwf(x);
        }

        Err(CompileErr(x.loc(), format!("Malformed type: {:?}", self)))
    }

    pub fn find_solved(&self, v: TVar) -> Option<Monotype> {
        for t in self.0.iter() {
            if let CExistsSolved(vprime) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn find_var_type(&self, alpha: TVar, tau: Monotype) -> Option<Context> {
        for t in self.0.iter() {
            if let CVar(vprime) = t {
                if v == vprime {
                    return Some(t.clone());
                }
            }
        }

        None
    }

    pub fn solve(&self, alpha: TVar, tau: Monotype) -> Option<Context> {
        let (gamma_l, gamma_r) = self.breakMarker(CExists(alpha.clone()));
        let mut gammaprime = gamma_l.clone();
        let mut gamma_r_copy = gamma_r.clone();
        gammaprime.push(CExistsSolved(alpha.clone(), tau.clone()));
        gammaprime.append(&mut gamma_r_copy);
        if let Just gamma2 = gamma_l.typewf(tau) {
            Some(gammaprime)
        } else {
            None
        }
    }

    pub fn insert_at(&self, c: ContextElem<ContextElimIncomplete>, theta: Context) -> Context {
        let (gamma_l, gamma_r) = self.breakMarker(c);
        let mut result_list = Vec::gamma_l.clone();
        let mut theta_copy = theta.0.clone();
        let mut gamma_r_copy = gamma_r.clone();
        result_list.append(&mut theta_copy);
        result_list.append(&mut gamma_r_copy);
        Context(result_list)
    }

    pub fn apply(&self, typ: Polytype) -> Polytype {
        match typ {
            TUnit => TUnit,
            TVar(v) => TVar(v.clone()),
            TForall(v,t) => TForall(v.clone(),t.clone()),
            TExists(v) => self.find_solved(v).map(|v| {
                self.apply(polytype(v))
            }).unwrap_or_else(|| TExists v),
            TFun(t1,t2) => TFun(self.apply(t1), self.apply(t2))
        }
    }

    pub fn ordered(&self, alpha: TVar, beta: TVar) -> Bool {
        let gamma_l = self.dropMarker(CExists beta);
        Context(gamma_l).existentials().elem(alpha)
    }
}
