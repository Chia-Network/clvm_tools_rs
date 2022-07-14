// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::rc::Rc;
use log::debug;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::srcloc::HasLoc;
use crate::compiler::types::ast::{
    Context,
    ContextElim,
    Expr,
    Polytype,
    TypeVar,
    Type
};
use crate::compiler::types::astfuns::{
    free_tvars,
    monotype,
    polytype,
    tforalls,
    type_subst,
    type_substs
};
use crate::compiler::types::context::{HasElem};
use crate::compiler::types::namegen::{fresh_var, fresh_tvar};
use crate::compiler::types::context::subst;
use crate::compiler::typecheck::TheoryToSExp;

const ORIGINAL: bool = false;

pub trait TypeTheory {
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr>;
    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr>;
    fn typeapplysynth(&self, typ: &Polytype, e: &Expr) -> Result<(Polytype, Box<Self>), CompileErr>;
    fn reify(&self, typ: &Polytype) -> Polytype;
}

impl Context {
    // | Algorithmic subtyping:
    //   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
    //
    // Given some morphism Delta on Gamma, B element Delta checks as A in Gamma
    fn subtype_(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr> {
        let double_exists = |alpha: &TypeVar, alphaprime: &TypeVar| {
            let exi = self.existentials();
            if alpha == alphaprime && exi.elem(alpha) {
                Some(Box::new(self.clone()))
            } else {
                None
            }
        };

        let _ = self.checkwftype(typ1)?;
        let _ = self.checkwftype(typ2)?;
        debug!("subtype {} {}", typ1.to_sexp().to_string(), typ2.to_sexp().to_string());
        match (typ1, typ2) {
            (Type::TVar(alpha), Type::TVar(alphaprime)) => {
                debug!("case 1");
                if alpha == alphaprime {
                    return Ok(Box::new(self.clone()));
                }
            },
            (Type::TUnit(_), Type::TUnit(_)) => {
                debug!("case 2");
                return Ok(Box::new(self.clone()));
            },
            (Type::TAtom(_), Type::TAtom(_)) => {
                debug!("case 3");
                return Ok(Box::new(self.clone()));
            },
            (Type::TFun(a1,a2), Type::TFun(b1,b2)) => {
                debug!("case 5");
                let theta = self.subtype(b1,a1)?;
                return theta.subtype(&theta.apply(a2), &theta.apply(b2));
            },

            (Type::TNullable(a), Type::TNullable(b)) => {
                debug!("case nullable");
                return self.subtype(a,b);
            },

            (Type::TExec(a), Type::TExec(b)) => {
                debug!("exec");
                return self.subtype(a,b);
            },

            (Type::TPair(a1,a2), Type::TPair(b1,b2)) => {
                debug!("case 6");
                let theta = self.subtype(a1,b1)?;
                return theta.subtype(a2,b2);
            },

            // <:forallR
            (a, Type::TForall(alpha,b)) => {
                let alphaprime = fresh_tvar(typ2.loc());
                debug!("case 7 a' = {}", alphaprime.to_sexp().to_string());
                return self.drop_marker(
                    ContextElim::CForall(alphaprime.clone()),
                    |gamma| {
                        gamma.subtype(
                            a,
                            &type_subst(
                                &Type::TVar(alphaprime.clone()),
                                &alpha.clone(),
                                b
                            )
                        )
                    }
                ).map(|x| Box::new(x));
            },

            // <:forallL
            (Type::TForall(alpha,a), b) => {
                debug!("case 8");
                let alphaprime = fresh_tvar(typ1.loc());
                let marker = fresh_tvar(typ1.loc());
                return self.appends_wf(vec![
                    ContextElim::CExists(alphaprime.clone())
                ]).drop_marker(
                    ContextElim::CMarker(marker.clone()),
                    |gamma| {
                        gamma.subtype(
                            &type_subst(
                                &Type::TExists(alphaprime.clone()),
                                &alpha.clone(),
                                a.borrow()
                            ),
                            &b.clone()
                        )
                    }
                ).map(|x| Box::new(x));
            },

            // <:instantiateL
            (Type::TExists(alpha), a) => {
                // Original code: Type.hs line 29 uses a guard
                if let Type::TExists(alphaprime) = a {
                    if let Some(r) = double_exists(alpha, alphaprime) {
                        return Ok(r);
                    }
                }

                if let Type::TNullable(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TNullable(Rc::new(Type::TVar(avar.clone())))
                        ))));
                    }
                }

                if let Type::TExec(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TExec(Rc::new(Type::TVar(avar.clone())))
                        ))));
                    }
                }

                let exi = self.existentials();
                if exi.elem(alpha) &&
                    !free_tvars(a).contains(alpha) {
                    return self.instantiate_l(alpha, a);
                }
            },

            // <:instantiateR
            (a, Type::TExists(alpha)) => {
                // Original code: Type.hs line 29 uses a guard
                if let Type::TExists(alphasub) = a {
                    if let Some(r) = double_exists(alphasub, alpha) {
                        return Ok(r);
                    }
                }

                if let Type::TNullable(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TNullable(Rc::new(Type::TVar(avar.clone())))
                        ))));
                    }
                }

                if let Type::TExec(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TExec(Rc::new(Type::TVar(avar.clone())))
                        ))));
                    }
                }

                let exi = self.existentials();
                if exi.elem(alpha) &&
                    !free_tvars(a).contains(alpha) {
                    return self.instantiate_r(a, alpha);
                }
            }

            _ => {
                debug!("subtype, didn't match");
            }
        }

        Err(CompileErr(typ1.loc(), format!("subtype, don't know what to do with: {} {} in context {}", typ1.to_sexp().to_string(), typ2.to_sexp().to_string(), self.to_sexp().to_string())))
    }

    // | Algorithmic instantiation (left):
    //   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
    fn instantiate_l_(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(&Type::TExists(alpha.clone()))?;
        let _ = self.checkwftype(a)?;
        match monotype(a).and_then(|mta| self.solve(alpha, &mta)) {
            Some(gammaprime) => { return Ok(Box::new(gammaprime)); },
            None => {
                match a {
                    // InstLReach
                    Type::TExists(beta) => {
                        if self.ordered(alpha,beta) {
                            return self.solve(beta, &Type::TExists(alpha.clone())).map(|x| Ok(x.clone())).unwrap_or_else(|| Err(CompileErr(alpha.loc(), format!("no solution in instantiate_l for {:?} {:?} in context {:?}", alpha, a, self)))).map(|x| Box::new(x));
                        } else {
                            return self.solve(alpha, &Type::TExists(beta.clone())).map(|x| Ok(x.clone())).unwrap_or_else(|| Err(CompileErr(alpha.loc(), format!("no solution in instantiate_l for {:?} {:?} in context {:?}", a, alpha, self)))).map(|x| Box::new(x));
                        }
                    },
                    // InstLArr
                    Type::TFun(a1, a2) => {
                        let alpha1 = fresh_tvar(a1.loc());
                        let alpha2 = fresh_tvar(a2.loc());
                        let rcontext = Context::new(vec![
                            ContextElim::CExists(alpha2.clone()),
                            ContextElim::CExists(alpha1.clone()),
                            ContextElim::CExistsSolved(
                                alpha.clone(),
                                Type::TFun(
                                    Rc::new(Type::TExists(alpha1.clone())),
                                    Rc::new(Type::TExists(alpha2.clone()))
                                )
                            )
                        ]);
                        let theta = (self.insert_at(ContextElim::CExists(alpha.clone()), rcontext)).
                            instantiate_r(a1, alpha)?;
                        return theta.instantiate_l(&alpha2, &theta.apply(a2));
                    },
                    // InstLAIIR
                    Type::TForall(beta, b) => {
                        let betaprime = fresh_tvar(beta.loc());
                        return self.drop_marker(
                            ContextElim::CForall(betaprime.clone()),
                            |gamma| {
                                gamma.instantiate_l(
                                    alpha,
                                    &type_subst(
                                        &Type::TVar(betaprime.clone()),
                                        &beta.clone(),
                                        b.borrow()
                                    )
                                )
                            }
                        ).map(|x| Box::new(x));
                    },

                    Type::TExec(t) => {
                        let alpha1 = fresh_tvar(t.loc());
                        let rcontext = Context::new(vec![
                            ContextElim::CExists(alpha1.clone()),
                            ContextElim::CExistsSolved(
                                alpha.clone(),
                                Type::TExec(Rc::new(Type::TExists(alpha1.clone())))
                            )
                        ]);
                        return self.insert_at(ContextElim::CExists(alpha.clone()), rcontext).
                            instantiate_r(t, alpha);
                    },

                    _ => { }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_l: {} {} {}", alpha.to_sexp().to_string(), a.to_sexp().to_string(), self.to_sexp().to_string())))
    }

    // | Algorithmic instantiation (right):
    //   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
    fn instantiate_r_(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(a);
        let _ = self.checkwftype(&Type::TExists(alpha.clone()));
        match monotype(a).and_then(|mta| self.solve(alpha,&mta)) {
            Some(gammaprime) => { return Ok(Box::new(gammaprime)); },
            None => {
                // InstRReach
                debug!("match {}", a.to_sexp().to_string());
                match a {
                    Type::TNullable(a1) => {
                        match monotype(a) {
                            Some(mta) => {
                                return Ok(Box::new(self.appends_wf(vec![
                                    ContextElim::CForall(alpha.clone()),
                                    ContextElim::CExistsSolved(alpha.clone(), mta)
                                ])));
                            },
                            _ => {
                                todo!("no monotype: {}", a.to_sexp().to_string())
                            }
                        }
                    },
                    Type::TExec(a1) => {
                        match monotype(a) {
                            Some(mta) => {
                                return Ok(Box::new(self.appends_wf(vec![
                                    ContextElim::CForall(alpha.clone()),
                                    ContextElim::CExistsSolved(alpha.clone(), mta)
                                ])));
                            },
                            _ => {
                                todo!("no monotype: {}", a.to_sexp().to_string())
                            }
                        }
                    },
                    Type::TPair(a1,a2) => {
                        match monotype(a) {
                            Some(mta) => {
                                return Ok(Box::new(self.appends_wf(vec![
                                    ContextElim::CForall(alpha.clone()),
                                    ContextElim::CExistsSolved(alpha.clone(), mta)
                                ])));
                            },
                            _ => {
                                todo!("no monotype: {}", a.to_sexp().to_string())
                            }
                        }
                    },
                    Type::TExists(beta) => {
                        debug!("texists {}", beta.to_sexp().to_string());
                        if self.ordered(alpha, beta) {
                            match self.solve(beta, &Type::TExists(alpha.clone())) {
                                Some(res) => { return Ok(Box::new(res)); },
                                None => {
                                    return Err(CompileErr(alpha.loc(), format!("no solution in instantiate_r: {} {} with context {:?}", a.to_sexp().to_string(), alpha.to_sexp().to_string(), self)));
                                }
                            }
                        } else {
                            match self.solve(alpha, &Type::TExists(beta.clone())) {
                                Some(res) => { return Ok(Box::new(res)); },
                                None => {
                                    return Err(CompileErr(beta.loc(), format!("no solution in instantiate_r: {} {} with context {:?}", a.to_sexp().to_string(), alpha.to_sexp().to_string(), self)));
                                }
                            }
                        }
                    },
                    Type::TFun(a1, a2) => {
                        let alpha1 = fresh_tvar(a1.loc());
                        let alpha2 = fresh_tvar(a2.loc());
                        let rcontext = Context::new(vec![
                            ContextElim::CExists(alpha2.clone()),
                            ContextElim::CExists(alpha1.clone()),
                            ContextElim::CExistsSolved(alpha.clone(), Type::TFun(Rc::new(Type::TExists(alpha1.clone())), Rc::new(Type::TVar(alpha2.clone()))))
                        ]);
                        let theta = (self.insert_at(
                            ContextElim::CExists(alpha.clone()), rcontext
                        )).instantiate_l(&alpha1, a1.borrow())?;
                        return theta.instantiate_r(
                            &theta.apply(a2.borrow()), &alpha2
                        );
                    },
                    Type::TForall(beta, b) => {
                        let betaprime = fresh_tvar(beta.loc());
                        return self.drop_marker(
                            ContextElim::CMarker(betaprime.clone()),
                            |gamma| {
                                self.appends_wf(vec![
                                    ContextElim::CExists(betaprime.clone())
                                ]).instantiate_r(
                                    &type_subst(
                                        &Type::TExists(betaprime.clone()), &beta.clone(), b
                                    ),
                                    alpha
                                )
                            }
                        ).map(|x| Box::new(x));
                    },
                    _ => { }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_r: {:?} {:?} {:?}", self, a, alpha)))
    }

    // | Type checking:
    //   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
    fn typecheck_(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(typ)?;
        match (expr, typ) {
            // 1I
            (Expr::EUnit(_), Type::TUnit(_)) => Ok(Box::new(self.clone())),
            // ForallI
            (e, Type::TForall(alpha, a)) => {
                let alphaprime = fresh_tvar(typ.loc());
                return self.drop_marker(
                    ContextElim::CForall(alphaprime.clone()),
                    |gamma| {
                        gamma.typecheck(
                            e,
                            &type_subst(
                                &Type::TVar(alphaprime.clone()),
                                &alpha.clone(),
                                a
                            )
                        )
                    }
                ).map(|x| Box::new(x));
            },

            (Expr::EUnit(_), Type::TNullable(_)) => Ok(Box::new(self.clone())),

            // ->I
            (Expr::EAbs(x,e), Type::TFun(a,b)) => {
                let xprime = fresh_var(expr.loc());
                let a_borrowed: &Polytype = a.borrow();
                let b_borrowed: &Polytype = b.borrow();
                let e_borrowed: &Expr = e.borrow();
                self.drop_marker(
                    ContextElim::CVar(xprime.clone(),a_borrowed.clone()),
                    |gamma| {
                        gamma.typecheck(
                            &subst(&Expr::EVar(xprime.clone()), x.clone(), e_borrowed),
                            b_borrowed
                        )
                    }
                ).map(|x| Box::new(x))
            },
            // Sub
            (e, b) => {
                let (a, theta) = self.typesynth(e)?;
                return theta.subtype(&theta.apply(&a), &theta.apply(b));
            }
        }
    }

    // | Type synthesising:
    //   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
    fn typesynth_(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        let _ = self.checkwf(expr.loc());
        match expr {
            // Var
            Expr::EVar(x) => {
                return self.find_var_type(x).map(|ty| {
                    Ok((ty, Box::new(self.clone())))
                }).unwrap_or_else(|| {
                    Err(CompileErr(expr.loc(), format!("typesynth: not in scope {:?} in context {:?}", expr, self)))
                });
            },

            // Anno
            Expr::EAnno(e,a) => {
                let delta = self.typecheck(e,a)?;
                return Ok((a.clone(), delta));
            },

            // 1I=>
            Expr::EUnit(l) => { return Ok((Type::TUnit(l.clone()), Box::new(self.clone()))); },

            Expr::ELit(l,_) => { return Ok((Type::TAtom(l.clone()), Box::new(self.clone()))); },

            // ->I=> Original rule
            Expr::EAbs(x,e) => {
                let xprime = fresh_var(x.loc());
                let alpha = fresh_tvar(x.loc());
                let beta = fresh_tvar(e.loc());
                let e_borrowed: &Expr = e.borrow();
                let subst_res = subst(
                    &Expr::EVar(xprime.clone()),
                    x.clone(),
                    e_borrowed
                );

                let (delta, deltaprime) = self.appends_wf(vec![
                    ContextElim::CExists(alpha.clone()),
                    ContextElim::CExists(beta.clone()),
                    ContextElim::CVar(
                        xprime.clone(),
                        Type::TExists(alpha.clone())
                    )
                    ]).break_marker(
                    ContextElim::CMarker(alpha.clone()),
                    |gamma| {
                        gamma.typecheck(
                            &subst_res,
                            &Type::TExists(beta.clone())
                        )
                    })?;

                debug!("delta  {}", delta.to_sexp().to_string());
                debug!("delta' {}", deltaprime.to_sexp().to_string());

                let tau = deltaprime.apply(&Type::TFun(
                    Rc::new(Type::TExists(alpha.clone())),
                    Rc::new(Type::TExists(beta.clone()))
                ));

                debug!("tau   {}", tau.to_sexp().to_string());

                let evars = deltaprime.unsolved();
                debug!("unsolved:");
                let uvars: Vec<(Polytype, TypeVar)> = evars.iter().map(|e| (Type::TVar(e.clone()), fresh_tvar(x.loc()))).collect();
                for e in uvars.iter() {
                    debug!(" - {} = {}", e.1.to_sexp().to_string(), e.0.to_sexp().to_string());
                }
                let tfa = tforalls(evars, type_substs(uvars, tau));
                Ok((tfa, Box::new(delta)))
            },

            // ->E
            Expr::EApp(e1,e2) => {
                let (a, theta) = self.typesynth(e1)?;
                theta.typeapplysynth(&theta.apply(&a), e2)
            }
        }
    }

    fn typeapplysynth_(&self, typ: &Polytype, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        let _ = self.checkwftype(typ)?;

        let resolve_inner_type = |t: &Polytype, delta: &Context| {
            if let Type::TExists(tv) = t.borrow() {
                if let Some(tau) = delta.find_solved(tv).as_ref().map(|t| polytype(t)) {
                    return Some(tau);
                }
            }

            None
        };

        match typ {
            // ForallApp
            Type::TForall(alpha,a) => {
                // Do alpha conversion to avoid clashes
                let alphaprime = fresh_tvar(typ.loc());
                return self.snoc_wf(
                    ContextElim::CExists(alphaprime.clone())
                ).typeapplysynth(
                    &type_subst(
                        &Type::TExists(alphaprime.clone()),
                        &alpha.clone(),
                        a
                    ),
                    expr
                );
            },

            // alpha^App
            Type::TExists(alpha) => {
                let alpha1 = fresh_tvar(typ.loc());
                let alpha2 = fresh_tvar(typ.loc());
                let rcontext = Context::new(vec![
                    ContextElim::CExists(alpha2.clone()),
                    ContextElim::CExists(alpha1.clone()),
                    ContextElim::CExistsSolved(
                        alpha.clone(),
                        Type::TFun(
                            Rc::new(Type::TExists(alpha1.clone())),
                            Rc::new(Type::TExists(alpha2.clone()))
                        )
                    )
                ]);
                let delta = (self.insert_at(
                    ContextElim::CExists(alpha.clone()),
                    rcontext
                )).typecheck(expr, &Type::TExists(alpha1.clone()))?;
                return Ok((Type::TExists(alpha2.clone()), delta));
            },

            // ->App
            Type::TFun(a, c) => {
                let c_borrowed: &Polytype = c.borrow();
                let delta = self.typecheck(expr, a)?;
                match c_borrowed {
                    Type::TNullable(t) => {
                        if let Some(tau) = resolve_inner_type(t, delta.borrow()) {
                            return Ok((
                                Type::TNullable(Rc::new(tau.clone())),
                                delta
                            ));
                        }
                    },
                    Type::TExec(t) => {
                        if let Some(tau) = resolve_inner_type(t, delta.borrow()) {
                            return Ok((
                                Type::TExec(Rc::new(tau.clone())),
                                delta
                            ));
                        }
                    },
                    Type::TPair(x,y) => {
                        let tau =
                            resolve_inner_type(x, delta.borrow()).
                            map(|x| Rc::new(x)).
                            unwrap_or_else(|| x.clone());
                        let sigma =
                            resolve_inner_type(y, delta.borrow()).
                            map(|y| Rc::new(y)).
                            unwrap_or_else(|| y.clone());

                        return Ok((
                            Type::TPair(
                                tau.clone(),
                                sigma.clone()
                            ),
                            delta
                        ));
                    },
                    _ => { }
                }

                return Ok((c_borrowed.clone(), delta));
            },

            Type::TNullable(t) => {
                let delta = self.typecheck(expr, &Type::TNullable(t.clone()))?;
                return Ok((Type::TNullable(t.clone()), delta));
            },

            Type::TExec(t) => {
                let delta = self.typecheck(expr, &Type::TExec(t.clone()))?;
                return Ok((Type::TExec(t.clone()), delta));
            }

            _ => { }
        }

        Err(CompileErr(expr.loc(), format!("typeapplysynth: don't know what to do with: {} {} in context {}", typ.to_sexp().to_string(), expr.to_sexp().to_string(), self.to_sexp().to_string())))
    }
}

impl TypeTheory for Context {
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr> {
        let res = self.subtype_(typ1, typ2);
        match &res {
            Ok(v) => { debug!("subtype {} {} in {} => {}", typ1.to_sexp().to_string(), typ2.to_sexp().to_string(), self.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(e) => { debug!("subtype {} {} in {} => {:?}", typ1.to_sexp().to_string(), typ2.to_sexp().to_string(), self.to_sexp().to_string(), e); }
        }
        res
    }

    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr> {
        let res = self.instantiate_l_(alpha, a);
        match &res {
            Ok(v) => { debug!("instantiate_l {} {} in {} => {}", alpha.to_sexp().to_string(), a.to_sexp().to_string(), self.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(e) => { debug!("instantiate_l {} {} in {} => {:?}", alpha.to_sexp().to_string(), a.to_sexp().to_string(), self.to_sexp().to_string(), e); }
        }
        res
    }


    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr> {
        let res = self.instantiate_r_(a, alpha);
        match &res {
            Ok(v) => { debug!("instantiate_r {} {} in {} => {}", a.to_sexp().to_string(), alpha.to_sexp().to_string(), self.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(e) => { debug!("instantiate_r {} {} in {} => {:?}", a.to_sexp().to_string(), alpha.to_sexp().to_string(), self.to_sexp().to_string(), e); }
        }
        res
    }

    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr> {
        let res = self.typecheck_(expr, typ);
        match &res {
            Ok(v) => { debug!("typecheck {} {} in {} => {}", expr.to_sexp().to_string(), typ.to_sexp().to_string(), self.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(e) => { debug!("typecheck {} {} in {} => {:?}", expr.to_sexp().to_string(), typ.to_sexp().to_string(), self.to_sexp().to_string(), e); }
        }
        res
    }

    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        let res = self.typesynth_(expr);
        match &res {
            Ok((t,v)) => { debug!("typesynth {} in {} => ({} {})", expr.to_sexp().to_string(), self.to_sexp().to_string(), t.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(e) => { debug!("typesynth {} in {} => {:?}", expr.to_sexp().to_string(), self.to_sexp().to_string(), e); },
        }
        res
    }

    fn typeapplysynth(&self, typ: &Polytype, e: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        let res = self.typeapplysynth_(typ, e);
        match &res {
            Ok((t,v)) => { debug!("typeapplysynth {} {} in {} => ({} {})", typ.to_sexp().to_string(), e.to_sexp().to_string(), self.to_sexp().to_string(), t.to_sexp().to_string(), v.to_sexp().to_string()); },
            Err(err) => { debug!("typeapplysynth {} {} in {} => {:?}", typ.to_sexp().to_string(), e.to_sexp().to_string(), self.to_sexp().to_string(), err); }
        }
        res
    }

    // Perform all available substitutions
    fn reify(&self, typ: &Polytype) -> Polytype {
        match &typ {
            Type::TExists(tv) => {
                self.find_solved(tv).as_ref().map(|x| polytype(x)).unwrap_or_else(|| typ.clone())
            },
            Type::TForall(tv,ty) => {
                Type::TForall(tv.clone(), Rc::new(self.reify(ty)))
            },
            Type::TFun(a,b) => {
                Type::TFun(
                    Rc::new(self.reify(a)),
                    Rc::new(self.reify(b))
                )
            },
            Type::TNullable(t) => Type::TNullable(Rc::new(self.reify(t))),
            Type::TPair(a,b) => {
                Type::TPair(
                    Rc::new(self.reify(a)),
                    Rc::new(self.reify(b))
                )
            },

            _ => typ.clone()

        }
    }
}

pub fn typesynth_closed(e: &Expr) -> Result<(Polytype, Context), CompileErr> {
    let (a, gamma) = Context::new(vec![]).typesynth(e)?;
    Ok((gamma.apply(&a), *gamma))
}

// Examples as tests
