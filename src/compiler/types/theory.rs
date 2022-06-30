// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::types::ast::{
    Context,
    ContextElim,
    Expr,
    TypeVar,
    Type,
    Polytype
};
use crate::compiler::types::astfuns::{
    free_tvars,
    monotype,
    typeSubst
};
use crate::compiler::types::context::{HasElem};
use crate::compiler::types::namegen::{fresh_var, fresh_tvar};
use crate::compiler::types::context::{subst};

trait TypeTheory {
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr>;
    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr>;
    fn typeapplysynth(&self, typ: &Polytype, e: &Expr) -> Result<(Polytype, Box<Self>), CompileErr>;
}

impl TypeTheory for Context {
    // | Algorithmic subtyping:
    //   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(typ1)?;
        let _ = self.checkwftype(typ2)?;
        match (typ1, typ2) {
            (Type::TVar(alpha), Type::TVar(alphaprime)) => {
                if alpha == alphaprime {
                    return Ok(Box::new(self.clone()));
                }
            },
            (Type::TUnit, Type::TUnit) => { return Ok(Box::new(self.clone())); },
            (Type::TExists(alpha), Type::TExists(alphaprime)) => {
                if alpha == alphaprime && self.existentials().elem(alpha) {
                    return Ok(Box::new(self.clone()));
                }
            },
            (Type::TFun(a1,a2), Type::TFun(b1,b2)) => {
                let theta = self.subtype(b1,a1)?;
                return theta.subtype(&theta.apply(a2), &theta.apply(b2));
            },

            // <:forallR
            (a, Type::TForall(alpha,b)) => {
                let alphaprime = fresh_tvar();
                return self.snoc(
                    ContextElim::CForall(alphaprime.clone())
                ).subtype(
                    a,
                    &typeSubst(&Type::TVar(alphaprime.clone()), &alpha.clone(), b)
                ).map(|d| Box::new(d.dropMarker(ContextElim::CForall(alphaprime.clone()))));
            },

            // <:forallL
            (Type::TForall(alpha,a), b) => {
                let alphaprime = fresh_tvar();
                return self.appends(
                    vec![
                        ContextElim::CMarker(alphaprime.clone()),
                        ContextElim::CExists(alphaprime.clone())
                    ]
                ).subtype(
                    &typeSubst(
                        &Type::TExists(alphaprime.clone()),
                        &alpha.clone(),
                        a.borrow()
                    ),
                    &b.clone()
                ).map(|d| Box::new(d.dropMarker(ContextElim::CForall(alphaprime.clone()))));
            },

            // <:instantiateL
            (Type::TExists(alpha), a) => {
                if self.existentials().elem(alpha) &&
                    !free_tvars(a).contains(alpha) {
                    return self.instantiate_l(alpha, a);
                }
            },

            // <:instantiateR
            (a, Type::TExists(alpha)) => {
                if self.existentials().elem(alpha) &&
                    !free_tvars(a).contains(alpha) {
                    return self.instantiate_r(a, alpha);
                }
            },

            _ => { }
        }

        Err(CompileErr(typ1.loc(), format!("subtype, don't know what to do with: {:?} {:?} in context {:?}", typ1, typ2, self)))
    }

    // | Algorithmic instantiation (left):
    //   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(&Type::TExists(alpha.clone()))?;
        let _ = self.checkwftype(a)?;
        match monotype(a).and_then(|mta| self.solve(alpha, &mta)) {
            Some(gammaprime) => { return Ok(Box::new(gammaprime)); },
            Nothing => {
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
                        let alpha1 = fresh_tvar();
                        let alpha2 = fresh_tvar();
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
                        let betaprime = fresh_tvar();
                        return (self.appends(vec![
                            ContextElim::CForall(betaprime.clone())
                        ])).instantiate_l(
                            alpha,
                            &typeSubst(
                                &Type::TVar(betaprime.clone()),
                                &beta.clone(),
                                b.borrow()
                            )
                        ).map(|d| Box::new(d.dropMarker(ContextElim::CForall(betaprime.clone()))));
                    },

                    _ => { }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_l: {:?} {:?} {:?}", self, alpha, a)))
    }

    // | Algorithmic instantiation (right):
    //   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(a);
        let _ = self.checkwftype(&Type::TExists(alpha.clone()));
        match monotype(a).and_then(|mta| self.solve(alpha,&mta)) {
            Some(gammaprime) => { return Ok(Box::new(gammaprime)); },
            None => {
                // InstRReach
                match a {
                    Type::TExists(beta) => {
                        if self.ordered(alpha, beta) {
                            match self.solve(beta, &Type::TExists(alpha.clone())) {
                                Some(res) => { return Ok(Box::new(res)); },
                                None => {
                                    return Err(CompileErr(alpha.loc(), format!("no solution in instantiate_r: {:?} {:?} with context {:?}", a, alpha, self)));
                                }
                            }
                        }
                    },
                    Type::TFun(a1, a2) => {
                        let alpha1 = fresh_tvar();
                        let alpha2 = fresh_tvar();
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
                        let betaprime = fresh_tvar();
                        return (self.appends(vec![
                            ContextElim::CMarker(betaprime.clone()),
                            ContextElim::CExists(betaprime.clone()),
                        ])).instantiate_r(
                            &typeSubst(
                                &Type::TExists(betaprime.clone()), &beta.clone(), b
                            ),
                            alpha
                        ).map(|d| Box::new(d.dropMarker(ContextElim::CMarker(betaprime))));
                    },
                    _ => { }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_r: {:?} {:?} {:?}", self, a, alpha)))
    }

    // | Type checking:
    //   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(typ)?;
        match (expr, typ) {
            // 1I
            (Expr::EUnit, Type::TUnit) => Ok(Box::new(self.clone())),
            // ForallI
            (e, Type::TForall(alpha, a)) => {
                let alphaprime = fresh_tvar();
                return self.snoc(ContextElim::CForall(alphaprime.clone())).
                    typecheck(
                        e,
                        &typeSubst(&Type::TVar(alphaprime.clone()), &alpha.clone(), a)
                    ).map(|d| Box::new(d.dropMarker(ContextElim::CForall(alphaprime.clone()))));
            },
            // ->I
            (Expr::EAbs(x,e), Type::TFun(a,b)) => {
                let xprime = fresh_var();
                let a_borrowed: &Polytype = a.borrow();
                let b_borrowed: &Polytype = b.borrow();
                let e_borrowed: &Expr = e.borrow();
                return self.snoc(
                    ContextElim::CVar(xprime.clone(),a_borrowed.clone())
                ).typecheck(
                    &subst(&Expr::EVar(xprime.clone()), x.clone(), e_borrowed),
                    b_borrowed
                ).map(|d| Box::new(d.dropMarker(ContextElim::CVar(xprime.clone(), a_borrowed.clone()))));
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
    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
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
            Expr::EUnit => { return Ok((Type::TUnit, Box::new(self.clone()))); },

            // ->I=> Original rule
            Expr::EAbs(x,e) => {
                let xprime = fresh_var();
                let alpha = fresh_tvar();
                let beta = fresh_tvar();
                let e_borrowed: &Expr = e.borrow();
                let delta = self.appends(vec![
                    ContextElim::CExists(alpha.clone()),
                    ContextElim::CExists(beta.clone()),
                    ContextElim::CVar(xprime.clone(),Type::TExists(alpha.clone()))
                ]).typecheck(&subst(&Expr::EVar(xprime.clone()),x.clone(),e_borrowed), &Type::TExists(beta.clone())).map(|d| d.dropMarker(ContextElim::CVar(xprime.clone(), Type::TExists(alpha.clone()))))?;
                return Ok((Type::TFun(Rc::new(Type::TExists(alpha.clone())), Rc::new(Type::TExists(beta.clone()))), Box::new(delta)));
            }
            // ->E
            Expr::EApp(e1,e2) => {
                let (a, theta) = self.typesynth(e1)?;
                theta.typeapplysynth(&theta.apply(&a), e2)
            }
        }
    }

    fn typeapplysynth(&self, typ: &Polytype, e: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        let _ = self.checkwftype(typ)?;
        match typ {
            // ForallApp
            Type::TForall(alpha,a) => {
                // Do alpha conversion to avoid clashes
                let alphaprime = fresh_tvar();
                return self.snoc(
                    ContextElim::CExists(alphaprime.clone())
                ).typeapplysynth(
                    &typeSubst(
                        &Type::TExists(alphaprime.clone()),
                        &alpha.clone(),
                        a
                    ),
                    e
                );
            },

            // alpha^App
            Type::TExists(alpha) => {
                let alpha1 = fresh_tvar();
                let alpha2 = fresh_tvar();
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
                )).typecheck(e, &Type::TExists(alpha1.clone()))?;
                return Ok((Type::TExists(alpha2.clone()), delta));
            },

            // ->App
            Type::TFun(a, c) => {
                let c_borrowed: &Polytype = c.borrow();
                let delta = self.typecheck(e,a)?;
                return Ok((c_borrowed.clone(), delta));
            },

            _ => { }
        }

        Err(CompileErr(e.loc(), format!("typeapplysynth: don't know what to do with: {:?} {:?} in context {:?}", typ, e, self)))
    }
}

pub fn typesynth_closed(e: &Expr) -> Result<(Polytype, Context), CompileErr> {
    let (a, gamma) = Context::new(vec![]).typesynth(e)?;
    Ok((gamma.apply(&a), *gamma))
}

// Examples as tests
