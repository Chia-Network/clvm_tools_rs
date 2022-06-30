// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use crate::compiler::types::ast;
use crate::compiler::types::astfuns;
use crate::compiler::types::namegen;
use crate::compiler::types::context;

trait TypeTheory {
    pub fn subtype(&self, typ1: Polytype, typ2: Polytype) -> Self;
    pub fn instantiate_l(&self, alpha: TVar, a: Polytype) -> Self;
    pub fn instantiate_r(&self, a: Polytype, alpha: TVar) -> Self;
    pub fn typecheck(&self, expr: Expr, typ: Polytype) -> Self;
    pub fn typesynth(&self, expr: Expr) -> (Polytype, Self);
    pub fn typeapplysynth(&self, typ: Polytype, e: Expr) -> (Polytype, Self);
}

impl TypeTheory for Context {
    // | Algorithmic subtyping:
    //   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
    pub fn subtype(&self, typ1: Polytype, typ2: Polytype) -> Result<Self, CompileErr> {
        let _ = self.checkwftype(typ1)?;
        let _ = self.checkwftype(typ2)?;
        match (typ1, typ2) {
            (TVar(alpha), TVar(alphaprime)) => {
                if alpha == alphaprime {
                    return Ok(self.clone());
                }
            },
            (TUnit, TUnit) => { return Ok(self.clone()); },
            (TExists(alpha), TExists(alphaprime)) => {
                if alpha == alphaprime && self.existentials().elem(alpha) {
                    return Ok(self.clone());
                }
            },
            (TFun(a1,a2), TFun(b1,b2)) => {
                let theta = self.subtype(b1,a1)?;
                theta.subtype(theta.apply(a2), theta.apply(b2))
            },

            // <:forallR
            (a, TForall(alpha,b)) => {
                let alphaprime = fresh_tvar();
                self.snoc(
                    CForall(alphaprime.clone())
                ).subtype(
                    a,
                    typeSubst(TVar(alphaprime.clone()), alpha, b)
                ).dropMarker(CForall(alphaprime.clone()))
            },

            // <:forallL
            (TForall(alpha,a), b) => {
                let alphaprime = fresh_tvar();
                self.appends(
                    vec![
                        CMarker(alphaprime.clone()),
                        CExists(alphaprime.clone())
                    ]
                ).subtype(
                    typeSubst(
                        TExists(alphaprime.clone()),
                        alpha.clone(),
                        a.clone()
                    ),
                    b.clone()
                ).dropMarker(CForall(alphaprime.clone()))
            },

            // <:instantiateL
            (TExists(alpha), a) => {
                if gamma.existentials().elem(alpha) &&
                    !free_tvars(a).member(alpha) {
                    return gamma.instantiate_l(alpha, a);
                }
            },

            // <:instantiateR
            (a, TExists(alpha)) => {
                if gamma.existentials().elem(alpha) &&
                    !free_tvars(a).member(alpha) {
                    return gamma.instantiate_r(a, alpha);
                }
            }
        }

        Err(CompileErr(typ1.loc(), format!("subtype, don't know what to do with: {:?} {:?} in context {:?}", typ1, typ2, self)))
    }

    // | Algorithmic instantiation (left):
    //   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
    pub fn instantiate_l(&self, alpha: TVar, a: Polytype) -> Result<Self, CompileErr> {
        let _ = self.checkwftype(TExists(alpha))?;
        let _ = self.checkwftype(a)?;
        match monotype(a).and_then(|mta| self.solve(alpha, mta)) {
            Some(gamamprime) => Ok(gammaprime),
            Nothing => {
                match a {
                    // InstLReach
                    TExists(beta) => {
                        if self.ordered(alpha,beta) {
                            self.solve(beta, TExists(alpha)).map(|x| Ok(x.clone())).unwrap_or_else(|| Err(CompileErr(alpha.loc(), format!("no solution in instantiate_l for {:?} {:?} in context {:?}", alpha, a, self))))
                        } else {
                            self.solve(alpha, TExists(beta)).map(|x| Ok(x.clone())).unwrap_or_else(|| Err(CompileErr(alpha.loc(), format!("no solution in instantiate_l for {:?} {:?} in context {:?}", a, alpha, self))))
                        }
                    },
                    // InstLArr
                    TFun(a1, a2) => {
                        let alpha1 = fresh_tvar();
                        let alpha2 = fresh_tvar();
                        let rcontext = context(vec![
                            CExists(alpha2.clone()),
                            CExists(alpha1.clone()),
                            CExistsSolved(
                                alpha.clone(),
                                TFun(
                                    TExists(alpha1.clone()),
                                    TExists(alpha2.clone())
                                )
                            )
                        ]);
                        let theta = (gamma.insert_at(CExists(alpha.clone()), rcontext)).
                            instantiate_r(a1, alpha)?;
                        theta.instantiate_l(alpha2.clone(), theta.apply(a2))
                    },
                    // InstLAIIR
                    TForall(beta, b) => {
                        let betaprime = fresh_tvar();
                        (gamma.appends(vec![CForall(betaprime.clone())])).instaniate_l(alpha, typeSubst(TVar(betaprime.clone()), beta.clone(), b.clone())).dropMarker(CForall(betaprime.clone()))
                    }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_l: {:?} {:?} {:?}", gamma, alpha, a)))
    }

    // | Algorithmic instantiation (right):
    //   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
    pub fn instantiate_r(&self, a: Polytype, alpha: TVar) -> Self {
        let _ = self.checkwftype(a);
        let _ = self.checkwftype(TExists(alpha));
        match monotype(a).and_then(|mta| self.solve(alpha,mta)) {
            Some(gammaprime) => { return Ok(gammaprime); },
            None => {
                // InstRReach
                match a {
                    TExists(beta) => {
                        if self.ordered(alpha.clone(), beta.clone()) {
                            match self.solve(beta, TExists(alpha.clone())) {
                                Some(res) => { return Ok(res); },
                                None => {
                                    return Err(CompileErr(alpha.loc(), format!("no solution in instantiate_r: {:?} {:?} with context {:?}", a, alpha, gamma)));
                                }
                            }
                        }
                    },
                    TFun(a1, a2) => {
                        let alpha1 = fresh_tvar();
                        let alpha2 = fresh_tvar();
                        let rcontext = context(vec![
                            CExists(alpha2.clone()),
                            CExists(alpha1.clone()),
                            CExistsSolved(alpha.clone(), TFun(TExists(alpha1.clone(), alpha2.clone())))
                        ]);
                        let theta = (gamma.insert_at(CExists(alpha.clone()), rcontext)).instantiate_l(alpha1.clone(), a1.clone());
                        return theta.instantiate_r(theta.apply(a2.clone()), alpha2.clone());
                    },
                    TForall(beta, b) => {
                        let betaprime = fresh_tvar();
                        (self.appends(vec![
                            CMarker(betaprime),
                            CExists(betaprime),
                        ])).instantiate_r(
                            typeSubst(
                                TExists(betaprime), beta, b),
                            alpha
                        ).dropMarker(CMarker(betaprime))
                    }
                }
            }
        }

        Err(CompileErr(alpha.loc(), format!("The impossible happened! instantiate_r: {:?} {:?} {:?}", gamma, a, alpha)))
    }

    // | Type checking:
    //   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
    pub fn typecheck(&self, expr: Expr, typ: Polytype) -> Self {
        let _ = self.checkwftype(typ)?;
        match (expr, typ) {
            // 1I
            (EUnit, EUnit) => Ok(self.clone()),
            // ForallI
            (e, TForall(alpha, e)) => {
                let alphaprime = fresh_tvar();
                self.snoc(CForall(alphaprime)).typecheck(e, typeSubst(TVar(alphaprime.clone()), alpha, a)).dropMarker(CForall(alphaprime.clone()))
            },
            // ->I
            (EAbs(x,e), TFun(a,b)) => {
                let xprime = fresh_var();
                self.snoc(CVar(xprime.clone(),a.clone())).typecheck(subst(EVar(xprime.clone()), x.clone(), e.clone()), b.clone()).dropMarker(CVar(xprime.clone(), a.clone()))
            },
            // Sub
            (e, b) => {
                let (a, theta) = self.typesynth(e);
                theta.subtype(theta.apply(a), theta.apply(b))
            }
        }
    }

    // | Type synthesising:
    //   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
    pub fn typesynth(&self, expr: Expr) -> Result<Polytype, Self> {
        let _ = self.checkwf();
        match expr {
            // Var
            EVar(x) => {
                return gamma.find_var_type(x).map(|ty| {
                    Ok(ty)
                }).unwrap_or_else(|| {
                    Err(CompileErr(expr.loc(), format!("typesynth: not in scope {:?} in context {:?}", expr, gamma)))
                });
            },

            // Anno
            EAnno(e,a) => {
                let delta = self.typecheck(e,a)?;
                return Ok((a, delta));
            },

            // 1I=>
            EUnit => { return (TUnit, self.clone()); },

            // ->I=> Original rule
            EAbs(x,e) => {
                let xprime = fresh_var();
                let alpha = fresh_tvar();
                let beta = fresh_tvar();
                let delta = gamma.appends(vec![
                    CExists(alpha.clone()),
                    CExists(beta.clone()),
                    CVar(xprime.clone(),TExists(alpha.clone()))
                ]).typecheck(subst(EVar(xprime.clone()),x.clone(),e.clone()), TExists(beta.clone())).dropMarker(CVar(xprime.clone(), TExists(alpha.clone)))?;
                return Ok((TFun(TExists(alpha.clone()),TExists(beta.clone())), delta));
            }
            // ->E
            EApp(e1,e2) => {
                let (a, theta) = gamma.typesynth(e1)?;
                theta.typeapplysynth(theta.apply(a), e2)
            }
        }
    }

    pub fn typeapplysynth(&self, typ: Polytype, e: Expr) -> Result<(Polytype, Self), CompileErr> {
        let _ = gamma.checkfwtype(typ)?;
        match typ {
            // ForallApp
            TForall(alpha,a) => {
                // Do alpha conversion to avoid clashes
                let alphaprime = fresh_tvar();
                return gamma.snoc(CExists(alphaprime.clone())).typeapplysynth(typeSubst(TExists(alphaprime.clone()), alpha.clone(), a.clone()), e);
            },

            // alpha^App
            TExists(alpha) => {
                let alpha1 = fresh_tvar();
                let alpha2 = fresh_tvar();
                let rcontext = context(vec![
                    CExists(alpha2.clone()),
                    CExists(alpha1.clone()),
                    CExistsSolved(alpha.clone(), TFun(TExists(alpha1.clone()), TExists(alpha2.clone())))
                ]);
                let delta = (gamma.insert_at(CExists(alpha.clone()), rcontext)).typecheck(e.clone(), TExists(alpha1.clone()))?;
                return Ok((TExists(alpha2.clone()), delta));
            },

            // ->App
            TFun(a, c) => {
                let delta = gamma.typecheck(e,a)?;
                return Ok((c, delta));
            }
        }

        Err(CompileErr(e.loc(), format!("typeapplysynth: don't know what to do with: {:?} {:?} in context {:?}", typ, e, gamma)))
    }
}

pub fn typesynth_closed(e: Expr) -> (Polytype, Context) {
    let (a, gamma) = Context::new().typesynth(e);
    (gamma.apply(a), gamma)
}

// Examples as tests
