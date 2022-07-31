// Based on MIT licensed code from
// https://github.com/kwanghoon/bidi

use log::debug;
use std::borrow::Borrow;
use std::iter;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use num_bigint::ToBigInt;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::srcloc::HasLoc;
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{
    Context, ContextElim, Expr, Monotype, Polytype, Type, TypeVar, CONTEXT_INCOMPLETE, TYPE_POLY,
};
use crate::compiler::types::astfuns::{
    free_tvars, monotype, polytype, tforalls, type_subst, type_substs,
};
use crate::compiler::types::context::subst;
use crate::compiler::types::context::HasElem;
use crate::compiler::types::namegen::{fresh_tvar, fresh_var};

lazy_static! {
    pub static ref INDENT_LEVEL: AtomicUsize = AtomicUsize::new(0);
}

const ORIGINAL: bool = true;

fn indented<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    INDENT_LEVEL.fetch_add(1, Ordering::SeqCst);
    let res = f();
    INDENT_LEVEL.fetch_add(usize::MAX, Ordering::SeqCst);
    res
}

fn i() -> String {
    let count = INDENT_LEVEL.fetch_add(0, Ordering::SeqCst);
    iter::repeat(' ').take(count * 3).collect()
}

pub trait TypeTheory {
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr>;
    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr>;
    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr>;
    fn typeapplysynth(&self, typ: &Polytype, e: &Expr)
        -> Result<(Polytype, Box<Self>), CompileErr>;
    fn reify(&self, typ: &Polytype) -> Polytype;
}

impl Context {
    fn increase_type_specificity(
        &self,
        old: &Monotype,
        tau: &Monotype,
    ) -> Result<Monotype, CompileErr> {
        debug!(
            "combine {} and {} to increase information",
            old.to_sexp().to_string(),
            tau.to_sexp().to_string()
        );
        match (&old, tau) {
            (Type::TNullable(a), Type::TNullable(b)) => {
                debug!("check nullable nullable");
                Ok(Type::TNullable(Rc::new(
                    self.increase_type_specificity(a.borrow(), b.borrow())?,
                )))
            }
            (Type::TNullable(nt), _) => Ok(Type::TNullable(Rc::new(
                self.increase_type_specificity(nt.borrow(), tau)?,
            ))),
            (_, Type::TNullable(nt)) => Ok(Type::TNullable(Rc::new(
                self.increase_type_specificity(old, nt.borrow())?,
            ))),
            (_, Type::TExists(_)) => {
                let r1 = self.reify(&polytype(&old));
                let r2 = self.reify(&polytype(tau));
                self.subtype(&polytype(&r2), &polytype(&r1))?;
                Ok(old.clone())
            }
            (Type::TExists(_), _) => {
                let r1 = self.reify(&polytype(&old));
                let r2 = self.reify(&polytype(tau));
                self.subtype(&polytype(&r2), &polytype(&r1))?;
                Ok(tau.clone())
            }
            (Type::TUnit(_), _) => Ok(Type::TNullable(Rc::new(tau.clone()))),
            (_, Type::TUnit(_)) => Ok(Type::TNullable(Rc::new(old.clone()))),
            (Type::TExec(a), Type::TExec(b)) => Ok(Type::TExec(Rc::new(
                self.increase_type_specificity(a.borrow(), b.borrow())?,
            ))),
            (Type::TPair(a1, b1), Type::TPair(a2, b2)) => Ok(Type::TPair(
                Rc::new(self.increase_type_specificity(a1.borrow(), a2.borrow())?),
                Rc::new(self.increase_type_specificity(b1.borrow(), b2.borrow())?),
            )),
            (Type::TFun(a1, b1), Type::TFun(a2, b2)) => {
                Ok(Type::TFun(
                    // contravariant order
                    Rc::new(self.increase_type_specificity(a2.borrow(), a1.borrow())?),
                    Rc::new(self.increase_type_specificity(b1.borrow(), b2.borrow())?),
                ))
            }
            (_, _) => {
                let r1 = self.reify(&polytype(&old));
                let r2 = self.reify(&polytype(tau));
                self.subtype(&polytype(&r2), &polytype(&r1))?;
                Ok(tau.clone())
            }
        }
    }

    fn increase_specificity(
        &self,
        alpha: &TypeVar,
        tau: &Monotype,
    ) -> Result<Monotype, CompileErr> {
        if let Some(old) = self.find_solved(alpha) {
            self.increase_type_specificity(&old, tau)
        } else {
            Ok(tau.clone())
        }
    }

    // Solve is a place where extensionality comes to a head.
    // We must respect the extensionality rules in bidir section 4.
    // This means "increasing information" in the combined context.
    pub fn solve(&self, alpha: &TypeVar, tau: &Monotype) -> Result<Option<Context>, CompileErr> {
        debug!(
            "solve {} in {}",
            alpha.to_sexp().to_string(),
            self.to_sexp().to_string()
        );
        let new_tau = self.increase_specificity(alpha, tau)?;
        let (gamma_l, gamma_r) = self.inspect_context(alpha);
        debug!(
            "solve {} {} in {} || {}",
            alpha.to_sexp().to_string(),
            new_tau.to_sexp().to_string(),
            gamma_l.to_sexp().to_string(),
            gamma_r.to_sexp().to_string()
        );
        let fa: ContextElim<CONTEXT_INCOMPLETE> = ContextElim::CForall(alpha.clone());
        if gamma_l.typewf(&tau) {
            let mut gammaprime: Vec<ContextElim<CONTEXT_INCOMPLETE>> = gamma_r
                .0
                .iter()
                .filter(|x| *x != &fa)
                .map(|x| x.clone())
                .collect();
            let gamma_l_copy: Vec<ContextElim<CONTEXT_INCOMPLETE>> = gamma_l.0.clone();
            gammaprime.push(ContextElim::CExistsSolved(alpha.clone(), new_tau.clone()));
            gammaprime.append(&mut gamma_l_copy.clone());
            let ctx = Context::new_wf(gammaprime.clone());
            Ok(Some(ctx))
        } else {
            Ok(None)
        }
    }

    // | Algorithmic subtyping:
    //   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
    //
    // Given some morphism Delta on Gamma, B element Delta checks as A in Gamma
    fn subtype_(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr> {
        let texists_guard = |a: &Polytype, alpha: &TypeVar| {
            let exi = self.existentials();
            exi.elem(alpha) && !free_tvars(a).contains(alpha)
        };

        let _ = self.checkwftype(typ1)?;
        let _ = self.checkwftype(typ2)?;
        match (typ1, typ2) {
            (Type::TVar(alpha), Type::TVar(alphaprime)) => {
                debug!("case 1");
                if alpha == alphaprime {
                    return Ok(Box::new(self.clone()));
                }
            }
            // All types check as any
            (_, Type::TAny(_)) => {
                return Ok(Box::new(self.clone()));
            }
            // Any checks as any type
            (Type::TAny(_), _) => {
                return Ok(Box::new(self.clone()));
            }
            (Type::TUnit(_), Type::TUnit(_)) => {
                debug!("case 2");
                return Ok(Box::new(self.clone()));
            }
            (Type::TAtom(_, _), Type::TAtom(_, None)) => {
                debug!("case Atom");
                return Ok(Box::new(self.clone()));
            }
            (Type::TAtom(_, x), Type::TAtom(_, y)) => {
                debug!("case Atom with sizes");
                if x == y {
                    return Ok(Box::new(self.clone()));
                }
            }
            (Type::TFun(a1, a2), Type::TFun(b1, b2)) => {
                debug!("case 5");
                let theta = self.subtype(b1, a1)?;
                return theta.subtype(&theta.apply(a2), &theta.apply(b2));
            }

            (Type::TNullable(a), Type::TNullable(b)) => {
                debug!("case nullable");
                return self.subtype(a, b);
            }

            (Type::TUnit(_), Type::TNullable(_)) => {
                return Ok(Box::new(self.clone()));
            }

            (a, Type::TNullable(b)) => {
                return self.subtype(a, b);
            }

            (Type::TExec(a), Type::TExec(b)) => {
                debug!("exec");
                return self.subtype(a, b);
            }

            (Type::TPair(a1, a2), Type::TPair(b1, b2)) => {
                debug!("case 6");
                let theta = self.subtype(a1, b1)?;
                return theta.subtype(a2, b2);
            }

            // <:forallR
            (a, Type::TForall(alpha, b)) => {
                let alphaprime = fresh_tvar(typ2.loc());
                let subst_res = type_subst(&Type::TVar(alphaprime.clone()), &alpha.clone(), b);
                debug!("case 7 a' = {}", alphaprime.to_sexp().to_string());
                return self
                    .drop_marker(ContextElim::CForall(alphaprime.clone()), |gamma| {
                        gamma.subtype(a, &subst_res)
                    })
                    .map(|x| Box::new(x));
            }

            // <:forallL
            (Type::TForall(alpha, a), b) => {
                debug!("case 8");
                let alphaprime = fresh_tvar(typ1.loc());
                let subst_res = type_subst(
                    &Type::TExists(alphaprime.clone()),
                    &alpha.clone(),
                    a.borrow(),
                );
                return self
                    .drop_marker(ContextElim::CMarker(alphaprime.clone()), |gamma| {
                        gamma
                            .appends_wf(vec![ContextElim::CExists(alphaprime.clone())])
                            .subtype(&subst_res, &b.clone())
                    })
                    .map(|x| Box::new(x));
            }

            (a, Type::TApp(t1, t2)) => {
                debug!("case TApp");
                if let Some((t, ctx)) = self.newtype::<TYPE_POLY>(t1.borrow(), t2.borrow()) {
                    debug!("new context {}", ctx.to_sexp().to_string());
                    return ctx.subtype(a, &t);
                }
            }

            (Type::TApp(t1, t2), a) => {
                debug!("case reflected TApp");
                if let Some((t, ctx)) = self.newtype::<TYPE_POLY>(t1.borrow(), t2.borrow()) {
                    debug!("new context {}", ctx.to_sexp().to_string());
                    return ctx.subtype(&t, a);
                }
            }

            // <:instantiateL
            (Type::TExists(alpha), a) => {
                debug!("TExists instantiateL");
                // Type.hs line 34
                if let Type::TExists(alphaprime) = a {
                    let exi = self.existentials();
                    if alpha == alphaprime && exi.elem(alpha) {
                        return Ok(Box::new(self.clone()));
                    }
                }

                // Original code: Type.hs line 29 uses a guard
                if !texists_guard(a, alpha) {
                    return Err(CompileErr(a.loc(), "instantiateL TExists".to_string()));
                }

                if let Type::TNullable(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc_wf(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TNullable(Rc::new(Type::TVar(avar.clone()))),
                        ))));
                    }
                }

                if let Type::TExec(aprime) = a {
                    if let Type::TVar(avar) = aprime.borrow() {
                        return Ok(Box::new(self.snoc_wf(ContextElim::CExistsSolved(
                            alpha.clone(),
                            Type::TExec(Rc::new(Type::TVar(avar.clone()))),
                        ))));
                    }
                }

                let exi = self.existentials();
                if exi.elem(alpha) && !free_tvars(a).contains(alpha) {
                    return self.instantiate_l(alpha, a);
                }
            }

            // <:instantiateR
            (a, Type::TExists(alpha)) => {
                // Original code: Type.hs line 29 uses a guard
                debug!(
                    "right hand TExists {} {}",
                    a.to_sexp().to_string(),
                    alpha.to_sexp().to_string()
                );
                if !texists_guard(a, alpha) {
                    return Err(CompileErr(a.loc(), "instantiateR TExists".to_string()));
                }

                return self.instantiate_r(a, alpha);
            }

            _ => {
                debug!("subtype, didn't match");
            }
        }

        Err(CompileErr(
            typ1.loc(),
            format!(
                "subtype, don't know what to do with: {} {} in context {}",
                typ1.to_sexp().to_string(),
                typ2.to_sexp().to_string(),
                self.to_sexp().to_string()
            ),
        ))
    }

    // | Algorithmic instantiation (left):
    //   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
    fn instantiate_l_(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(&Type::TExists(alpha.clone()))?;
        let _ = self.checkwftype(a)?;
        let prev_monotype_a = if let Some(mta) = monotype(a) {
            self.solve(alpha, &mta)?
        } else {
            None
        };

        match prev_monotype_a {
            Some(gammaprime) => {
                return Ok(Box::new(gammaprime));
            }
            None => {
                debug!("L match {}", a.to_sexp().to_string());
                match a {
                    // InstLReach
                    Type::TExists(beta) => {
                        if self.ordered(alpha, beta) {
                            debug!("InstLReach AB");
                            return self
                                .solve(beta, &Type::TExists(alpha.clone()))?
                                .map(|x| Ok(Box::new(x.clone())))
                                .unwrap_or_else(|| {
                                    Err(CompileErr(
                                        alpha.loc(),
                                        format!(
                                            "no solution in instantiate_l for {} {} in context {}",
                                            alpha.to_sexp().to_string(),
                                            a.to_sexp().to_string(),
                                            self.to_sexp().to_string()
                                        ),
                                    ))
                                });
                        } else {
                            debug!("InstLReach BA");
                            return self
                                .solve(alpha, &Type::TExists(beta.clone()))?
                                .map(|x| Ok(Box::new(x.clone())))
                                .unwrap_or_else(|| {
                                    Err(CompileErr(
                                        alpha.loc(),
                                        format!(
                                            "no solution in instantiate_l for {} {} in context {}",
                                            a.to_sexp().to_string(),
                                            alpha.to_sexp().to_string(),
                                            self.to_sexp().to_string()
                                        ),
                                    ))
                                });
                        }
                    }
                    // InstLArr
                    Type::TFun(a1, a2) => {
                        debug!("InstLArr");
                        let alpha1 = fresh_tvar(a1.loc());
                        let alpha2 = fresh_tvar(a2.loc());
                        let rcontext = Context::new_wf(vec![
                            ContextElim::CExistsSolved(
                                alpha.clone(),
                                Type::TFun(
                                    Rc::new(Type::TExists(alpha1.clone())),
                                    Rc::new(Type::TExists(alpha2.clone())),
                                ),
                            ),
                            ContextElim::CExists(alpha2.clone()),
                            ContextElim::CExists(alpha1.clone()),
                        ]);
                        let theta = (self.insert_at(alpha, rcontext)).instantiate_r(a1, alpha)?;
                        return theta.instantiate_l(&alpha2, &theta.apply(a2));
                    }
                    // InstLAIIR
                    Type::TForall(beta, b) => {
                        debug!("InstLArrR");
                        let betaprime = fresh_tvar(beta.loc());
                        let subst_res =
                            type_subst(&Type::TVar(betaprime.clone()), &beta.clone(), b.borrow());
                        return self
                            .drop_marker(ContextElim::CForall(betaprime.clone()), |gamma| {
                                gamma.instantiate_l(alpha, &subst_res)
                            })
                            .map(|x| Box::new(x));
                    }

                    Type::TExec(t) => {
                        debug!("instL TExec");
                        let alpha1 = fresh_tvar(t.loc());
                        let rcontext = Context::new_wf(vec![
                            ContextElim::CExistsSolved(
                                alpha.clone(),
                                Type::TExec(Rc::new(Type::TExists(alpha1.clone()))),
                            ),
                            ContextElim::CExists(alpha1.clone()),
                        ]);
                        return self.insert_at(alpha, rcontext).instantiate_r(t, alpha);
                    }

                    _ => {}
                }
            }
        }

        Err(CompileErr(
            alpha.loc(),
            format!(
                "The impossible happened! instantiate_l: {} {} {}",
                alpha.to_sexp().to_string(),
                a.to_sexp().to_string(),
                self.to_sexp().to_string()
            ),
        ))
    }

    // | Algorithmic instantiation (right):
    //   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
    fn instantiate_r_(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr> {
        let _ = self.checkwftype(a);
        let _ = self.checkwftype(&Type::TExists(alpha.clone()));

        if let Some(mta) = monotype(a) {
            if let Some(gammaprime) = self.solve(alpha, &mta)? {
                debug!("just gamma'");
                return Ok(Box::new(gammaprime));
            }
        }

        // InstRReach
        debug!("match {:?}", a);
        match a {
            Type::TNullable(a1) => {
                debug!("case 1");
                match monotype(a1) {
                    Some(mta) => {
                        return Ok(Box::new(self.appends_wf(vec![
                            ContextElim::CForall(alpha.clone()),
                            ContextElim::CExistsSolved(alpha.clone(), mta),
                        ])));
                    }
                    _ => {
                        return Err(CompileErr(
                            a.loc(),
                            format!("no monotype: {}", a1.to_sexp().to_string()),
                        ));
                    }
                }
            }
            Type::TExec(a1) => {
                debug!("case 2");
                match monotype(a1) {
                    Some(mta) => {
                        return Ok(Box::new(self.appends_wf(vec![
                            ContextElim::CForall(alpha.clone()),
                            ContextElim::CExistsSolved(alpha.clone(), mta),
                        ])));
                    }
                    _ => {
                        return Err(CompileErr(
                            a.loc(),
                            format!("no monotype: {}", a1.to_sexp().to_string()),
                        ));
                    }
                }
            }
            Type::TPair(a1, a2) => {
                debug!("case 3");
                let alpha1 = fresh_tvar(a1.loc());
                let alpha2 = fresh_tvar(a2.loc());
                match monotype(a1).and_then(|mta| monotype(a2).map(|mtb| (mta, mtb))) {
                    Some((mta, mtb)) => {
                        return Ok(Box::new(self.appends_wf(vec![
                            ContextElim::CExistsSolved(alpha1.clone(), mta),
                            ContextElim::CExistsSolved(alpha2.clone(), mtb),
                        ])));
                    }
                    _ => {
                        return Err(CompileErr(
                            a.loc(),
                            format!(
                                "no monotype: {} or {}",
                                a1.to_sexp().to_string(),
                                a2.to_sexp().to_string()
                            ),
                        ));
                    }
                }
            }
            Type::TExists(beta) => {
                debug!("texists {}", beta.to_sexp().to_string());
                if self.ordered(alpha, beta) {
                    match self.solve(beta, &Type::TExists(alpha.clone()))? {
                        Some(res) => {
                            return Ok(Box::new(res));
                        }
                        None => {
                            return Err(CompileErr(
                                alpha.loc(),
                                format!(
                                    "no solution in instantiate_r: {} {} with context {}",
                                    a.to_sexp().to_string(),
                                    alpha.to_sexp().to_string(),
                                    self.to_sexp().to_string()
                                ),
                            ));
                        }
                    }
                } else {
                    match self.solve(alpha, &Type::TExists(beta.clone()))? {
                        Some(res) => {
                            return Ok(Box::new(res));
                        }
                        None => {
                            return Err(CompileErr(
                                beta.loc(),
                                format!(
                                    "no solution in instantiate_r: {} {} with context {:?}",
                                    a.to_sexp().to_string(),
                                    alpha.to_sexp().to_string(),
                                    self
                                ),
                            ));
                        }
                    }
                }
            }
            Type::TFun(a1, a2) => {
                debug!("case 4");
                let alpha1 = fresh_tvar(a1.loc());
                let alpha2 = fresh_tvar(a2.loc());
                let rcontext = Context::new_wf(vec![
                    ContextElim::CExists(alpha2.clone()),
                    ContextElim::CExists(alpha1.clone()),
                    ContextElim::CExistsSolved(
                        alpha.clone(),
                        Type::TFun(
                            Rc::new(Type::TExists(alpha1.clone())),
                            Rc::new(Type::TVar(alpha2.clone())),
                        ),
                    ),
                ]);
                let theta =
                    (self.insert_at(alpha, rcontext)).instantiate_l(&alpha1, a1.borrow())?;
                return theta.instantiate_r(&theta.apply(a2.borrow()), &alpha2);
            }
            Type::TForall(beta, b) => {
                debug!("case 5");
                let betaprime = fresh_tvar(beta.loc());
                let subst_res = type_subst(&Type::TExists(betaprime.clone()), &beta.clone(), b);
                return self
                    .drop_marker(ContextElim::CMarker(betaprime.clone()), |gamma| {
                        debug!("instantate_r from drop_marker");
                        gamma
                            .appends_wf(vec![ContextElim::CExists(betaprime.clone())])
                            .instantiate_r(&subst_res, alpha)
                    })
                    .map(|x| Box::new(x));
            }
            _ => {}
        }

        Err(CompileErr(
            alpha.loc(),
            format!(
                "The impossible happened! instantiate_r: {} {} {}",
                self.to_sexp().to_string(),
                a.to_sexp().to_string(),
                alpha.to_sexp().to_string()
            ),
        ))
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
                debug!("tforall");
                let alphaprime = fresh_tvar(typ.loc());
                let subst_res = type_subst(&Type::TVar(alphaprime.clone()), &alpha.clone(), a);
                return self
                    .drop_marker(ContextElim::CForall(alphaprime.clone()), |gamma| {
                        gamma.typecheck(e, &subst_res)
                    })
                    .map(|x| Box::new(x));
            }

            (Expr::EUnit(_), Type::TNullable(_)) => Ok(Box::new(self.clone())),

            // ->I
            (Expr::EAbs(x, e), Type::TFun(a, b)) => {
                debug!("eabs tfun");
                let xprime = fresh_var(expr.loc());
                let a_borrowed: &Polytype = a.borrow();
                let b_borrowed: &Polytype = b.borrow();
                let e_borrowed: &Expr = e.borrow();
                let subst_res = subst(&Expr::EVar(xprime.clone()), x.clone(), e_borrowed);

                self.drop_marker(
                    ContextElim::CVar(xprime.clone(), a_borrowed.clone()),
                    |gamma| gamma.typecheck(&subst_res, b_borrowed),
                )
                .map(|x| Box::new(x))
            }
            // Sub
            (e, b) => {
                debug!("// Sub");
                let (a, theta) = self.typesynth(e)?;
                let aprime = theta.reify(&a);
                debug!(
                    "typesynth {} = {}",
                    e.to_sexp().to_string(),
                    aprime.to_sexp().to_string()
                );
                return theta.subtype(&theta.apply(&aprime), &theta.apply(b));
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
                return self
                    .find_var_type(x)
                    .map(|ty| Ok((ty, Box::new(self.clone()))))
                    .unwrap_or_else(|| {
                        Err(CompileErr(
                            expr.loc(),
                            format!(
                                "typesynth: not in scope {} in context {}",
                                expr.to_sexp().to_string(),
                                self.to_sexp().to_string()
                            ),
                        ))
                    });
            }

            // Anno
            Expr::EAnno(e, a) => {
                let delta = self.typecheck(e, a)?;
                return Ok((a.clone(), delta));
            }

            // 1I=>
            Expr::EUnit(l) => {
                return Ok((Type::TUnit(l.clone()), Box::new(self.clone())));
            }

            Expr::ELit(l, n) => {
                let atom_size = if n == &32_u32.to_bigint().unwrap() {
                    Some(n.clone())
                } else {
                    None
                };
                return Ok((Type::TAtom(l.clone(), atom_size), Box::new(self.clone())));
            }
            // ->I=> Original rule
            Expr::EAbs(x, e) => {
                if ORIGINAL {
                    let xprime = fresh_var(x.loc());
                    let alpha = fresh_tvar(x.loc());
                    let beta = fresh_tvar(x.loc());
                    let e_borrowed: &Expr = e.borrow();

                    let subst_res = subst(&Expr::EVar(xprime.clone()), x.clone(), e_borrowed);

                    debug!(
                        "eabs {} {}",
                        x.to_sexp().to_string(),
                        e.to_sexp().to_string()
                    );
                    self.appends_wf(vec![
                        ContextElim::CExists(beta.clone()),
                        ContextElim::CExists(alpha.clone()),
                    ])
                    .drop_marker(
                        ContextElim::CVar(xprime.clone(), Type::TExists(alpha.clone())),
                        |gamma| {
                            debug!("gamma is {}", gamma.to_sexp().to_string());
                            gamma.typecheck(&subst_res, &Type::TExists(beta.clone()))
                        },
                    )
                    .map(|delta| {
                        debug!("delta is {}", delta.to_sexp().to_string());
                        (
                            Type::TFun(Rc::new(Type::TExists(alpha)), Rc::new(Type::TExists(beta))),
                            Box::new(delta),
                        )
                    })
                } else {
                    let xprime = fresh_var(x.loc());
                    let alpha = fresh_tvar(x.loc());
                    let beta = fresh_tvar(e.loc());
                    let e_borrowed: &Expr = e.borrow();
                    let subst_res = subst(&Expr::EVar(xprime.clone()), x.clone(), e_borrowed);

                    let (delta, deltaprime) = self
                        .appends_wf(vec![
                            ContextElim::CVar(xprime.clone(), Type::TExists(alpha.clone())),
                            ContextElim::CExists(alpha.clone()),
                            ContextElim::CExists(beta.clone()),
                        ])
                        .break_marker(ContextElim::CMarker(alpha.clone()), |gamma| {
                            gamma.typecheck(&subst_res, &Type::TExists(beta.clone()))
                        })?;

                    debug!("delta  {}", delta.to_sexp().to_string());
                    debug!("delta' {}", deltaprime.to_sexp().to_string());

                    let tau = deltaprime.apply(&Type::TFun(
                        Rc::new(Type::TExists(alpha.clone())),
                        Rc::new(Type::TExists(beta.clone())),
                    ));

                    debug!("tau   {}", tau.to_sexp().to_string());

                    let evars = deltaprime.unsolved();
                    debug!("unsolved:");
                    let uvars: Vec<(Polytype, TypeVar)> = evars
                        .iter()
                        .map(|e| (Type::TVar(e.clone()), fresh_tvar(x.loc())))
                        .collect();
                    for e in uvars.iter() {
                        debug!(
                            " - {} = {}",
                            e.1.to_sexp().to_string(),
                            e.0.to_sexp().to_string()
                        );
                    }
                    let tfa = tforalls(evars, type_substs(uvars, tau));
                    Ok((tfa, Box::new(delta)))
                }
            }

            // ->E
            Expr::EApp(e1, e2) => {
                let (a, theta) = self.typesynth(e1)?;
                theta.typeapplysynth(&theta.apply(&a), e2)
            }
        }
    }

    fn typeapplysynth_(
        &self,
        typ: &Polytype,
        expr: &Expr,
    ) -> Result<(Polytype, Box<Self>), CompileErr> {
        let _ = self.checkwftype(typ)?;

        let resolve_inner_type = |t: &Polytype, delta: &Context| {
            if let Type::TExists(tv) = t.borrow() {
                if let Some(tau) = delta.find_solved(tv).as_ref().map(|t| polytype(t)) {
                    return Some(tau);
                }
            }

            None
        };

        debug!("do match");
        match typ {
            // ForallApp
            Type::TForall(alpha, a) => {
                // Do alpha conversion to avoid clashes
                let alphaprime = fresh_tvar(typ.loc());
                return self
                    .snoc_wf(ContextElim::CExists(alphaprime.clone()))
                    .typeapplysynth(
                        &type_subst(&Type::TExists(alphaprime.clone()), &alpha.clone(), a),
                        expr,
                    );
            }

            // alpha^App
            Type::TExists(alpha) => {
                let alpha1 = fresh_tvar(typ.loc());
                let alpha2 = fresh_tvar(typ.loc());
                let rcontext = Context::new_wf(vec![
                    ContextElim::CExistsSolved(
                        alpha.clone(),
                        Type::TFun(
                            Rc::new(Type::TExists(alpha1.clone())),
                            Rc::new(Type::TExists(alpha2.clone())),
                        ),
                    ),
                    ContextElim::CExists(alpha2.clone()),
                    ContextElim::CExists(alpha1.clone()),
                ]);
                let delta = (self.insert_at(alpha, rcontext))
                    .typecheck(expr, &Type::TExists(alpha1.clone()))?;
                return Ok((Type::TExists(alpha2.clone()), delta));
            }

            // ->App
            Type::TFun(a, c) => {
                let c_borrowed: &Polytype = c.borrow();
                let delta = self.typecheck(expr, a)?;
                match c_borrowed {
                    Type::TNullable(t) => {
                        if let Some(tau) = resolve_inner_type(t, delta.borrow()) {
                            return Ok((Type::TNullable(Rc::new(tau.clone())), delta));
                        }
                    }
                    Type::TExec(t) => {
                        if let Some(tau) = resolve_inner_type(t, delta.borrow()) {
                            return Ok((Type::TExec(Rc::new(tau.clone())), delta));
                        }
                    }
                    Type::TPair(x, y) => {
                        let tau = resolve_inner_type(x, delta.borrow())
                            .map(|x| Rc::new(x))
                            .unwrap_or_else(|| x.clone());
                        let sigma = resolve_inner_type(y, delta.borrow())
                            .map(|y| Rc::new(y))
                            .unwrap_or_else(|| y.clone());

                        return Ok((Type::TPair(tau.clone(), sigma.clone()), delta));
                    }
                    _ => {}
                }

                return Ok((c_borrowed.clone(), delta));
            }

            Type::TNullable(t) => {
                let delta = self.typecheck(expr, &Type::TNullable(t.clone()))?;
                return Ok((Type::TNullable(t.clone()), delta));
            }

            Type::TExec(t) => {
                let delta = self.typecheck(expr, &Type::TExec(t.clone()))?;
                return Ok((Type::TExec(t.clone()), delta));
            }

            _ => {}
        }

        Err(CompileErr(
            expr.loc(),
            format!(
                "typeapplysynth: don't know what to do with: {} {} in context {}",
                typ.to_sexp().to_string(),
                expr.to_sexp().to_string(),
                self.to_sexp().to_string()
            ),
        ))
    }
}

impl TypeTheory for Context {
    fn subtype(&self, typ1: &Polytype, typ2: &Polytype) -> Result<Box<Self>, CompileErr> {
        indented(|| {
            debug!(
                "{}subtype {} {}",
                i(),
                typ1.to_sexp().to_string(),
                typ2.to_sexp().to_string()
            );
            let res = self.subtype_(typ1, typ2);
            match &res {
                Ok(v) => {
                    debug!(
                        "{}subtype => {}",
                        i(),
                        /*self.to_sexp().to_string(),*/ v.to_sexp().to_string()
                    );
                }
                Err(e) => {
                    debug!(
                        "{}subtype {} {} in {} => {:?}",
                        i(),
                        typ1.to_sexp().to_string(),
                        typ2.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        e
                    );
                }
            }
            res
        })
    }

    fn instantiate_l(&self, alpha: &TypeVar, a: &Polytype) -> Result<Box<Self>, CompileErr> {
        indented(|| {
            debug!(
                "{}instantiate_l {} {} in {}",
                i(),
                alpha.to_sexp().to_string(),
                a.to_sexp().to_string(),
                self.to_sexp().to_string()
            );
            let res = self.instantiate_l_(alpha, a);
            match &res {
                Ok(v) => {
                    debug!(
                        "{}instantiate_l {} {} => {}",
                        i(),
                        alpha.to_sexp().to_string(),
                        a.to_sexp().to_string(),
                        /*self.to_sexp().to_string(),*/ v.to_sexp().to_string()
                    );
                }
                Err(e) => {
                    debug!(
                        "{}instantiate_l {} {} in {} => {:?}",
                        i(),
                        alpha.to_sexp().to_string(),
                        a.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        e
                    );
                }
            }
            res
        })
    }

    fn instantiate_r(&self, a: &Polytype, alpha: &TypeVar) -> Result<Box<Self>, CompileErr> {
        indented(|| {
            debug!(
                "{}instantiate_r {} {} in {}",
                i(),
                a.to_sexp().to_string(),
                alpha.to_sexp().to_string(),
                self.to_sexp().to_string()
            );
            let res = self.instantiate_r_(a, alpha);
            match &res {
                Ok(v) => {
                    debug!(
                        "{}instantiate_r {} {} => {}",
                        i(),
                        a.to_sexp().to_string(),
                        alpha.to_sexp().to_string(),
                        /*self.to_sexp().to_string(),*/ v.to_sexp().to_string()
                    );
                }
                Err(e) => {
                    debug!(
                        "{}instantiate_r {} {} in {} => {:?}",
                        i(),
                        a.to_sexp().to_string(),
                        alpha.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        e
                    );
                }
            }
            res
        })
    }

    fn typecheck(&self, expr: &Expr, typ: &Polytype) -> Result<Box<Self>, CompileErr> {
        indented(|| {
            debug!(
                "{}typecheck {} {}",
                i(),
                expr.to_sexp().to_string(),
                typ.to_sexp().to_string()
            );
            let res = self.typecheck_(expr, typ);
            match &res {
                Ok(v) => {
                    debug!(
                        "{}typecheck {} {} => {}",
                        i(),
                        expr.to_sexp().to_string(),
                        typ.to_sexp().to_string(),
                        /*self.to_sexp().to_string(),*/ v.to_sexp().to_string()
                    );
                }
                Err(e) => {
                    debug!(
                        "{}typecheck {} {} in {} => {:?}",
                        i(),
                        expr.to_sexp().to_string(),
                        typ.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        e
                    );
                }
            }
            res
        })
    }

    fn typesynth(&self, expr: &Expr) -> Result<(Polytype, Box<Self>), CompileErr> {
        indented(|| {
            debug!(
                "{}typesynth {} in {}",
                i(),
                expr.to_sexp().to_string(),
                self.to_sexp().to_string()
            );
            let res = self.typesynth_(expr);
            match &res {
                Ok((t, v)) => {
                    debug!(
                        "{}typesynth {} => ({} {})",
                        i(),
                        expr.to_sexp().to_string(),
                        /*self.to_sexp().to_string(),*/ t.to_sexp().to_string(),
                        v.to_sexp().to_string()
                    );
                }
                Err(e) => {
                    debug!(
                        "{}typesynth {} in {} => {:?}",
                        i(),
                        expr.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        e
                    );
                }
            }
            res
        })
    }

    fn typeapplysynth(
        &self,
        typ: &Polytype,
        e: &Expr,
    ) -> Result<(Polytype, Box<Self>), CompileErr> {
        indented(|| {
            debug!(
                "{}typeapplysynth {} {} in {}",
                i(),
                typ.to_sexp().to_string(),
                e.to_sexp().to_string(),
                self.to_sexp().to_string()
            );
            let res = self.typeapplysynth_(typ, e);
            match &res {
                Ok((t, v)) => {
                    debug!(
                        "{}typeapplysynth {} {} => ({} {})",
                        i(),
                        typ.to_sexp().to_string(),
                        e.to_sexp().to_string(),
                        /*self.to_sexp().to_string(),*/ t.to_sexp().to_string(),
                        v.to_sexp().to_string()
                    );
                }
                Err(err) => {
                    debug!(
                        "{}typeapplysynth {} {} in {} => {:?}",
                        i(),
                        typ.to_sexp().to_string(),
                        e.to_sexp().to_string(),
                        self.to_sexp().to_string(),
                        err
                    );
                }
            }
            res
        })
    }

    // Perform all available substitutions
    fn reify(&self, typ: &Polytype) -> Polytype {
        match &typ {
            Type::TExists(tv) => self
                .find_solved(tv)
                .as_ref()
                .map(|x| self.reify(&polytype(x)))
                .unwrap_or_else(|| typ.clone()),
            Type::TForall(tv, ty) => Type::TForall(tv.clone(), Rc::new(self.reify(ty))),
            Type::TFun(a, b) => Type::TFun(Rc::new(self.reify(a)), Rc::new(self.reify(b))),
            Type::TNullable(t) => Type::TNullable(Rc::new(self.reify(t))),
            Type::TPair(a, b) => Type::TPair(Rc::new(self.reify(a)), Rc::new(self.reify(b))),
            Type::TApp(a, b) => Type::TApp(Rc::new(self.reify(a)), Rc::new(self.reify(b))),
            _ => typ.clone(),
        }
    }
}

pub fn typesynth_closed(e: &Expr) -> Result<(Polytype, Context), CompileErr> {
    let (a, gamma) = Context::new_wf(vec![]).typesynth(e)?;
    Ok((gamma.apply(&a), *gamma))
}

// Examples as tests
