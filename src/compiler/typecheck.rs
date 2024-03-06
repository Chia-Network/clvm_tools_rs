use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::sexp::{enlist, SExp};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::types::ast::{ContextElim, Expr, GContext, Type, TypeVar, Var};

pub trait TheoryToSExp {
    fn to_sexp(&self) -> SExp;
}

impl TheoryToSExp for TypeVar {
    fn to_sexp(&self) -> SExp {
        SExp::Atom(self.loc(), self.0.as_bytes().to_vec())
    }
}

impl TheoryToSExp for Var {
    fn to_sexp(&self) -> SExp {
        SExp::Atom(self.loc(), self.0.as_bytes().to_vec())
    }
}

impl<const A: usize> TheoryToSExp for Type<A> {
    fn to_sexp(&self) -> SExp {
        match self {
            Type::TUnit(l) => SExp::Nil(l.clone()),
            Type::TAny(l) => SExp::Atom(l.clone(), "Any".as_bytes().to_vec()),
            Type::TAtom(l, None) => SExp::Atom(l.clone(), "Atom".as_bytes().to_vec()),
            Type::TAtom(l, Some(s)) => {
                let atom_intro = format!("Atom{s}").as_bytes().to_vec();
                SExp::Atom(l.clone(), atom_intro)
            }
            Type::TVar(v) => SExp::Atom(v.loc(), v.0.as_bytes().to_vec()),
            Type::TExists(v) => SExp::Cons(
                v.loc(),
                Rc::new(SExp::Atom(v.loc(), "exists".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(v.loc(), v.0.as_bytes().to_vec())),
                    Rc::new(SExp::Nil(v.loc())),
                )),
            ),
            Type::TForall(v, t) => SExp::Cons(
                v.loc(),
                Rc::new(SExp::Atom(v.loc(), "forall".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(v.loc(), v.0.as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        v.loc(),
                        Rc::new(t.to_sexp()),
                        Rc::new(SExp::Nil(v.loc())),
                    )),
                )),
            ),
            Type::TFun(t1, t2) => SExp::Cons(
                t1.loc(),
                Rc::new(t1.to_sexp()),
                Rc::new(SExp::Cons(
                    t1.loc(),
                    Rc::new(SExp::Atom(t1.loc(), "->".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        t2.loc(),
                        Rc::new(t2.to_sexp()),
                        Rc::new(SExp::Nil(t2.loc())),
                    )),
                )),
            ),
            Type::TNullable(t1) => SExp::Cons(
                t1.loc(),
                Rc::new(SExp::Atom(t1.loc(), "Nullable".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    t1.loc(),
                    Rc::new(t1.to_sexp()),
                    Rc::new(SExp::Nil(t1.loc())),
                )),
            ),
            Type::TExec(t1) => SExp::Cons(
                t1.loc(),
                Rc::new(SExp::Atom(t1.loc(), "Exec".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    t1.loc(),
                    Rc::new(t1.to_sexp()),
                    Rc::new(SExp::Nil(t1.loc())),
                )),
            ),
            Type::TPair(t1, t2) => SExp::Cons(
                t1.loc(),
                Rc::new(SExp::Atom(t1.loc(), "Pair".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    t1.loc(),
                    Rc::new(t1.to_sexp()),
                    Rc::new(SExp::Cons(
                        t2.loc(),
                        Rc::new(t2.to_sexp()),
                        Rc::new(SExp::Nil(t2.loc())),
                    )),
                )),
            ),
            Type::TAbs(v, t) => SExp::Cons(
                v.loc(),
                Rc::new(v.to_sexp()),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(v.loc(), "~>".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        t.loc(),
                        Rc::new(t.to_sexp()),
                        Rc::new(SExp::Nil(t.loc())),
                    )),
                )),
            ),
            Type::TApp(t1, t2) => SExp::Cons(
                t1.loc(),
                Rc::new(t1.to_sexp()),
                Rc::new(SExp::Cons(
                    t2.loc(),
                    Rc::new(t2.to_sexp()),
                    Rc::new(SExp::Nil(t2.loc())),
                )),
            ),
        }
    }
}

impl TheoryToSExp for Expr {
    fn to_sexp(&self) -> SExp {
        match self {
            Expr::EVar(v) => SExp::Atom(v.loc(), v.0.as_bytes().to_vec()),
            Expr::EUnit(l) => SExp::Nil(l.clone()),
            Expr::EAbs(v, e) => SExp::Cons(
                v.loc(),
                Rc::new(SExp::Atom(v.loc(), "lambda".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(v.loc(), v.0.as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        e.loc(),
                        Rc::new(e.to_sexp()),
                        Rc::new(SExp::Nil(e.loc())),
                    )),
                )),
            ),
            Expr::EApp(e1, e2) => SExp::Cons(
                e1.loc(),
                Rc::new(e1.to_sexp()),
                Rc::new(SExp::Cons(
                    e2.loc(),
                    Rc::new(e2.to_sexp()),
                    Rc::new(SExp::Nil(e2.loc())),
                )),
            ),
            Expr::EAnno(e, t) => SExp::Cons(
                e.loc(),
                Rc::new(e.to_sexp()),
                Rc::new(SExp::Cons(
                    t.loc(),
                    Rc::new(SExp::Atom(t.loc(), ":".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        t.loc(),
                        Rc::new(t.to_sexp()),
                        Rc::new(SExp::Nil(t.loc())),
                    )),
                )),
            ),
            Expr::ELit(l, n) => SExp::Integer(l.clone(), n.clone()),
        }
    }
}

impl<const A: usize> TheoryToSExp for ContextElim<A> {
    fn to_sexp(&self) -> SExp {
        match self {
            ContextElim::CForall(tv) => SExp::Cons(
                tv.loc(),
                Rc::new(SExp::Atom(tv.loc(), "cforall".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    tv.loc(),
                    Rc::new(tv.to_sexp()),
                    Rc::new(SExp::Nil(tv.loc())),
                )),
            ),
            ContextElim::CVar(v, typ) => SExp::Cons(
                v.loc(),
                Rc::new(SExp::Atom(v.loc(), "cvar".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(v.to_sexp()),
                    Rc::new(SExp::Cons(
                        typ.loc(),
                        Rc::new(typ.to_sexp()),
                        Rc::new(SExp::Nil(v.loc())),
                    )),
                )),
            ),
            ContextElim::CExists(tv) => SExp::Cons(
                tv.loc(),
                Rc::new(SExp::Atom(tv.loc(), "cexists".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    tv.loc(),
                    Rc::new(tv.to_sexp()),
                    Rc::new(SExp::Nil(tv.loc())),
                )),
            ),
            ContextElim::CExistsSolved(t, m) => SExp::Cons(
                t.loc(),
                Rc::new(SExp::Atom(t.loc(), "csolved".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    t.loc(),
                    Rc::new(t.to_sexp()),
                    Rc::new(SExp::Cons(
                        m.loc(),
                        Rc::new(m.to_sexp()),
                        Rc::new(SExp::Nil(m.loc())),
                    )),
                )),
            ),
            ContextElim::CMarker(m) => SExp::Cons(
                m.loc(),
                Rc::new(SExp::Atom(m.loc(), "cmarker".as_bytes().to_vec())),
                Rc::new(SExp::Cons(
                    m.loc(),
                    Rc::new(m.to_sexp()),
                    Rc::new(SExp::Nil(m.loc())),
                )),
            ),
        }
    }
}

impl<const A: usize> TheoryToSExp for GContext<A> {
    fn to_sexp(&self) -> SExp {
        let thloc = Srcloc::start("*gcontext*");
        let self_list: Vec<Rc<SExp>> = self.0.iter().map(|x| Rc::new(x.to_sexp())).collect();
        enlist(thloc, &self_list)
    }
}

pub fn parse_type_var(atom: Rc<SExp>) -> Result<TypeVar, CompileErr> {
    match atom.atomize() {
        SExp::Atom(l, a) => Ok(TypeVar(std::str::from_utf8(&a).unwrap().to_string(), l)),
        _ => Err(CompileErr(atom.loc(), format!("not a type var: {atom}"))),
    }
}

fn parse_type_exists<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    match rest.borrow() {
        SExp::Cons(_, a, _) => {
            let tv = parse_type_var(a.clone())?;
            Ok(Type::TExists(tv))
        }
        _ => Err(CompileErr(
            rest.loc(),
            format!("not a valid exists tail: {rest}"),
        )),
    }
}

fn parse_type_forall<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    if let SExp::Cons(_, a, b) = rest.borrow() {
        let tv = parse_type_var(a.clone())?;
        if let SExp::Cons(_, ty, _) = b.borrow() {
            let parsed_ty = parse_type_sexp(ty.clone())?;
            return Ok(Type::TForall(tv, Rc::new(parsed_ty)));
        }
    }

    Err(CompileErr(rest.loc(), format!("bad forall tail: {rest}")))
}

fn parse_type_pair<const A: usize, F>(f: F, rest: Rc<SExp>) -> Result<Type<A>, CompileErr>
where
    F: FnOnce(Rc<Type<A>>, Rc<Type<A>>) -> Type<A>,
{
    if let SExp::Cons(_, a, rest) = rest.borrow() {
        let parsed_a = parse_type_sexp(a.clone())?;
        if let SExp::Cons(_, b, _rest) = rest.borrow() {
            let parsed_b = parse_type_sexp(b.clone())?;
            return Ok(f(Rc::new(parsed_a), Rc::new(parsed_b)));
        }
    }

    Err(CompileErr(rest.loc(), format!("bad product tail: {rest}")))
}

fn parse_type_single<const A: usize, F>(f: F, rest: Rc<SExp>) -> Result<Type<A>, CompileErr>
where
    F: FnOnce(Rc<Type<A>>) -> Type<A>,
{
    if let SExp::Cons(_, a, _) = rest.borrow() {
        return Ok(f(Rc::new(parse_type_sexp(a.clone())?)));
    }

    Err(CompileErr(rest.loc(), format!("bad wrapper tail: {rest}")))
}

fn parse_type_app<const A: usize>(
    apply_to: Type<A>,
    offs: usize,
    elist: &[SExp],
) -> Result<Type<A>, CompileErr> {
    if offs >= elist.len() {
        Ok(apply_to)
    } else {
        let next = parse_type_sexp(Rc::new(elist[offs].clone()))?;
        parse_type_app(
            Type::TApp(Rc::new(apply_to), Rc::new(next)),
            offs + 1,
            elist,
        )
    }
}

// Even elements are types, odd elements are "->" or "~>"
fn parse_type_fun<const A: usize>(full: Rc<SExp>, elist: &[SExp]) -> Result<Type<A>, CompileErr> {
    let mut result = parse_type_sexp(Rc::new(elist[elist.len() - 1].clone()))?;
    let mut use_type = false;

    if elist[1].atomize().to_string() == "~>" {
        let tv = parse_type_var(Rc::new(elist[0].clone()))?;
        let ty = parse_type_sexp(Rc::new(elist[2].clone()))?;
        result = Type::TAbs(tv, Rc::new(ty));
    } else if elist[1].atomize().to_string() == "->" {
        for i_rev in 0..elist.len() - 1 {
            let i = elist.len() - i_rev - 2;
            if use_type {
                let ty = parse_type_sexp(Rc::new(elist[i].clone()))?;
                result = Type::TFun(Rc::new(ty), Rc::new(result));
            } else if let SExp::Atom(l, a) = &elist[i].atomize() {
                if &"->".as_bytes().to_vec() != a {
                    return Err(CompileErr(l.clone(), format!("bad arrow in {full}")));
                }
            }

            use_type = !use_type;
        }
    } else {
        return Err(CompileErr(full.loc(), "Not arrow in fun".to_string()));
    }

    Ok(result)
}

pub fn parse_fixedlist<const A: usize>(expr: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    match &expr.atomize() {
        SExp::Cons(_l, a, b) => {
            let rest = parse_fixedlist(b.clone())?;
            let first = parse_type_sexp(a.clone())?;
            Ok(Type::TPair(Rc::new(first), Rc::new(rest)))
        }
        SExp::Atom(_l, _a) => parse_type_sexp(expr),
        SExp::Nil(l) => Ok(Type::TUnit(l.clone())),
        _ => Err(CompileErr(
            expr.loc(),
            format!("Don't know how to handle type named {expr}"),
        )),
    }
}

pub fn parse_type_sexp<const A: usize>(expr: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    match &expr.atomize() {
        SExp::Atom(l, a) => {
            if a.is_empty() || a == &"Unit".as_bytes().to_vec() {
                return Ok(Type::TUnit(l.clone()));
            } else if a == &"Any".as_bytes().to_vec() {
                return Ok(Type::TAny(l.clone()));
            } else if a == &"Atom".as_bytes().to_vec() {
                return Ok(Type::TAtom(l.clone(), None));
            } else if a == &"Atom32".as_bytes().to_vec() {
                return Ok(Type::TAtom(l.clone(), 32_u32.to_bigint()));
            } else {
                return Ok(Type::TVar(parse_type_var(expr.clone())?));
            }
        }

        SExp::Nil(l) => {
            return Ok(Type::TUnit(l.clone()));
        }

        SExp::Cons(_, a, b) => {
            // Some kind of larger type form:
            //
            // Declarations
            // (exists v)
            // (forall v ty)
            //
            // Concrete types
            // (Pair x y)
            // Function type
            // (x -> y)
            // (x -> . rest)
            // (v ~> t)
            if let SExp::Atom(_l, a) = &a.atomize() {
                if a == &"exists".as_bytes().to_vec() {
                    return parse_type_exists(b.clone());
                } else if a == &"forall".as_bytes().to_vec() {
                    return parse_type_forall(b.clone());
                } else if a == &"Pair".as_bytes().to_vec() {
                    return parse_type_pair(Type::TPair, b.clone());
                } else if a == &"Nullable".as_bytes().to_vec() {
                    return parse_type_single(Type::TNullable, b.clone());
                } else if a == &"Exec".as_bytes().to_vec() {
                    return parse_type_single(Type::TExec, b.clone());
                } else if a == &"FixedList".as_bytes().to_vec() {
                    return parse_fixedlist(b.clone());
                }
            }

            if let Some(lst) = expr.proper_list() {
                if lst.len() > 1 {
                    return parse_type_fun(expr.clone(), &lst)
                        .map(Ok)
                        .unwrap_or_else(|_| {
                            let apply_name = parse_type_var(Rc::new(lst[0].clone()))?;
                            parse_type_app(Type::TVar(apply_name), 1, &lst)
                        });
                }
            }
        }

        _ => {}
    }

    Err(CompileErr(
        expr.loc(),
        format!("not a valid type expression: {expr}"),
    ))
}

pub fn parse_evar(expr: &SExp) -> Result<Var, CompileErr> {
    if let SExp::Atom(l, a) = expr {
        return Ok(Var(std::str::from_utf8(a).unwrap().to_string(), l.clone()));
    }

    Err(CompileErr(expr.loc(), format!("expected var got {expr}")))
}

pub fn parse_expr_anno(elist: &[SExp]) -> Result<Expr, CompileErr> {
    let ty = parse_type_sexp(Rc::new(elist[2].clone()))?;
    let expr = parse_expr_sexp(Rc::new(elist[0].clone()))?;
    Ok(Expr::EAnno(Rc::new(expr), ty))
}

pub fn parse_expr_lambda(elist: &[SExp]) -> Result<Expr, CompileErr> {
    let arg = parse_evar(&elist[1])?;
    let body = parse_expr_sexp(Rc::new(elist[2].clone()))?;
    Ok(Expr::EAbs(arg, Rc::new(body)))
}

// Parse a simple expression syntax to use with our type theory.
pub fn parse_expr_sexp(expr: Rc<SExp>) -> Result<Expr, CompileErr> {
    match expr.borrow() {
        SExp::Atom(l, a) => {
            if a.is_empty() {
                return Ok(Expr::EUnit(l.clone()));
            } else {
                return Ok(Expr::EVar(parse_evar(expr.borrow())?));
            }
        }
        SExp::Cons(l, _, _) => {
            // (called-fun arg arg ...) -> EApp
            // (x : T) -> EAnno
            // (lambda arg ...) -> EAbs
            // (some x)
            // there is no none:
            // we want Γ |- () <== (forall x (nullable x))
            if let Some(lst) = expr.proper_list() {
                if lst.len() == 3 {
                    if let SExp::Atom(_, name) = &lst[0] {
                        if &"lambda".as_bytes().to_vec() == name {
                            return parse_expr_lambda(&lst);
                        }

                        if &"cons".as_bytes().to_vec() == name {
                            let e1 = parse_expr_sexp(Rc::new(lst[1].clone()))?;
                            let e2 = parse_expr_sexp(Rc::new(lst[2].clone()))?;
                            return Ok(Expr::EApp(
                                Rc::new(Expr::EApp(
                                    Rc::new(Expr::EVar(Var("c^".to_string(), l.clone()))),
                                    Rc::new(e1),
                                )),
                                Rc::new(e2),
                            ));
                        }
                    }

                    if let SExp::Atom(_, name) = &lst[1] {
                        if name.len() == 1 && name[0] == b':' {
                            return parse_expr_anno(&lst);
                        }
                    }
                }

                if lst.len() == 2 {
                    if let SExp::Atom(_, name) = &lst[0] {
                        if &"some".as_bytes().to_vec() == name {
                            let inner_exp = parse_expr_sexp(Rc::new(lst[1].clone()))?;
                            return Ok(Expr::EApp(
                                Rc::new(Expr::EVar(Var("some".to_string(), l.clone()))),
                                Rc::new(inner_exp),
                            ));
                        }
                    }
                }

                // I may change this to model all functions as unary, but
                // it serves here.
                if lst.len() > 1 {
                    let mut res = parse_expr_sexp(Rc::new(lst[lst.len() - 1].clone()))?;
                    for e in lst.iter().rev().skip(1) {
                        let new_expr = parse_expr_sexp(Rc::new(e.clone()))?;
                        res = Expr::EApp(Rc::new(new_expr), Rc::new(res));
                    }
                    return Ok(res);
                } else if !lst.is_empty() {
                    // Just pretend (foo) is (foo ())
                    return Ok(Expr::EApp(
                        Rc::new(parse_expr_sexp(Rc::new(lst[0].clone()))?),
                        Rc::new(Expr::EUnit(l.clone())),
                    ));
                }
            }
        }
        SExp::Integer(l, a) => {
            return Ok(Expr::ELit(l.clone(), a.clone()));
        }
        SExp::Nil(l) => {
            return Ok(Expr::EUnit(l.clone()));
        }
        _ => {}
    }

    Err(CompileErr(expr.loc(), format!("bad expr {expr}")))
}
