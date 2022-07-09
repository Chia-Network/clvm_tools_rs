use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::comptypes::CompileErr;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::types::ast::{
    Context,
    ContextElim,
    Expr,
    TYPE_MONO,
    Type,
    TypeVar,
    Var
};

pub trait TheoryToSExp {
    fn to_sexp(&self) -> SExp;
}

impl TheoryToSExp for TypeVar {
    fn to_sexp(&self) -> SExp {
        SExp::Atom(self.loc(), self.0.as_bytes().to_vec())
    }
}

impl<const A: usize> TheoryToSExp for Type<A> {
    fn to_sexp(&self) -> SExp {
        match self {
            Type::TUnit(l) => SExp::Nil(l.clone()),
            Type::TAny(l) => SExp::Atom(l.clone(), "Any".as_bytes().to_vec()),
            Type::TAtom(l) => SExp::Atom(l.clone(), "Atom".as_bytes().to_vec()),
            Type::TVar(v) => SExp::Atom(v.loc(), v.0.as_bytes().to_vec()),
            Type::TExists(v) => {
                SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(
                        v.loc(),
                        "exists".as_bytes().to_vec()
                    )),
                    Rc::new(SExp::Cons(
                        v.loc(),
                        Rc::new(SExp::Atom(
                            v.loc(),
                            v.0.as_bytes().to_vec()
                        )),
                        Rc::new(SExp::Nil(v.loc()))
                    ))
                )
            },
            Type::TForall(v, t) => {
            SExp::Cons(
                v.loc(),
                Rc::new(SExp::Atom(
                    v.loc(),
                    "forall".as_bytes().to_vec()
                )),
                Rc::new(SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(
                        v.loc(),
                        v.0.as_bytes().to_vec()
                    )),
                    Rc::new(SExp::Cons(
                        v.loc(),
                        Rc::new(t.to_sexp()),
                        Rc::new(SExp::Nil(v.loc()))
                    ))
                ))
            )
            },
            Type::TFun(t1, t2) => {
                SExp::Cons(
                    t1.loc(),
                    Rc::new(t1.to_sexp()),
                    Rc::new(SExp::Cons(
                        t1.loc(),
                        Rc::new(SExp::Atom(
                            t1.loc(),
                            "->".as_bytes().to_vec()
                        )),
                        Rc::new(SExp::Cons(
                            t2.loc(),
                            Rc::new(t2.to_sexp()),
                            Rc::new(SExp::Nil(t2.loc()))
                        ))
                    ))
                )
            },
            Type::TNullable(t1) => {
                SExp::Cons(
                    t1.loc(),
                    Rc::new(SExp::Atom(
                        t1.loc(),
                        "Nullable".as_bytes().to_vec()
                    )),
                    Rc::new(SExp::Cons(
                        t1.loc(),
                        Rc::new(t1.to_sexp()),
                        Rc::new(SExp::Nil(t1.loc()))
                    ))
                )
            },
            Type::TPair(t1,t2) => {
                SExp::Cons(
                    t1.loc(),
                    Rc::new(SExp::Atom(
                        t1.loc(),
                        "Pair".as_bytes().to_vec()
                    )),
                    Rc::new(SExp::Cons(
                        t1.loc(),
                        Rc::new(t1.to_sexp()),
                        Rc::new(SExp::Cons(
                            t2.loc(),
                            Rc::new(t2.to_sexp()),
                            Rc::new(SExp::Nil(t2.loc()))
                        ))
                    ))
                )
            }
        }
    }
}

impl TheoryToSExp for Expr {
    fn to_sexp(&self) -> SExp {
        match self {
            Expr::EVar(v) => SExp::Atom(v.loc(), v.0.as_bytes().to_vec()),
            Expr::EUnit(l) => SExp::Nil(l.clone()),
            Expr::EAbs(v,e) => {
                SExp::Cons(
                    v.loc(),
                    Rc::new(SExp::Atom(v.loc(), "lambda".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        v.loc(),
                        Rc::new(SExp::Atom(v.loc(), v.0.as_bytes().to_vec())),
                        Rc::new(SExp::Cons(
                            e.loc(),
                            Rc::new(e.to_sexp()),
                            Rc::new(SExp::Nil(e.loc()))
                        ))
                    ))
                )
            },
            Expr::EApp(e1,e2) => {
                SExp::Cons(
                    e1.loc(),
                    Rc::new(e1.to_sexp()),
                    Rc::new(SExp::Cons(
                        e2.loc(),
                        Rc::new(e2.to_sexp()),
                        Rc::new(SExp::Nil(e2.loc()))
                    ))
                )
            },
            Expr::EAnno(e,t) => {
                SExp::Cons(
                    e.loc(),
                    Rc::new(e.to_sexp()),
                    Rc::new(SExp::Cons(
                        t.loc(),
                        Rc::new(SExp::Atom(t.loc(), ":".as_bytes().to_vec())),
                        Rc::new(SExp::Cons(
                            t.loc(),
                            Rc::new(t.to_sexp()),
                            Rc::new(SExp::Nil(t.loc()))
                        ))
                    ))
                )
            },
            Expr::ELit(l,n) => {
                SExp::Integer(l.clone(), n.clone())
            },
            Expr::ESome(e) => {
                SExp::Cons(
                    e.loc(),
                    Rc::new(SExp::Atom(e.loc(), "some".as_bytes().to_vec())),
                    Rc::new(SExp::Cons(
                        e.loc(),
                        Rc::new(e.to_sexp()),
                        Rc::new(SExp::Nil(e.loc()))
                    ))
                )
            }
        }
    }
}

fn parse_type_var(atom: Rc<SExp>) -> Result<TypeVar, CompileErr> {
    match atom.borrow() {
        SExp::Atom(l,a) => {
            Ok(TypeVar(std::str::from_utf8(&a).unwrap().to_string(), l.clone()))
        },
        _ => Err(CompileErr(atom.loc(), format!("not a type var: {}", atom.to_string())))
    }
}

fn parse_type_exists<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    match rest.borrow() {
        SExp::Cons(l,a,b) => {
            let tv = parse_type_var(a.clone())?;
            Ok(Type::TExists(tv))
        },
        _ => Err(CompileErr(rest.loc(), format!("not a valid exists tail: {}", rest.to_string())))
    }
}

fn parse_type_forall<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    if let SExp::Cons(l,a,b) = rest.borrow() {
        let tv = parse_type_var(a.clone())?;
        if let SExp::Cons(l2,ty,_) = b.borrow() {
            let parsed_ty = parse_type_sexp(ty.clone())?;
            return Ok(Type::TForall(tv, Rc::new(parsed_ty)));
        }
    }

    Err(CompileErr(rest.loc(), format!("bad forall tail: {}", rest.to_string())))
}

fn parse_type_pair<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    if let SExp::Cons(l,a,rest) = rest.borrow() {
        let parsed_a = parse_type_sexp(a.clone())?;
        if let SExp::Cons(l,b,rest) = rest.borrow() {
            let parsed_b = parse_type_sexp(b.clone())?;
            return Ok(Type::TPair(Rc::new(parsed_a), Rc::new(parsed_b)));
        }
    }

    Err(CompileErr(rest.loc(), format!("bad Pair tail: {}", rest.to_string())))
}

fn parse_type_nullable<const A: usize>(rest: Rc<SExp>) -> Result<Type<A>, CompileErr> {
    if let SExp::Cons(l,a,b) = rest.borrow() {
        return Ok(Type::TNullable(Rc::new(parse_type_sexp(a.clone())?)));
    }

    Err(CompileErr(rest.loc(), format!("bad Nullable tail: {}", rest.to_string())))
}

// Even elements are types, odd elements are "->"
fn parse_type_fun<const A: usize>(full: Rc<SExp>, elist: Vec<SExp>) -> Result<Type<A>, CompileErr> {
    let mut result = parse_type_sexp(Rc::new(elist[elist.len()-1].clone()))?;
    let mut use_type = false;

    for i_rev in 0..elist.len() - 1 {
        let i = elist.len() - i_rev - 2;
        if use_type {
            let ty = parse_type_sexp(Rc::new(elist[i].clone()))?;
            result = Type::TFun(Rc::new(ty), Rc::new(result));
        } else {
            if let SExp::Atom(l,a) = &elist[i] {
                if &"->".as_bytes().to_vec() != a {
                    return Err(CompileErr(l.clone(), format!("bad arrow in {}", full.to_string())));
                }
            }
        }

        use_type = !use_type;
    }

    Ok(result)
}

pub fn parse_type_sexp<const A: usize>(
    expr: Rc<SExp>
) -> Result<Type<A>, CompileErr> {
    match expr.borrow() {
        SExp::Atom(l,a) => {
            if a.len() == 0 {
                return Ok(Type::TUnit(l.clone()));
            } else if a == &"Unit".as_bytes().to_vec() {
                return Ok(Type::TUnit(l.clone()));
            } else if a == &"Any".as_bytes().to_vec() {
                return Ok(Type::TAny(l.clone()));
            } else if a == &"Atom".as_bytes().to_vec() {
                return Ok(Type::TAtom(l.clone()));
            } else {
                return Ok(Type::TVar(parse_type_var(expr.clone())?));
            }
        },

        SExp::Nil(l) => {
            return Ok(Type::TUnit(l.clone()));
        },

        SExp::Cons(l,a,b) => {
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
            if let SExp::Atom(l,a) = a.borrow() {
                if a == &"exists".as_bytes().to_vec() {
                    return parse_type_exists(b.clone());
                } else if a == &"forall".as_bytes().to_vec() {
                    return parse_type_forall(b.clone());
                } else if a == &"Pair".as_bytes().to_vec() {
                    return parse_type_pair(b.clone());
                } else if a == &"Nullable".as_bytes().to_vec() {
                    return parse_type_nullable(b.clone());
                }
            }

            if let Some(lst) = expr.proper_list() {
                if lst.len() % 2 == 1 && lst.len() > 2 {
                    return parse_type_fun(expr.clone(), lst);
                }
            }
        },

        _ => { }
    }

    Err(CompileErr(expr.loc(), format!("not a valid type expression: {}", expr.to_string())))
}

pub fn parse_evar(expr: &SExp) -> Result<Var, CompileErr> {
    if let SExp::Atom(l,a) = expr {
        return Ok(Var(std::str::from_utf8(&a).unwrap().to_string(), l.clone()));
    }

    Err(CompileErr(expr.loc(), format!("expected var got {}", expr.to_string())))
}

pub fn parse_expr_anno(elist: &Vec<SExp>) -> Result<Expr, CompileErr> {
    let ty = parse_type_sexp(Rc::new(elist[2].clone()))?;
    let expr = parse_expr_sexp(Rc::new(elist[0].clone()))?;
    Ok(Expr::EAnno(Rc::new(expr), ty))
}

pub fn parse_expr_lambda(elist: &Vec<SExp>) -> Result<Expr, CompileErr> {
    let arg = parse_evar(&elist[1])?;
    let body = parse_expr_sexp(Rc::new(elist[2].clone()))?;
    Ok(Expr::EAbs(arg, Rc::new(body)))
}

// Parse a simple expression syntax to use with our type theory.
pub fn parse_expr_sexp(expr: Rc<SExp>) -> Result<Expr, CompileErr> {
    match expr.borrow() {
        SExp::Atom(l,a) => {
            if a.len() == 0 {
                return Ok(Expr::EUnit(l.clone()));
            } else {
                return Ok(Expr::EVar(parse_evar(expr.borrow())?));
            }
        },
        SExp::Cons(l,a,_) => {
            // (called-fun arg arg ...) -> EApp
            // (x : T) -> EAnno
            // (lambda arg ...) -> EAbs
            // (some x)
            // there is no none:
            // we want Γ |- () <== (forall x (nullable x))
            if let Some(lst) = expr.proper_list() {
                if lst.len() == 3 {
                    if let SExp::Atom(loc,name) = &lst[0] {
                        if &"lambda".as_bytes().to_vec() == name {
                            return parse_expr_lambda(&lst);
                        }
                    }

                    if let SExp::Atom(loc,name) = &lst[1] {
                        if name.len() == 1 && name[0] == b':' {
                            return parse_expr_anno(&lst);
                        }
                    }
                }

                if lst.len() == 2 {
                    if let SExp::Atom(loc,name) = &lst[0] {
                        if &"some".as_bytes().to_vec() == name {
                            let inner_exp = parse_expr_sexp(Rc::new(lst[1].clone()))?;
                            return Ok(Expr::ESome(Rc::new(inner_exp)));
                        }
                    }
                }

                // I may change this to model all functions as unary, but
                // it serves here.
                if lst.len() > 1 {
                    let mut res = parse_expr_sexp(Rc::new(lst[lst.len()-1].clone()))?;
                    for e in lst.iter().rev().skip(1) {
                        let new_expr = parse_expr_sexp(Rc::new(e.clone()))?;
                        res = Expr::EApp(Rc::new(new_expr), Rc::new(res));
                    }
                    return Ok(res);
                } else if lst.len() > 0 {
                    // Just pretend (foo) is (foo ())
                    return Ok(Expr::EApp(Rc::new(parse_expr_sexp(Rc::new(lst[0].clone()))?), Rc::new(Expr::EUnit(l.clone()))));
                }
            }
        },
        SExp::Integer(l,a) => {
            return Ok(Expr::ELit(l.clone(),a.clone()));
        },
        SExp::Nil(l) => {
            return Ok(Expr::EUnit(l.clone()));
        },
        _ => { }
    }

    Err(CompileErr(expr.loc(), format!("bad expr {}", expr.to_string())))
}

pub fn standard_type_context() -> Context {
    let loc = Srcloc::start(&"*type-prelude*".to_string());

    // Basic sorts
    let unit_tv = TypeVar("Unit".to_string(), loc.clone());
    let any_tv = TypeVar("Any".to_string(), loc.clone());
    let atom_tv = TypeVar("Atom".to_string(), loc.clone());

    let unit: Type<TYPE_MONO> = Type::TUnit(loc.clone());
    let any: Type<TYPE_MONO> = Type::TAny(loc.clone());
    let atom: Type<TYPE_MONO> = Type::TAtom(loc.clone());

    Context::new(vec![
        ContextElim::CExistsSolved(unit_tv, unit),
        ContextElim::CExistsSolved(any_tv, any),
        ContextElim::CExistsSolved(atom_tv, atom)
    ])
}
