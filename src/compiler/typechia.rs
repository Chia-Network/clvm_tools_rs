use std::borrow::Borrow;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    BodyForm,
    ChiaType,
    CompileErr,
    CompileForm,
    HelperForm
};
use crate::compiler::sexp::{
    SExp,
    decode_string
};
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{
    Context,
    ContextElim,
    Expr,
    Monotype,
    Polytype,
    TYPE_MONO,
    Type,
    TypeVar,
    Var
};
use crate::compiler::types::astfuns::polytype;
use crate::compiler::types::theory::TypeTheory;
use crate::util::Number;

//
// Standard chia type environment.
//
// Includes all primitives and aliases for some primitives
// that allow cracking and building types that resist
// ordinary operators.
//
pub fn standard_type_context() -> Context {
    let loc = Srcloc::start(&"*type-prelude*".to_string());

    // Basic sorts
    let unit_tv = TypeVar("Unit".to_string(), loc.clone());
    let any_tv = TypeVar("Any".to_string(), loc.clone());
    let atom_tv = TypeVar("Atom".to_string(), loc.clone());
    let list_tv = TypeVar("List".to_string(), loc.clone());
    let f0 = TypeVar("f0".to_string(), loc.clone());
    let r0 = TypeVar("r0".to_string(), loc.clone());

    let unit: Type<TYPE_MONO> = Type::TUnit(loc.clone());
    let any: Type<TYPE_MONO> = Type::TAny(loc.clone());
    let atom: Type<TYPE_MONO> = Type::TAtom(loc.clone(), None);
    let cons: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TForall(
                r0.clone(),
                Rc::new(Type::TFun(
                    Rc::new(Type::TVar(r0.clone())),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone()))
                    ))
                ))
            ))
        ))
    );
    let first: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone()))
                )),
                Rc::new(Type::TVar(f0.clone()))
            )),
        ))
    );
    let fprime: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TExec(
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone()))
                    )),
                )),
                Rc::new(Type::TVar(f0.clone()))
            ))
        ))
    );
    let rest: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TForall(
            f0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone()))
                )),
                Rc::new(Type::TVar(r0.clone()))
            ))
        ))
    );
    let rprime: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TForall(
            f0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TExec(
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone()))
                    ))
                )),
                Rc::new(Type::TVar(r0.clone()))
            ))
        ))
    );
    let bless: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TForall(
                r0.clone(),
                Rc::new(Type::TFun(
                    Rc::new(Type::TVar(r0.clone())),
                    Rc::new(Type::TExec(
                        Rc::new(Type::TPair(
                            Rc::new(Type::TVar(f0.clone())),
                            Rc::new(Type::TVar(r0.clone()))
                        ))
                    ))
                ))
            ))
        ))
    );
    // (a (Exec X)) => X
    // so
    // ((a (Exec (x -> y))) x)
    let apply: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TExec(
                Rc::new(Type::TVar(f0.clone()))
            )),
            Rc::new(Type::TVar(f0.clone()))
        ))
    );
    let some: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TNullable(Rc::new(Type::TVar(f0.clone()))))
        ))
    );

    let list: Type<TYPE_MONO> = Type::TAbs(
        f0.clone(),
        Rc::new(Type::TNullable(
            Rc::new(Type::TPair(
                Rc::new(Type::TVar(f0.clone())),
                Rc::new(Type::TApp(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(list_tv.clone()))
                ))
            ))
        ))
    );

    // Primitive definitions
    let c_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(r0.clone())),
                        Rc::new(Type::TUnit(f0.loc()))
                    ))
                )),
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone()))
                ))
            ))
        ))
    );
    let plus_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TApp(
            Rc::new(Type::TAtom(atom_tv.loc(), None)),
            Rc::new(Type::TVar(list_tv.clone()))
        )),
        Rc::new(Type::TAtom(atom_tv.loc(), None))
    );
    let sha256_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TApp(
            Rc::new(Type::TAtom(atom_tv.loc(), None)),
            Rc::new(Type::TVar(list_tv.clone()))
        )),
        Rc::new(Type::TAtom(atom_tv.loc(), Some(32)))
    );

    Context::new(vec![
        ContextElim::CVar(Var("c^".to_string(), loc.clone()), polytype(&cons)),
        ContextElim::CVar(Var("some".to_string(), loc.clone()), polytype(&some)),
        ContextElim::CVar(Var("f".to_string(), loc.clone()), polytype(&first)),
        ContextElim::CVar(Var("r".to_string(), loc.clone()), polytype(&rest)),
        ContextElim::CVar(Var("a".to_string(), loc.clone()), polytype(&apply)),
        ContextElim::CVar(Var("f^".to_string(), loc.clone()), polytype(&fprime)),
        ContextElim::CVar(Var("r^".to_string(), loc.clone()), polytype(&rprime)),
        ContextElim::CVar(Var("bless".to_string(), loc.clone()), polytype(&bless)),

        // clvm primitives
        ContextElim::CVar(Var("c".to_string(), loc.clone()), polytype(&c_prim)),
        ContextElim::CVar(Var("+".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("sha256".to_string(), loc.clone()), polytype(&sha256_prim)),

        // Builtin types
        ContextElim::CExistsSolved(list_tv, list),
        ContextElim::CExistsSolved(unit_tv, unit),
        ContextElim::CExistsSolved(any_tv, any),
        ContextElim::CExistsSolved(atom_tv, atom)
    ])
}

fn type_of_defun(l: Srcloc, ty: &Option<Polytype>) -> Polytype {
    if let Some(ty) = ty {
        ty.clone()
    } else {
        Type::TFun(
            Rc::new(Type::TAny(l.clone())),
            Rc::new(Type::TAny(l.clone()))
        )
    }
}

pub fn context_from_args_and_type(
    context: &Context,
    args: Rc<SExp>,
    argty: &Polytype,
    path: Number,
    path_bit: Number
) -> Result<Context, CompileErr> {
    match (args.borrow(), argty) {
        (SExp::Nil(_), Type::TAny(_)) => Ok(context.clone()),
        (SExp::Nil(_), Type::TUnit(_)) => Ok(context.clone()),
        (SExp::Nil(l), _) => {
            Err(CompileErr(l.clone(), format!("function has empty argument list but type {}", argty.to_sexp().to_string())))
        },
        (SExp::Atom(l,a), ty) => {
            Ok(context.snoc_wf(
                ContextElim::CVar(
                    Var(decode_string(a), l.clone()),
                    argty.clone()
                )
            ))
        },
        (SExp::Cons(l,_,_), Type::TUnit(_)) => {
            Err(CompileErr(l.clone(), format!("function has an argument list but specifies empty arguments")))
        },
        (SExp::Cons(_,f,r), Type::TAny(_)) => {
            if let Some((_,_)) = is_at_capture(f.clone(), r.clone()) {
                todo!()
            } else {
                let cf = context_from_args_and_type(
                    context,
                    f.clone(),
                    argty,
                    path.clone(),
                    path_bit.clone() * 2_u32.to_bigint().unwrap()
                )?;
                context_from_args_and_type(
                    &cf,
                    r.clone(),
                    argty,
                    path + path_bit.clone(),
                    path_bit * 2_u32.to_bigint().unwrap()
                )
            }
        },
        (SExp::Cons(l,f,r), Type::TPair(a,b)) => {
            if let Some((_,_)) = is_at_capture(f.clone(), r.clone()) {
                todo!()
            } else {
                let cf = context_from_args_and_type(
                    context,
                    f.clone(),
                    a.borrow(),
                    bi_zero(),
                    bi_one()
                )?;
                context_from_args_and_type(
                    &cf,
                    r.clone(),
                    b.borrow(),
                    path + path_bit.clone(),
                    path_bit * 2_u32.to_bigint().unwrap()
                )
            }
        },
        _ => todo!("unhandled case {} vs {}", args.to_string(), argty.to_sexp().to_string())
    }
}

fn chialisp_to_expr(
    body: Rc<BodyForm>
) -> Expr {
    match body.borrow() {
        BodyForm::Quoted(SExp::Nil(l)) => { Expr::EUnit(l.clone()) },
        BodyForm::Value(SExp::Nil(l)) => { Expr::EUnit(l.clone()) },
        BodyForm::Value(SExp::Atom(l,n)) => {
            Expr::EVar(Var(decode_string(n), l.clone()))
        },
        BodyForm::Call(l,lst) => {
            let mut arg_expr = Expr::EUnit(l.clone());
            for i_rev in 0..lst.len() - 1 {
                let i = lst.len() - i_rev - 1;
                let new_expr = chialisp_to_expr(lst[i].clone());
                arg_expr = Expr::EApp(
                    Rc::new(Expr::EApp(
                        Rc::new(Expr::EVar(Var("c^".to_string(), l.clone()))),
                        Rc::new(new_expr)
                    )),
                    Rc::new(arg_expr)
                );
            }
            Expr::EApp(
                Rc::new(chialisp_to_expr(lst[0].clone())),
                Rc::new(arg_expr)
            )
        },
        _ => todo!("not sure how to handle {:?} yet", body)
    }
}

fn typecheck_chialisp_body_with_context(
    context_: &Context,
    expr: &Expr
) -> Result<Polytype, CompileErr> {
    context_.typesynth(&expr).map(|(res,_)| res)
}

fn chia_to_type(ty: &ChiaType) -> Monotype {
    todo!()
}

fn handle_function_type(
    context: &Context,
    loc: Srcloc,
    args: Rc<SExp>,
    ty: &Polytype
) -> Result<(Context, Polytype), CompileErr> {
    match ty {
        Type::TFun(a,r) => {
            let r_borrowed: &Polytype = r.borrow();
            context_from_args_and_type(
                &context,
                args.clone(),
                a.borrow(),
                bi_zero(),
                bi_one()
            ).map(|ctx| (ctx, r_borrowed.clone()))
        },
        Type::TForall(t,f) => {
            let inner_ctx = context.snoc_wf(ContextElim::CForall(t.clone()));
            let f_borrowed: &Polytype = f.borrow();
            handle_function_type(&inner_ctx, loc, args, f_borrowed)
        },
        _ => {
            Err(CompileErr(loc, "Type of a defun must be a function type".to_string()))
        }
    }
}

// Given a compileform, typecheck
impl Context {
    pub fn typecheck_chialisp_program(
        &self, comp: &CompileForm
    ) -> Result<Polytype, CompileErr> {
        let mut context = self.clone();

        // Extract type definitions
        for h in comp.helpers.iter() {
            if let HelperForm::Deftype(l, name, args, ty) = &h {
                let tname = decode_string(name);
                if let Some(ty) = ty {
                    let use_type = chia_to_type(ty);
                    context = context.snoc_wf(ContextElim::CExistsSolved(
                        TypeVar(tname, l.clone()), use_type
                    ));
                } else {
                    // An abstract type declaration.
                    context = context.snoc_wf(
                        ContextElim::CForall(TypeVar(tname, l.clone()))
                    );
                }
            }
        }

        // Extract constants
        for h in comp.helpers.iter() {
            if let HelperForm::Defconstant(l, name, body, ty) = &h {
                let tname = decode_string(name);
                if let Some(ty) = ty {
                    context = context.snoc_wf(ContextElim::CVar(
                        Var(tname, l.clone()),
                        ty.clone()
                    ));
                } else {
                    context = context.snoc_wf(ContextElim::CVar(
                        Var(tname, l.clone()),
                        Type::TAny(l.clone())
                    ));
                }
            }
        }

        // Extract functions
        for h in comp.helpers.iter() {
            if let HelperForm::Defun(l, name, _, args, body, ty) = &h {
                let tname = decode_string(name);
                let ty = type_of_defun(l.clone(), ty);
                context = context.snoc_wf(
                    ContextElim::CVar(Var(tname, l.clone()), ty)
                );
            }
        }

        // Typecheck helper functions
        for h in comp.helpers.iter() {
            if let HelperForm::Defun(l, name, _, args, body, ty) = &h {
                let ty = type_of_defun(l.clone(), ty);
                let (context_with_args, result_ty) =
                    handle_function_type(&context, h.loc(), args.clone(), &ty)?;
                typecheck_chialisp_body_with_context(
                    &context_with_args,
                    &Expr::EAnno(
                        Rc::new(chialisp_to_expr(body.clone())),
                        result_ty
                    )
                )?;
            }
        }

        // Typecheck main expression
        let ty = type_of_defun(comp.exp.loc(), &comp.ty);
        let (context_with_args, result_ty) =
            handle_function_type(
                &context,
                comp.exp.loc(),
                comp.args.clone(),
                &ty
            )?;
        typecheck_chialisp_body_with_context(
            &context_with_args,
            &Expr::EAnno(
                Rc::new(chialisp_to_expr(comp.exp.clone())),
                result_ty
            )
        )
    }
}
