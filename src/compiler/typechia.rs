use std::borrow::Borrow;
use std::rc::Rc;

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
    let plus: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TApp(
            Rc::new(Type::TAtom(atom_tv.loc(), None)),
            Rc::new(Type::TVar(list_tv.clone()))
        )),
        Rc::new(Type::TAtom(atom_tv.loc(), None))
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

    Context::new(vec![
        ContextElim::CVar(Var("c".to_string(), loc.clone()), polytype(&cons)),
        ContextElim::CVar(Var("some".to_string(), loc.clone()), polytype(&some)),
        ContextElim::CVar(Var("f".to_string(), loc.clone()), polytype(&first)),
        ContextElim::CVar(Var("r".to_string(), loc.clone()), polytype(&rest)),
        ContextElim::CVar(Var("a".to_string(), loc.clone()), polytype(&apply)),
        ContextElim::CVar(Var("f^".to_string(), loc.clone()), polytype(&fprime)),
        ContextElim::CVar(Var("r^".to_string(), loc.clone()), polytype(&rprime)),
        ContextElim::CVar(Var("+^".to_string(), loc.clone()), polytype(&plus)),
        ContextElim::CVar(Var("bless".to_string(), loc.clone()), polytype(&bless)),
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
    argty: &Polytype
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
                    argty
                )?;
                context_from_args_and_type(&cf, r.clone(), argty)
            }
        },
        (SExp::Cons(l,f,r), Type::TPair(a,b)) => {
            if let Some((_,_)) = is_at_capture(f.clone(), r.clone()) {
                todo!()
            } else {
                let cf = context_from_args_and_type(
                    context,
                    f.clone(),
                    a.borrow()
                )?;
                context_from_args_and_type(&cf, r.clone(), b.borrow())
            }
        },
        _ => todo!()
    }
}

fn chialisp_to_expr(
    args: Rc<SExp>,
    body: Rc<BodyForm>
) -> Expr {
    todo!()
}

fn typecheck_chialisp_body_with_context(
    context_: &Context,
    expr: &Expr
) -> Result<(), CompileErr> {
    todo!()
}

fn chia_to_type(ty: &ChiaType) -> Monotype {
    todo!()
}

// Given a compileform, typecheck
impl Context {
    pub fn typecheck_chialisp_program(
        &self, comp: CompileForm
    ) -> Result<(), CompileErr> {
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
                let context_with_args =
                    if let Type::TFun(a,r) = ty {
                        context_from_args_and_type(
                            &context, args.clone(), a.borrow()
                        )
                    } else {
                        Err(CompileErr(h.loc(), format!("Type of a defun must be a function type in {}", decode_string(name))))?
                    };

                typecheck_chialisp_body_with_context(
                    &context_with_args?,
                    &chialisp_to_expr(args.clone(), body.clone())
                )?;
            }
        }

        // Typecheck main expression
        let ty = type_of_defun(comp.exp.loc(), &comp.ty);
        let context_with_args = context_from_args_and_type(
            &context, comp.args.clone(), &ty
        )?;
        typecheck_chialisp_body_with_context(
            &context_with_args,
            &chialisp_to_expr(comp.args.clone(), comp.exp.clone())
        )
    }
}
