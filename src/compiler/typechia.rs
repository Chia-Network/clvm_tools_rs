use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use log::debug;

use num_bigint::ToBigInt;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::compiler::{is_at_capture, DefaultCompilerOpts};
use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, HelperForm};
use crate::compiler::evaluate::{build_argument_captures, dequote, Evaluator};
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{
    Context, ContextElim, Expr, Polytype, Type, TypeVar, Var, TYPE_MONO,
};
use crate::compiler::types::astfuns::polytype;
use crate::compiler::types::namegen::fresh_var;
use crate::compiler::types::theory::TypeTheory;
use crate::util::{number_from_u8, u8_from_number, Number};

//
// Standard chia type environment.
//
// Includes all primitives and aliases for some primitives
// that allow cracking and building types that resist
// ordinary operators.
//
pub fn standard_type_context() -> Context {
    let loc = Srcloc::start("*type-prelude*");

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
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TVar(f0.clone())),
                Rc::new(Type::TFun(
                    Rc::new(Type::TVar(r0.clone())),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )),
                )),
            )),
        )),
    );
    let first: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone())),
                )),
                Rc::new(Type::TVar(f0.clone())),
            )),
        )),
    );
    let fprime: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TExec(Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone())),
                )))),
                Rc::new(Type::TVar(f0.clone())),
            )),
        )),
    );
    let rest: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TForall(
            f0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone())),
                )),
                Rc::new(Type::TVar(r0.clone())),
            )),
        )),
    );
    let rprime: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TForall(
            f0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TExec(Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone())),
                )))),
                Rc::new(Type::TVar(r0.clone())),
            )),
        )),
    );
    let bless: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TForall(
                r0.clone(),
                Rc::new(Type::TFun(
                    Rc::new(Type::TVar(r0.clone())),
                    Rc::new(Type::TExec(Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )))),
                )),
            )),
        )),
    );
    // (a (Exec X)) => X
    // so
    // ((a (Exec (x -> y))) x)
    let apply: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TExec(Rc::new(Type::TVar(f0.clone())))),
            Rc::new(Type::TVar(f0.clone())),
        )),
    );
    let some: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TNullable(Rc::new(Type::TVar(f0.clone())))),
        )),
    );

    let list: Type<TYPE_MONO> = Type::TAbs(
        f0.clone(),
        Rc::new(Type::TNullable(Rc::new(Type::TPair(
            Rc::new(Type::TVar(f0.clone())),
            Rc::new(Type::TApp(
                Rc::new(Type::TVar(list_tv.clone())),
                Rc::new(Type::TVar(f0.clone())),
            )),
        )))),
    );
    let com: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TFun(
                Rc::new(Type::TAny(f0.loc())),
                Rc::new(Type::TVar(r0.clone())),
            )),
            Rc::new(Type::TExec(Rc::new(Type::TFun(
                Rc::new(Type::TAny(f0.loc())),
                Rc::new(Type::TVar(r0.clone())),
            )))),
        )),
    );

    // Primitive definitions
    let a_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TExec(Rc::new(Type::TFun(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )))),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TUnit(f0.loc())),
                    )),
                )),
                Rc::new(Type::TVar(r0.clone())),
            )),
        )),
    );
    let i_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TPair(
                Rc::new(Type::TAny(f0.loc())),
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TUnit(f0.loc())),
                    )),
                )),
            )),
            Rc::new(Type::TVar(f0.clone())),
        )),
    );
    let c_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(r0.clone())),
                        Rc::new(Type::TUnit(f0.loc())),
                    )),
                )),
                Rc::new(Type::TPair(
                    Rc::new(Type::TVar(f0.clone())),
                    Rc::new(Type::TVar(r0.clone())),
                )),
            )),
        )),
    );
    let f_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TNullable(Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )))),
                    Rc::new(Type::TUnit(f0.loc())),
                )),
                Rc::new(Type::TVar(f0.clone())),
            )),
        )),
    );
    let r_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TNullable(Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )))),
                    Rc::new(Type::TUnit(f0.loc())),
                )),
                Rc::new(Type::TVar(r0)),
            )),
        )),
    );
    let l_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAny(f0.loc())),
            Rc::new(Type::TUnit(f0.loc())),
        )),
        Rc::new(Type::TAtom(f0.loc(), None)),
    );
    let x_prim: Type<TYPE_MONO> =
        Type::TFun(Rc::new(Type::TAny(f0.loc())), Rc::new(Type::TAny(f0.loc())));
    let eq_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TPair(
                Rc::new(Type::TAtom(f0.loc(), None)),
                Rc::new(Type::TUnit(f0.loc())),
            )),
        )),
        Rc::new(Type::TAtom(f0.loc(), None)),
    );
    let sub_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TPair(
                Rc::new(Type::TAtom(f0.loc(), None)),
                Rc::new(Type::TUnit(f0.loc())),
            )),
        )),
        Rc::new(Type::TAtom(f0.loc(), None)),
    );
    let substr_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TPair(
                Rc::new(Type::TAtom(f0.loc(), None)),
                Rc::new(Type::TPair(
                    Rc::new(Type::TAtom(f0.loc(), None)),
                    Rc::new(Type::TUnit(f0.loc())),
                )),
            )),
        )),
        Rc::new(Type::TAtom(f0.loc(), None)),
    );
    let plus_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TApp(
            Rc::new(Type::TVar(list_tv.clone())),
            Rc::new(Type::TAtom(atom_tv.loc(), None)),
        )),
        Rc::new(Type::TAtom(atom_tv.loc(), None)),
    );
    let divmod_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TPair(
                Rc::new(Type::TAtom(f0.loc(), None)),
                Rc::new(Type::TUnit(f0.loc())),
            )),
        )),
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TAtom(f0.loc(), None)),
        )),
    );
    let strlen_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAtom(f0.loc(), None)),
            Rc::new(Type::TUnit(f0.loc())),
        )),
        Rc::new(Type::TAtom(f0.loc(), None)),
    );
    let sha256_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TApp(
            Rc::new(Type::TVar(list_tv.clone())),
            Rc::new(Type::TAtom(atom_tv.loc(), None)),
        )),
        Rc::new(Type::TAtom(atom_tv.loc(), 32_u32.to_bigint())),
    );
    let softfork_prim: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TAny(f0.loc())),
        Rc::new(Type::TUnit(f0.loc())),
    );

    Context::new(vec![
        ContextElim::CVar(Var("c^".to_string(), loc.clone()), polytype(&cons)),
        ContextElim::CVar(Var("some".to_string(), loc.clone()), polytype(&some)),
        ContextElim::CVar(Var("f^".to_string(), loc.clone()), polytype(&first)),
        ContextElim::CVar(Var("r^".to_string(), loc.clone()), polytype(&rest)),
        ContextElim::CVar(Var("a^".to_string(), loc.clone()), polytype(&apply)),
        ContextElim::CVar(Var("com^".to_string(), loc.clone()), polytype(&com)),
        ContextElim::CVar(Var("f!".to_string(), loc.clone()), polytype(&fprime)),
        ContextElim::CVar(Var("r!".to_string(), loc.clone()), polytype(&rprime)),
        ContextElim::CVar(Var("bless".to_string(), loc.clone()), polytype(&bless)),
        ContextElim::CVar(Var("@".to_string(), loc.clone()), Type::TAny(f0.loc())),
        // clvm primitives
        ContextElim::CVar(Var("a".to_string(), loc.clone()), polytype(&a_prim)),
        ContextElim::CVar(Var("i".to_string(), loc.clone()), polytype(&i_prim)),
        ContextElim::CVar(Var("c".to_string(), loc.clone()), polytype(&c_prim)),
        ContextElim::CVar(Var("f".to_string(), loc.clone()), polytype(&f_prim)),
        ContextElim::CVar(Var("r".to_string(), loc.clone()), polytype(&r_prim)),
        ContextElim::CVar(Var("l".to_string(), loc.clone()), polytype(&l_prim)),
        ContextElim::CVar(Var("x".to_string(), loc.clone()), polytype(&x_prim)),
        ContextElim::CVar(Var("=".to_string(), loc.clone()), polytype(&eq_prim)),
        ContextElim::CVar(Var(">s".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(
            Var("sha256".to_string(), loc.clone()),
            polytype(&sha256_prim),
        ),
        ContextElim::CVar(
            Var("substr".to_string(), loc.clone()),
            polytype(&substr_prim),
        ),
        ContextElim::CVar(
            Var("strlen".to_string(), loc.clone()),
            polytype(&strlen_prim),
        ),
        ContextElim::CVar(Var("concat".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("+".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("-".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(Var("*".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("/".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(
            Var("divmod".to_string(), loc.clone()),
            polytype(&divmod_prim),
        ),
        ContextElim::CVar(Var(">".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(Var("ash".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(Var("lsh".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(Var("logand".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("logior".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("logxor".to_string(), loc.clone()), polytype(&sub_prim)),
        ContextElim::CVar(
            Var("lognot".to_string(), loc.clone()),
            polytype(&strlen_prim),
        ),
        ContextElim::CVar(
            Var("point_add".to_string(), loc.clone()),
            polytype(&plus_prim),
        ),
        ContextElim::CVar(
            Var("pubkey_for_exp".to_string(), loc.clone()),
            polytype(&strlen_prim),
        ),
        ContextElim::CVar(Var("not".to_string(), loc.clone()), polytype(&strlen_prim)),
        ContextElim::CVar(Var("any".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("all".to_string(), loc.clone()), polytype(&plus_prim)),
        ContextElim::CVar(Var("softfork".to_string(), loc), polytype(&softfork_prim)),
        // Builtin types
        ContextElim::CExistsSolved(list_tv, list),
        ContextElim::CExistsSolved(unit_tv, unit),
        ContextElim::CExistsSolved(any_tv, any),
        ContextElim::CExistsSolved(atom_tv, atom),
    ])
}

fn type_of_defun(l: Srcloc, ty: &Option<Polytype>) -> Polytype {
    if let Some(ty) = ty {
        ty.clone()
    } else {
        Type::TFun(Rc::new(Type::TAny(l.clone())), Rc::new(Type::TAny(l)))
    }
}

pub fn context_from_args_and_type(
    context: &Context,
    args: Rc<SExp>,
    argty: &Polytype,
    path: Number,
    path_bit: Number,
) -> Result<Context, CompileErr> {
    match (args.borrow(), argty) {
        (SExp::Nil(_), Type::TAny(_)) => Ok(context.clone()),
        (SExp::Nil(_), Type::TUnit(_)) => Ok(context.clone()),
        (SExp::Nil(l), _) => Err(CompileErr(
            l.clone(),
            format!(
                "function has empty argument list but type {}",
                argty.to_sexp()
            ),
        )),
        (SExp::Atom(l, a), Type::TVar(TypeVar(v, vl))) => Ok(context.snoc_wf(ContextElim::CVar(
            Var(decode_string(a), l.clone()),
            Type::TVar(TypeVar(v.clone(), vl.clone())),
        ))),
        (SExp::Atom(l, a), _ty) => Ok(context.snoc_wf(ContextElim::CVar(
            Var(decode_string(a), l.clone()),
            argty.clone(),
        ))),
        (SExp::Cons(l, _, _), Type::TUnit(_)) => Err(CompileErr(
            l.clone(),
            "function has an argument list but specifies empty arguments".to_string(),
        )),
        (SExp::Cons(l, f, r), Type::TAny(_)) => {
            if let Some((_, _)) = is_at_capture(f.clone(), r.clone()) {
                if let SExp::Cons(_, sub, _) = r.borrow() {
                    let sub_context = context_from_args_and_type(
                        context,
                        sub.clone(),
                        argty,
                        path.clone(),
                        path_bit.clone(),
                    )?;
                    context_from_args_and_type(&sub_context, f.clone(), argty, path, path_bit)
                } else {
                    Err(CompileErr(l.clone(), "Bad at-tail".to_string()))
                }
            } else {
                let cf = context_from_args_and_type(
                    context,
                    f.clone(),
                    argty,
                    path.clone(),
                    path_bit.clone() * 2_u32.to_bigint().unwrap(),
                )?;
                context_from_args_and_type(
                    &cf,
                    r.clone(),
                    argty,
                    path + path_bit.clone(),
                    path_bit * 2_u32.to_bigint().unwrap(),
                )
            }
        }
        (SExp::Cons(l, f, r), Type::TPair(a, b)) => {
            if let Some((_, _)) = is_at_capture(f.clone(), r.clone()) {
                if let SExp::Cons(_, sub, _) = r.borrow() {
                    let sub_context = context_from_args_and_type(
                        context,
                        sub.clone(),
                        argty,
                        path.clone(),
                        path_bit.clone(),
                    )?;
                    context_from_args_and_type(&sub_context, f.clone(), argty, path, path_bit)
                } else {
                    Err(CompileErr(l.clone(), "Bad at-tail".to_string()))
                }
            } else {
                let cf = context_from_args_and_type(
                    context,
                    f.clone(),
                    a.borrow(),
                    bi_zero(),
                    bi_one(),
                )?;
                context_from_args_and_type(
                    &cf,
                    r.clone(),
                    b.borrow(),
                    path + path_bit.clone(),
                    path_bit * 2_u32.to_bigint().unwrap(),
                )
            }
        }
        _ => Err(CompileErr(
            args.loc(),
            format!("unhandled case {} vs {}", args, argty.to_sexp()),
        )),
    }
}

fn handle_macro(
    program: &CompileForm,
    form_args: Rc<SExp>,
    _args: Rc<SExp>,
    form: Rc<CompileForm>,
    loc: Srcloc,
    provided_args: &[Rc<BodyForm>],
) -> Result<Expr, CompileErr> {
    // It is a macro, we need to interpret it in our way:
    // We'll compile and run the code itself on a
    // representation of the argument list and return the
    // result.  We'll interpret the result in the following
    // but we'll treat com as com^ whose type will be
    // (forall s (forall t (t -> (Exec (s -> t)))))
    // Given an 'a' operator:
    // (forall s
    //   (forall t
    //     ((Pair (Exec (s -> t)) (Pair s ())) -> t)
    //     )
    //    )
    // And given a well typed 'i' operator:
    // (forall t ((Pair Any (Pair t (Pair t ()))) -> t))
    // We should be able to type things that come our way
    let call_args: Vec<Rc<BodyForm>> = provided_args
        .iter()
        .skip(1)
        .map(|x| {
            let literal = x.to_sexp();
            let literal_borrowed: &SExp = literal.borrow();
            Rc::new(BodyForm::Quoted(literal_borrowed.clone()))
        })
        .collect();
    let opts = Rc::new(DefaultCompilerOpts::new(&loc.file.to_string()));
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut ev = Evaluator::new(opts.clone(), runner, program.helpers.clone());
    for h in form.helpers.iter() {
        ev.add_helper(h);
    }
    let mut allocator = Allocator::new();
    let arg_env = build_argument_captures(&loc, &call_args, form.args.clone())?;
    let result = ev.shrink_bodyform(
        &mut allocator,
        Rc::new(SExp::Nil(loc.clone())),
        &arg_env,
        form.exp.clone(),
        true,
    )?;
    let parsed_macro_output = frontend(opts.clone(), &[result.to_sexp()])?;
    let exp_result = ev.shrink_bodyform(
        &mut allocator,
        Rc::new(SExp::Nil(loc.clone())),
        &arg_env,
        parsed_macro_output.exp,
        false,
    )?;
    match dequote(loc.clone(), exp_result) {
        Ok(dequoted) => {
            let last_reparse = frontend(opts, &[dequoted])?;
            let final_res = chialisp_to_expr(program, form_args, last_reparse.exp)?;
            Ok(final_res)
        }
        Err(_) => {
            // Give up: we can't do better than Any
            Ok(Expr::EAnno(
                Rc::new(Expr::EUnit(loc.clone())),
                Type::TAny(loc),
            ))
        }
    }
}

fn chialisp_to_expr(
    program: &CompileForm,
    form_args: Rc<SExp>,
    body: Rc<BodyForm>,
) -> Result<Expr, CompileErr> {
    match body.borrow() {
        BodyForm::Quoted(SExp::Nil(l)) => Ok(Expr::EUnit(l.clone())),
        BodyForm::Quoted(SExp::Integer(l, i)) => {
            let v = u8_from_number(i.clone());
            Ok(Expr::ELit(l.clone(), v.len().to_bigint().unwrap()))
        }
        BodyForm::Quoted(SExp::QuotedString(l, _, v)) => {
            Ok(Expr::ELit(l.clone(), v.len().to_bigint().unwrap()))
        }
        BodyForm::Quoted(SExp::Cons(l, a, b)) => {
            let a_borrowed: &SExp = a.borrow();
            let b_borrowed: &SExp = b.borrow();
            Ok(Expr::EApp(
                Rc::new(Expr::EApp(
                    Rc::new(Expr::EVar(Var("c^".to_string(), l.clone()))),
                    Rc::new(chialisp_to_expr(
                        program,
                        form_args.clone(),
                        Rc::new(BodyForm::Quoted(a_borrowed.clone())),
                    )?),
                )),
                Rc::new(chialisp_to_expr(
                    program,
                    form_args,
                    Rc::new(BodyForm::Quoted(b_borrowed.clone())),
                )?),
            ))
        }
        BodyForm::Value(SExp::Nil(l)) => Ok(Expr::EUnit(l.clone())),
        BodyForm::Value(SExp::Integer(l, i)) => {
            let v = u8_from_number(i.clone());
            Ok(Expr::ELit(l.clone(), v.len().to_bigint().unwrap()))
        }
        BodyForm::Value(SExp::Atom(l, n)) => Ok(Expr::EVar(Var(decode_string(n), l.clone()))),
        BodyForm::Let(_, letdata) => {
            // Inline via the evaluator
            let mut allocator = Allocator::new();
            let file_borrowed: &String = letdata.loc.file.borrow();
            let opts = Rc::new(DefaultCompilerOpts::new(file_borrowed));
            let runner = Rc::new(DefaultProgramRunner::new());
            let evaluator = Evaluator::new(opts, runner, program.helpers.clone()).disable_calls();
            let beta_reduced = evaluator.shrink_bodyform(
                &mut allocator,
                Rc::new(SExp::Nil(letdata.loc.clone())),
                &HashMap::new(),
                body.clone(),
                false,
            )?;
            chialisp_to_expr(program, form_args, beta_reduced)
        }
        BodyForm::Call(l, lst) => {
            let mut arg_expr = Expr::EUnit(l.clone());
            for i_rev in 0..lst.len() - 1 {
                let i = lst.len() - i_rev - 1;
                let new_expr = chialisp_to_expr(program, form_args.clone(), lst[i].clone())?;
                arg_expr = Expr::EApp(
                    Rc::new(Expr::EApp(
                        Rc::new(Expr::EVar(Var("c^".to_string(), l.clone()))),
                        Rc::new(new_expr),
                    )),
                    Rc::new(arg_expr),
                );
            }
            if let BodyForm::Value(SExp::Atom(_, n1)) = &lst[0].borrow() {
                // Find out if it's a macro
                for h in program.helpers.iter() {
                    if let HelperForm::Defmacro(defm) = &h {
                        if defm.name == *n1 {
                            return handle_macro(
                                program,
                                form_args,
                                defm.args.clone(),
                                defm.program.clone(),
                                body.loc(),
                                lst,
                            );
                        }
                    }
                }

                if n1 == &vec![b'c', b'o', b'm'] {
                    // Handle com
                    // Rewrite (com X) as (com^ (lambda x X))
                    let inner = chialisp_to_expr(program, form_args, lst[1].clone())?;
                    let var = fresh_var(l.clone());
                    return Ok(Expr::EApp(
                        Rc::new(Expr::EVar(Var("com^".to_string(), l.clone()))),
                        Rc::new(Expr::EAbs(var, Rc::new(inner))),
                    ));
                }
            }

            // Just treat it as an expression...  If it's a function we defined,
            // then it's in the environment.
            Ok(Expr::EApp(
                Rc::new(chialisp_to_expr(program, form_args, lst[0].clone())?),
                Rc::new(arg_expr),
            ))
        }
        _ => Err(CompileErr(
            body.loc(),
            format!("not sure how to handle {:?} yet", body),
        )),
    }
}

fn typecheck_chialisp_body_with_context(
    context_: &Context,
    expr: &Expr,
) -> Result<Polytype, CompileErr> {
    let res = context_.typesynth(expr).map(|(res, _)| res)?;
    Ok(res)
}

fn handle_function_type(
    context: &Context,
    loc: Srcloc,
    args: Rc<SExp>,
    ty: &Polytype,
) -> Result<(Context, Polytype), CompileErr> {
    match ty {
        Type::TFun(a, r) => {
            let r_borrowed: &Polytype = r.borrow();
            context_from_args_and_type(context, args, a.borrow(), bi_zero(), bi_one())
                .map(|ctx| (ctx, r_borrowed.clone()))
        }
        Type::TForall(t, f) => {
            let inner_ctx = context.snoc_wf(ContextElim::CForall(t.clone()));
            let f_borrowed: &Polytype = f.borrow();
            handle_function_type(&inner_ctx, loc, args, f_borrowed)
        }
        _ => Err(CompileErr(
            loc,
            "Type of a defun must be a function type".to_string(),
        )),
    }
}

// Given a compileform, typecheck
impl Context {
    pub fn typecheck_chialisp_program(&self, comp: &CompileForm) -> Result<Polytype, CompileErr> {
        let mut context = self.clone();

        // Extract type definitions
        for h in comp.helpers.iter() {
            if let HelperForm::Deftype(deft) = &h {
                let tname = decode_string(&deft.name);
                let n_encoding = number_from_u8(format!("struct {}", tname).as_bytes());
                // Ensure that we build up a unique type involving all variables so we won't try to solve it to some specific type
                let mut result_ty = Type::TAtom(h.loc(), Some(n_encoding));
                for a in deft.args.iter().rev() {
                    result_ty = Type::TPair(Rc::new(Type::TVar(a.clone())), Rc::new(result_ty));
                }
                result_ty = Type::TExec(Rc::new(result_ty));
                for a in deft.args.iter().rev() {
                    result_ty = Type::TAbs(a.clone(), Rc::new(result_ty));
                }
                let exists_solved =
                    ContextElim::CExistsSolved(TypeVar(tname.clone(), deft.loc.clone()), result_ty);
                debug!(
                    "struct exists_solved {}",
                    exists_solved.to_sexp().to_string()
                );
                context = context.appends_wf(vec![exists_solved]);
            }
        }

        // Extract constants
        for h in comp.helpers.iter() {
            if let HelperForm::Defconstant(defc) = &h {
                let tname = decode_string(&defc.name);
                if let Some(ty) = &defc.ty {
                    context = context
                        .snoc_wf(ContextElim::CVar(Var(tname, defc.loc.clone()), ty.clone()));
                } else {
                    context = context.snoc_wf(ContextElim::CVar(
                        Var(tname, defc.loc.clone()),
                        Type::TAny(defc.loc.clone()),
                    ));
                }
            }
        }

        // Extract functions
        for h in comp.helpers.iter() {
            if let HelperForm::Defun(_, defun) = &h {
                let tname = decode_string(&defun.name);
                let ty = type_of_defun(defun.loc.clone(), &defun.ty);
                context = context.snoc_wf(ContextElim::CVar(Var(tname, defun.loc.clone()), ty));
            }
        }

        // Typecheck helper functions
        for h in comp.helpers.iter() {
            if let HelperForm::Defun(_, defun) = &h {
                let ty = type_of_defun(defun.loc.clone(), &defun.ty);
                let (context_with_args, result_ty) =
                    handle_function_type(&context, h.loc(), defun.args.clone(), &ty)?;
                typecheck_chialisp_body_with_context(
                    &context_with_args,
                    &Expr::EAnno(
                        Rc::new(chialisp_to_expr(
                            comp,
                            defun.args.clone(),
                            defun.body.clone(),
                        )?),
                        result_ty,
                    ),
                )?;
            }
        }

        // Typecheck main expression
        let ty = type_of_defun(comp.exp.loc(), &comp.ty);
        let (context_with_args, result_ty) =
            handle_function_type(&context, comp.exp.loc(), comp.args.clone(), &ty)?;
        let clexpr = chialisp_to_expr(comp, comp.args.clone(), comp.exp.clone())?;
        typecheck_chialisp_body_with_context(
            &context_with_args,
            &Expr::EAnno(Rc::new(clexpr), result_ty),
        )
    }
}
