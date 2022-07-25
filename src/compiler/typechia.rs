use std::borrow::Borrow;
use std::collections::{HashSet};
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::compiler::{
    DefaultCompilerOpts,
    is_at_capture
};
use crate::compiler::comptypes::{
    BodyForm,
    CompileErr,
    CompileForm,
    HelperForm
};
use crate::compiler::evaluate::{
    Evaluator,
    build_argument_captures,
    dequote
};
use crate::compiler::frontend::frontend;
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
    Polytype,
    TYPE_MONO,
    Type,
    TypeVar,
    Var
};
use crate::compiler::types::namegen::fresh_var;
use crate::compiler::types::astfuns::{monotype, polytype};
use crate::compiler::types::theory::TypeTheory;
use crate::util::{Number, u8_from_number};

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
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TVar(f0.clone())),
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
    let applyany: Type<TYPE_MONO> = Type::TFun(
        Rc::new(Type::TPair(
            Rc::new(Type::TAny(f0.loc())),
            Rc::new(Type::TPair(
                Rc::new(Type::TAny(f0.loc())),
                Rc::new(Type::TUnit(f0.loc()))
            ))
        )),
        Rc::new(Type::TAny(f0.loc()))
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
    let com: Type<TYPE_MONO> = Type::TForall(
        r0.clone(),
        Rc::new(Type::TFun(
            Rc::new(Type::TFun(
                Rc::new(Type::TAny(f0.loc())),
                Rc::new(Type::TVar(r0.clone()))
            )),
            Rc::new(Type::TExec(
                Rc::new(Type::TFun(
                    Rc::new(Type::TAny(f0.loc())),
                    Rc::new(Type::TVar(r0.clone()))
                ))
            ))
        ))
    );

    // Primitive definitions
    let a_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TExec(
                        Rc::new(Type::TFun(
                            Rc::new(Type::TVar(f0.clone())),
                            Rc::new(Type::TVar(r0.clone()))
                        ))
                    )),
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TUnit(f0.loc()))
                    ))
                )),
                Rc::new(Type::TVar(r0.clone()))
            ))
        ))
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
                        Rc::new(Type::TUnit(f0.loc()))
                    ))
                ))
            )),
            Rc::new(Type::TVar(f0.clone()))
        ))
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
    let f_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )),
                    Rc::new(Type::TUnit(f0.loc()))
                )),
                Rc::new(Type::TVar(f0.clone()))
            ))
        ))
    );
    let r_prim: Type<TYPE_MONO> = Type::TForall(
        f0.clone(),
        Rc::new(Type::TForall(
            r0.clone(),
            Rc::new(Type::TFun(
                Rc::new(Type::TPair(
                    Rc::new(Type::TPair(
                        Rc::new(Type::TVar(f0.clone())),
                        Rc::new(Type::TVar(r0.clone())),
                    )),
                    Rc::new(Type::TUnit(f0.loc()))
                )),
                Rc::new(Type::TVar(r0.clone()))
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
        ContextElim::CVar(Var("f^".to_string(), loc.clone()), polytype(&first)),
        ContextElim::CVar(Var("r^".to_string(), loc.clone()), polytype(&rest)),
        ContextElim::CVar(Var("a^".to_string(), loc.clone()), polytype(&apply)),
        ContextElim::CVar(Var("a*".to_string(), loc.clone()), polytype(&applyany)),
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
    structs: &HashSet<String>,
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
        (SExp::Atom(l,a), Type::TVar(TypeVar(v,vl))) => {
            Ok(context.snoc_wf(
                ContextElim::CVar(
                    Var(decode_string(a), l.clone()),
                    Type::TVar(TypeVar(v.clone(),vl.clone()))
                )
            ))
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
                    structs,
                    context,
                    f.clone(),
                    argty,
                    path.clone(),
                    path_bit.clone() * 2_u32.to_bigint().unwrap()
                )?;
                context_from_args_and_type(
                    structs,
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
                    structs,
                    context,
                    f.clone(),
                    a.borrow(),
                    bi_zero(),
                    bi_one()
                )?;
                context_from_args_and_type(
                    structs,
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

fn make_offsides_protection(set: &mut HashSet<Vec<u8>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Atom(_,n) => { set.insert(n.clone()); },
        SExp::Cons(_,a,b) => {
            make_offsides_protection(set, a.clone());
            make_offsides_protection(set, b.clone());
        },
        _ => { }
    }
}

fn enquote_offsides_expressions_tail(
    protected_atoms: &HashSet<Vec<u8>>,
    input: Rc<SExp>
) -> Rc<SExp> {
    match input.borrow() {
        SExp::Cons(l,a,b) => {
            let first = enquote_offsides_expressions(protected_atoms, a.clone());
            let rest = enquote_offsides_expressions_tail(protected_atoms, b.clone());
            Rc::new(SExp::Cons(
                l.clone(),
                first,
                rest
            ))
        },
        _ => enquote_offsides_expressions(protected_atoms, input)
    }
}

// Fixup output from a macro to ensure that it can be shrunk to real chialisp
// code.  This is distinct from 'clvm' code in that we'll enquote anything output
// that is used "as" chialisp code.  This includes any unguarded atoms in the
// output.
//
// A subsequent layer will handle "com" specially, turning it into
// (com X) -> (com^ (lambda x X))
fn enquote_offsides_expressions(
    protected_atoms: &HashSet<Vec<u8>>,
    input: Rc<SExp>
) -> Rc<SExp> {
    match input.borrow() {
        SExp::Atom(l,n) => {
            if protected_atoms.contains(n) {
                Rc::new(SExp::Cons(
                    l.clone(),
                    Rc::new(SExp::Atom(l.clone(),vec![b'q'])),
                    input.clone()
                ))
            } else {
                input.clone()
            }
        },
        SExp::Cons(l,a,b) => {
            let new_b = enquote_offsides_expressions_tail(
                protected_atoms, b.clone()
            );
            Rc::new(SExp::Cons(
                l.clone(),
                a.clone(),
                new_b
            ))
        },
        _ => { input.clone() }
    }
}

fn handle_macro(
    program: &CompileForm,
    form_args: Rc<SExp>,
    args: Rc<SExp>,
    form: Rc<CompileForm>,
    loc: Srcloc,
    provided_args: &Vec<Rc<BodyForm>>
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
    let call_args: Vec<Rc<BodyForm>> =
        provided_args.iter().skip(1).map(|x| {
            let literal = x.to_sexp();
            let literal_borrowed: &SExp = literal.borrow();
            Rc::new(BodyForm::Quoted(literal_borrowed.clone()))
        }).collect();
    let opts = Rc::new(DefaultCompilerOpts::new(&loc.file.to_string()));
    let runner = Rc::new(DefaultProgramRunner::new());
    let ev = Evaluator::new(
        opts.clone(),
        runner,
        program.helpers.clone()
    );
    let mut allocator = Allocator::new();
    let arg_env = build_argument_captures(
        &loc,
        &call_args,
        form.args.clone()
    )?;
    let result = ev.shrink_bodyform(
        &mut allocator,
        Rc::new(SExp::Nil(loc.clone())),
        &arg_env,
        form.exp.clone(),
        true
    )?;
    let mut offsides = HashSet::new();
    // make_offsides_protection(&mut offsides, form_args.clone());
    let parsed_macro_output = frontend(opts.clone(), vec![enquote_offsides_expressions(&offsides, result.to_sexp())])?;
    let exp_result = ev.shrink_bodyform(
        &mut allocator,
        Rc::new(SExp::Nil(loc.clone())),
        &arg_env,
        parsed_macro_output.exp.clone(),
        false
    )?;
    match dequote(loc.clone(), exp_result) {
        Ok(dequoted) => {
            let last_reparse = frontend(opts, vec![dequoted])?;
            let final_res = chialisp_to_expr(
                program,
                form_args,
                last_reparse.exp.clone()
            )?;
            Ok(final_res)
        },
        Err(_) => {
            // Give up: we can't do better than Any
            Ok(Expr::EAnno(
                Rc::new(Expr::EUnit(loc.clone())),
                Type::TAny(loc.clone())
            ))
        }
    }
}

fn chialisp_to_expr(
    program: &CompileForm,
    form_args: Rc<SExp>,
    body: Rc<BodyForm>
) -> Result<Expr, CompileErr> {
    match body.borrow() {
        BodyForm::Quoted(SExp::Nil(l)) => { Ok(Expr::EUnit(l.clone())) },
        BodyForm::Quoted(SExp::Integer(l,i)) => {
            let v = u8_from_number(i.clone());
            Ok(Expr::ELit(l.clone(), v.len().to_bigint().unwrap()))
        },
        BodyForm::Value(SExp::Nil(l)) => { Ok(Expr::EUnit(l.clone())) },
        BodyForm::Value(SExp::Integer(l,i)) => {
            let v = u8_from_number(i.clone());
            Ok(Expr::ELit(l.clone(), v.len().to_bigint().unwrap()))
        },
        BodyForm::Value(SExp::Atom(l,n)) => {
            Ok(Expr::EVar(Var(decode_string(n), l.clone())))
        },
        BodyForm::Call(l,lst) => {
            let mut arg_expr = Expr::EUnit(l.clone());
            for i_rev in 0..lst.len() - 1 {
                let i = lst.len() - i_rev - 1;
                let new_expr = chialisp_to_expr(program, form_args.clone(), lst[i].clone())?;
                arg_expr = Expr::EApp(
                    Rc::new(Expr::EApp(
                        Rc::new(Expr::EVar(Var("c^".to_string(), l.clone()))),
                        Rc::new(new_expr)
                    )),
                    Rc::new(arg_expr)
                );
            }
            if let BodyForm::Value(SExp::Atom(l1,n1)) = &lst[0].borrow() {
                // Find out if it's a macro
                for h in program.helpers.iter() {
                    if let HelperForm::Defmacro(l, name, args, form) = &h {
                        if name == n1 {
                            return handle_macro(
                                program,
                                form_args.clone(),
                                args.clone(),
                                form.clone(),
                                body.loc(),
                                &lst
                            );
                        }
                    }
                }

                if n1 == &vec![b'c',b'o',b'm'] {
                    // Handle com
                    // Rewrite (com X) as (com^ (lambda x X))
                    let inner = chialisp_to_expr(program, form_args.clone(), lst[1].clone())?;
                    let var = fresh_var(l.clone());
                    return Ok(Expr::EApp(
                        Rc::new(Expr::EVar(Var("com^".to_string(), l.clone()))),
                        Rc::new(Expr::EAbs(var, Rc::new(inner)))
                    ));
                }
            }

            // Just treat it as an expression...  If it's a function we defined,
            // then it's in the environment.
            Ok(Expr::EApp(
                Rc::new(chialisp_to_expr(program, form_args.clone(), lst[0].clone())?),
                Rc::new(arg_expr)
            ))
        },
        _ => todo!("not sure how to handle {:?} yet", body)
    }
}

fn typecheck_chialisp_body_with_context(
    context_: &Context,
    expr: &Expr
) -> Result<Polytype, CompileErr> {
    let res = context_.typesynth(&expr).map(|(res,_)| res)?;
    Ok(res)
}

fn handle_function_type(
    structs: &HashSet<String>,
    context: &Context,
    loc: Srcloc,
    args: Rc<SExp>,
    ty: &Polytype
) -> Result<(Context, Polytype), CompileErr> {
    match ty {
        Type::TFun(a,r) => {
            let r_borrowed: &Polytype = r.borrow();
            context_from_args_and_type(
                &structs,
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
            handle_function_type(&structs, &inner_ctx, loc, args, f_borrowed)
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
        let mut structs = HashSet::new();

        // Extract type definitions
        for h in comp.helpers.iter() {
            if let HelperForm::Deftype(l, name, args, ty) = &h {
                let tname = decode_string(name);
                match ty {
                    None => { // Abstract
                        context = context.appends_wf(vec![
                            ContextElim::CForall(TypeVar(tname.clone(),l.clone()))
                        ]);
                    },
                    Some(t) => { // Struct
                        structs.insert(tname.clone());
                        context = context.appends_wf(vec![
                            ContextElim::CForall(TypeVar(tname.clone(),l.clone()))
                        ]);
                    }
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
                    handle_function_type(
                        &structs,
                        &context,
                        h.loc(),
                        args.clone(),
                        &ty
                    )?;
                typecheck_chialisp_body_with_context(
                    &context_with_args,
                    &Expr::EAnno(
                        Rc::new(chialisp_to_expr(comp, args.clone(), body.clone())?),
                        result_ty
                    )
                )?;
            }
        }

        // Typecheck main expression
        let ty = type_of_defun(comp.exp.loc(), &comp.ty);
        let (context_with_args, result_ty) =
            handle_function_type(
                &structs,
                &context,
                comp.exp.loc(),
                comp.args.clone(),
                &ty
            )?;
        let clexpr = chialisp_to_expr(comp, comp.args.clone(), comp.exp.clone())?;
        typecheck_chialisp_body_with_context(
            &context_with_args,
            &Expr::EAnno(
                Rc::new(clexpr),
                result_ty
            )
        )
    }
}
