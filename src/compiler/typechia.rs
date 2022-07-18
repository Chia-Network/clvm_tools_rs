use std::rc::Rc;

use crate::compiler::comptypes::{CompileErr, CompileForm};
use crate::compiler::srcloc::{Srcloc, HasLoc};
use crate::compiler::types::ast::{
    Context,
    ContextElim,
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

// Given a compileform, typecheck
impl Context {
    pub fn typecheck_chialisp_program(
        &self, comp: CompileForm
    ) -> Result<(), CompileErr> {
        Ok(())
    }
}
