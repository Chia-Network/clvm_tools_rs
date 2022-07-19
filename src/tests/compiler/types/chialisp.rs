use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{
    CompileErr
};
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::typechia::{
    context_from_args_and_type,
    standard_type_context
};
use crate::compiler::types::ast::{
    Polytype,
    Type,
    TypeVar
};
use crate::tests::compiler::types::types::{
    check_expression_against_type_with_context
};

#[test]
fn test_chialisp_context_from_args_and_type_empty() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Nil(loc.clone())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "()",
        "Unit",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_atom_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any_pair() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_arg_with_list_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TApp(
            Rc::new(Type::TAtom(loc.clone(), None)),
            Rc::new(Type::TVar(TypeVar("List".to_string(), loc.clone())))
        ),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "(Atom List)",
        false
    );
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_with_pair_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone()))
        )),
        &Type::TPair(
            Rc::new(Type::TAtom(loc.clone(), None)),
            Rc::new(Type::TUnit(loc.clone()))
        ),
        bi_zero(),
        bi_one()
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "Atom",
        false
    );
}

fn test_chialisp_program_typecheck(s: &str) -> Result<Polytype, CompileErr> {
    let testname = "*test*".to_string();
    let loc = Srcloc::start(&testname);
    let context = standard_type_context();
    let opts = DefaultCompilerOpts::new(&testname);
    let pre_forms = parse_sexp(loc.clone(), &s.to_string()).
        map_err(|e| CompileErr(e.0, e.1))?;
    let compileform = frontend(Rc::new(opts), pre_forms)?;
    let _ = println!("compileform ty {:?}", compileform.ty);
    context.typecheck_chialisp_program(&compileform)
}

#[test]
fn test_chialisp_program_returning_unit_no_anno() {
    let ty = test_chialisp_program_typecheck(
        "(mod () ())"
    ).expect("should type check");
    assert_eq!(ty, Type::TAny(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_unit_annotation() {
    let ty = test_chialisp_program_typecheck(
        "(mod () : (Unit -> Unit) ())"
    ).expect("should type check");
    assert_eq!(ty, Type::TUnit(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_one_atom_annotation() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X) : ((Pair Atom Unit) -> Atom) X)"
    ).expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}
