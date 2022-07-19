use std::rc::Rc;

use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::typechia::{
    context_from_args_and_type,
    standard_type_context
};
use crate::compiler::types::ast::Type;
use crate::tests::compiler::types::types::{
    check_expression_against_type_with_context
};

#[test]
fn test_chialisp_context_from_args_and_type_empty() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &standard_type_context(),
        Rc::new(SExp::Nil(loc.clone())),
        &Type::TAny(loc.clone())
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
        &Type::TAny(loc.clone())
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
        &Type::TAny(loc.clone())
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
        &Type::TAny(loc.clone())
    ).expect("should synthesize a context");
    println!("context {}", context.to_sexp().to_string());
    check_expression_against_type_with_context(
        &context,
        "X",
        "Any",
        false
    );
}
