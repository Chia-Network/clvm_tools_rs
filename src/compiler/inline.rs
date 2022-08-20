use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::codegen::{generate_expr_code, get_call_name, get_callable};
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    BodyForm, Callable, CompileErr, CompiledCode, CompilerOpts, InlineFunction, PrimaryCodegen,
};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

use crate::util::Number;

fn apply_fn(loc: Srcloc, name: String, expr: Rc<BodyForm>) -> Rc<BodyForm> {
    Rc::new(BodyForm::Call(
        loc.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), &name))),
            expr,
        ],
    ))
}

fn at_form(loc: Srcloc, path: Number) -> Rc<BodyForm> {
    apply_fn(
        loc.clone(),
        "@".to_string(),
        Rc::new(BodyForm::Value(SExp::Integer(loc.clone(), path.clone()))),
    )
}

pub fn synthesize_args(arg_: Rc<SExp>) -> Vec<Rc<BodyForm>> {
    let mut start = 5_i32.to_bigint().unwrap();
    let mut result = Vec::new();
    let mut arg = arg_.clone();
    loop {
        match arg.borrow() {
            SExp::Cons(l, _, b) => {
                result.push(at_form(l.clone(), start.clone()));
                start = bi_one() + start.clone() * 2_i32.to_bigint().unwrap();
                arg = b.clone();
            }
            _ => {
                return result;
            }
        }
    }
}

fn enlist_remaining_args(loc: Srcloc, arg_choice: usize, args: &Vec<Rc<BodyForm>>) -> Rc<BodyForm> {
    let mut result_body = BodyForm::Value(SExp::Nil(loc.clone()));

    for i_reverse in arg_choice..args.len() {
        let i = args.len() - i_reverse - 1;
        result_body = BodyForm::Call(
            loc.clone(),
            vec![
                Rc::new(BodyForm::Value(SExp::atom_from_string(
                    loc.clone(),
                    &"c".to_string(),
                ))),
                args[i].clone(),
                Rc::new(result_body),
            ],
        );
    }

    Rc::new(result_body)
}

fn pick_value_from_arg_element(
    match_args: Rc<SExp>,
    provided: Rc<BodyForm>,
    apply: &dyn Fn(Rc<BodyForm>) -> Rc<BodyForm>,
    name: Vec<u8>,
) -> Option<Rc<BodyForm>> {
    match match_args.borrow() {
        SExp::Cons(l, a, b) => {
            if let Some((capture, children)) = is_at_capture(a.clone(), b.clone()) {
                if capture == name {
                    return Some(apply(provided));
                }

                return pick_value_from_arg_element(children, provided.clone(), apply, name);
            }
            let matched_a = pick_value_from_arg_element(
                a.clone(),
                provided.clone(),
                &|x| apply_fn(l.clone(), "f".to_string(), apply(x.clone())),
                name.clone(),
            );
            let matched_b = pick_value_from_arg_element(
                b.clone(),
                provided.clone(),
                &|x| apply_fn(l.clone(), "r".to_string(), apply(x.clone())),
                name.clone(),
            );

            let result = match (matched_a, matched_b) {
                (Some(a), _) => Some(a),
                (_, Some(b)) => Some(b),
                _ => None,
            };

            result
        }
        SExp::Atom(_l, a) => {
            if *a == name {
                Some(apply(provided))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn arg_lookup(
    match_args: Rc<SExp>,
    arg_choice: usize,
    args: &Vec<Rc<BodyForm>>,
    name: Vec<u8>,
) -> Option<Rc<BodyForm>> {
    match match_args.borrow() {
        SExp::Cons(_l, f, r) => {
            match pick_value_from_arg_element(
                f.clone(),
                args[arg_choice].clone(),
                &|x| x.clone(),
                name.clone(),
            ) {
                Some(x) => Some(x),
                None => arg_lookup(r.clone(), arg_choice + 1, args, name.clone()),
            }
        }
        _ => pick_value_from_arg_element(
            match_args.clone(),
            enlist_remaining_args(match_args.loc(), arg_choice, args),
            &|x: Rc<BodyForm>| x.clone(),
            name,
        ),
    }
}

fn get_inline_callable(
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    list_head: Rc<BodyForm>,
) -> Result<Callable, CompileErr> {
    let list_head_borrowed: &BodyForm = list_head.borrow();
    let name = get_call_name(loc.clone(), list_head_borrowed.clone())?;
    get_callable(opts, compiler, loc.clone(), name.clone())
}

fn replace_inline_body(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    inline: &InlineFunction,
    args: &Vec<Rc<BodyForm>>,
    expr: Rc<BodyForm>,
) -> Result<Rc<BodyForm>, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(_l, _, _, _) => Err(CompileErr(
            loc.clone(),
            "let binding should have been hoisted before optimization".to_string(),
        )),
        BodyForm::Call(l, call_args) => {
            let mut new_args = Vec::new();
            for i in 0..call_args.len() {
                if i == 0 {
                    new_args.push(call_args[i].clone());
                } else {
                    let replaced = replace_inline_body(
                        allocator,
                        runner.clone(),
                        opts.clone(),
                        compiler,
                        call_args[i].loc(),
                        inline,
                        &args.clone(),
                        call_args[i].clone(),
                    )?;
                    new_args.push(replaced);
                }
            }
            // If the called function is an inline, we'll expand it here.
            // This is so we can preserve the context of argument expressions
            // so no new mapping is needed.  This solves a number of problems
            // with the previous implementation.
            //
            // If it's a macro we'll expand it here so we can recurse and
            // determine whether an inline is the next level.
            match get_inline_callable(opts.clone(), compiler, l.clone(), call_args[0].clone())? {
                Callable::CallInline(_, new_inline) => {
                    let pass_on_args: Vec<Rc<BodyForm>> =
                        new_args.iter().skip(1).map(|x| x.clone()).collect();
                    replace_inline_body(
                        allocator,
                        runner,
                        opts.clone(),
                        compiler,
                        l.clone(),
                        &new_inline,
                        &pass_on_args,
                        new_inline.body.clone(),
                    )
                }
                _ => {
                    let call = BodyForm::Call(l.clone(), new_args);
                    Ok(Rc::new(call))
                }
            }
        }
        BodyForm::Value(SExp::Atom(_, a)) => {
            let alookup = arg_lookup(inline.args.clone(), 0, args, a.clone())
                .map(|x| Ok(x.clone()))
                .unwrap_or_else(|| Ok(expr.clone()))?;
            Ok(alookup)
        }
        _ => Ok(expr.clone()),
    }
}

pub fn replace_in_inline(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    inline: &InlineFunction,
    args: &Vec<Rc<BodyForm>>,
) -> Result<CompiledCode, CompileErr> {
    replace_inline_body(
        allocator,
        runner.clone(),
        opts.clone(),
        compiler,
        loc.clone(),
        inline,
        args,
        inline.body.clone(),
    )
    .and_then(|x| generate_expr_code(allocator, runner, opts, compiler, x.clone()))
}
