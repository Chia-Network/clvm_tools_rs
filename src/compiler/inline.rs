use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::codegen::{generate_expr_code, get_call_name, get_callable};
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    BodyForm, Callable, CompileErr, CompiledCode, CompilerOpts, InlineFunction, LambdaData,
    PrimaryCodegen,
};
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;

use crate::util::Number;

fn apply_fn(loc: Srcloc, name: String, expr: Rc<BodyForm>) -> Rc<BodyForm> {
    Rc::new(BodyForm::Call(
        loc.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::atom_from_string(loc, &name))),
            expr,
        ],
    ))
}

fn at_form(loc: Srcloc, path: Number) -> Rc<BodyForm> {
    apply_fn(
        loc.clone(),
        "@".to_string(),
        Rc::new(BodyForm::Value(SExp::Integer(loc, path))),
    )
}

pub fn synthesize_args(arg_: Rc<SExp>) -> Vec<Rc<BodyForm>> {
    let mut start = 5_i32.to_bigint().unwrap();
    let mut result = Vec::new();
    let mut arg = arg_;
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

fn enlist_remaining_args(loc: Srcloc, arg_choice: usize, args: &[Rc<BodyForm>]) -> Rc<BodyForm> {
    let mut result_body = BodyForm::Value(SExp::Nil(loc.clone()));

    for i_reverse in arg_choice..args.len() {
        let i = args.len() - i_reverse - 1;
        result_body = BodyForm::Call(
            loc.clone(),
            vec![
                Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), "c"))),
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

                return pick_value_from_arg_element(children, provided, apply, name);
            }
            let matched_a = pick_value_from_arg_element(
                a.clone(),
                provided.clone(),
                &|x| apply_fn(l.clone(), "f".to_string(), apply(x)),
                name.clone(),
            );
            let matched_b = pick_value_from_arg_element(
                b.clone(),
                provided,
                &|x| apply_fn(l.clone(), "r".to_string(), apply(x)),
                name,
            );

            match (matched_a, matched_b) {
                (Some(a), _) => Some(a),
                (_, Some(b)) => Some(b),
                _ => None,
            }
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
    callsite: Srcloc,
    match_args: Rc<SExp>,
    arg_choice: usize,
    args: &[Rc<BodyForm>],
    name: Vec<u8>,
) -> Result<Option<Rc<BodyForm>>, CompileErr> {
    match match_args.borrow() {
        SExp::Cons(_l, f, r) => {
            if arg_choice >= args.len() {
                return Err(CompileErr(
                    callsite,
                    format!("Lookup for argument {} that wasn't passed", arg_choice + 1),
                ));
            }

            match pick_value_from_arg_element(
                f.clone(),
                args[arg_choice].clone(),
                &|x| x,
                name.clone(),
            ) {
                Some(x) => Ok(Some(x)),
                None => arg_lookup(callsite, r.clone(), arg_choice + 1, args, name),
            }
        }
        _ => Ok(pick_value_from_arg_element(
            match_args.clone(),
            enlist_remaining_args(match_args.loc(), arg_choice, args),
            &|x: Rc<BodyForm>| x,
            name,
        )),
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
    get_callable(opts, compiler, loc, name)
}

#[allow(clippy::too_many_arguments)]
fn replace_inline_body(
    visited_inlines: &mut HashSet<Vec<u8>>,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    inline: &InlineFunction,
    args: &[Rc<BodyForm>],
    callsite: Srcloc,
    expr: Rc<BodyForm>,
) -> Result<Rc<BodyForm>, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(_, _) => Err(CompileErr(
            loc,
            "let binding should have been hoisted before optimization".to_string(),
        )),
        BodyForm::Call(l, call_args) => {
            let mut new_args = Vec::new();
            // Ensure that we don't count branched invocations when checking
            // each call downstream of the main expr is recursive.
            //
            // Previously, this program detected as recursive:
            // (mod (A) ;; 11
            //   (include *standard-cl-22*)
            //   (defun-inline <= (A B) (not (> A B)))
            //   (assign
            //     foo (<= 2 A)
            //     bar (<= 1 A)
            //
            //     baz (<= foo bar)
            //
            //     yorgle (<= baz bar)
            //
            //     (<= yorgle foo)
            //     ))
            //
            // <= appears in the arguments, but isn't called recursively on itself.
            // We ensure here that each argument has a separate visited stack.
            // Recursion only happens when the same stack encounters an inline
            // twice.
            for (i, arg) in call_args.iter().enumerate() {
                if i == 0 {
                    new_args.push(arg.clone());
                } else {
                    let mut new_visited = visited_inlines.clone();
                    let replaced = replace_inline_body(
                        &mut new_visited,
                        runner.clone(),
                        opts.clone(),
                        compiler,
                        arg.loc(),
                        inline,
                        args,
                        callsite.clone(),
                        arg.clone(),
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
                Callable::CallInline(l, new_inline) => {
                    if visited_inlines.contains(&new_inline.name) {
                        return Err(CompileErr(
                            l,
                            format!(
                                "recursive call to inline function {}",
                                decode_string(&inline.name)
                            ),
                        ));
                    }

                    visited_inlines.insert(new_inline.name.clone());

                    let pass_on_args: Vec<Rc<BodyForm>> =
                        new_args.iter().skip(1).cloned().collect();
                    replace_inline_body(
                        visited_inlines,
                        runner,
                        opts.clone(),
                        compiler,
                        l, // clippy update since 1.59
                        &new_inline,
                        &pass_on_args,
                        callsite,
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
            let alookup = arg_lookup(callsite, inline.args.clone(), 0, args, a.clone())?
                .unwrap_or_else(|| expr.clone());
            Ok(alookup)
        }
        BodyForm::Lambda(ldata) => {
            let rewritten_captures = replace_inline_body(
                visited_inlines,
                runner,
                opts,
                compiler,
                loc,
                inline,
                args,
                callsite,
                ldata.captures.clone(),
            )?;
            Ok(Rc::new(BodyForm::Lambda(LambdaData {
                captures: rewritten_captures,
                ..ldata.clone()
            })))
        }
        _ => Ok(expr.clone()),
    }
}

/// Given an inline function and a list of arguments, return compiled code that
/// stands in for the inline expansion.  Along the way, generate code for the
/// expressions in the argument list.
///
/// This will probably be changed at some point to return Rc<BodyForm> so it
/// can be treated as a desugaring step that's subject to frontend optimization.
#[allow(clippy::too_many_arguments)]
pub fn replace_in_inline(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    inline: &InlineFunction,
    callsite: Srcloc,
    args: &[Rc<BodyForm>],
) -> Result<CompiledCode, CompileErr> {
    let mut visited = HashSet::new();
    visited.insert(inline.name.clone());
    replace_inline_body(
        &mut visited,
        runner.clone(),
        opts.clone(),
        compiler,
        loc,
        inline,
        args,
        callsite,
        inline.body.clone(),
    )
    .and_then(|x| generate_expr_code(allocator, runner, opts, compiler, x))
}
