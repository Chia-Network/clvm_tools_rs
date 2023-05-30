#[cfg(test)]
use num_bigint::ToBigInt;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

#[cfg(test)]
use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm::__type_compatibility__::bi_zero;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::run;
use crate::compiler::codegen::{codegen, get_callable};
use crate::compiler::comptypes::{
    BodyForm, Callable, CompileErr, CompileForm, CompilerOpts, HelperForm, PrimaryCodegen,
    SyntheticType,
};
#[cfg(test)]
use crate::compiler::sexp::parse_sexp;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::u8_from_number;

const CONST_FOLD_LIMIT: usize = 10000000;

fn is_at_form(head: Rc<BodyForm>) -> bool {
    match head.borrow() {
        BodyForm::Value(SExp::Atom(_, a)) => a.len() == 1 && a[0] == b'@',
        _ => false,
    }
}

// Return a score for sexp size.
pub fn sexp_scale(sexp: &SExp) -> u64 {
    match sexp {
        SExp::Cons(_, a, b) => {
            let a_scale = sexp_scale(a.borrow());
            let b_scale = sexp_scale(b.borrow());
            1_u64 + a_scale + b_scale
        }
        SExp::Nil(_) => 1,
        SExp::QuotedString(_, _, s) => 1_u64 + s.len() as u64,
        SExp::Atom(_, n) => 1_u64 + n.len() as u64,
        SExp::Integer(_, i) => {
            let raw_bits = i.bits();
            let use_bits = if raw_bits > 0 { raw_bits - 1 } else { 0 };
            let bytes = use_bits / 8;
            1_u64 + bytes
        }
    }
}

#[test]
fn test_sexp_scale_increases_with_atom_size() {
    let l = Srcloc::start("*test*");
    assert!(
        sexp_scale(&SExp::Integer(l.clone(), bi_one()))
            < sexp_scale(&SExp::Integer(l, 1000000_u32.to_bigint().unwrap()))
    );
}

/// At this point, very rudimentary constant folding on body expressions.
pub fn optimize_expr(
    allocator: &mut Allocator,
    opts: Rc<dyn CompilerOpts>,
    runner: Rc<dyn TRunProgram>,
    compiler: &PrimaryCodegen,
    body: Rc<BodyForm>,
) -> Option<(bool, Rc<BodyForm>)> {
    match body.borrow() {
        BodyForm::Quoted(_) => Some((true, body)),
        BodyForm::Call(l, forms) => {
            // () evaluates to ()
            if forms.is_empty() {
                return Some((true, body));
            } else if is_at_form(forms[0].clone()) {
                return None;
            }

            let mut examine_call = |al: Srcloc, an: &Vec<u8>| {
                get_callable(
                    opts.clone(),
                    compiler,
                    l.clone(),
                    Rc::new(SExp::Atom(al, an.to_vec())),
                )
                .map(|calltype| match calltype {
                    // A macro invocation emits a bodyform, which we
                    // run back through the frontend and check.
                    Callable::CallMacro(_l, _) => None,
                    // A function is constant if its body is a constant
                    // expression or all its arguments are constant and
                    // its body doesn't include an environment reference.
                    Callable::CallDefun(_l, _target) => None,
                    // A primcall is constant if its arguments are constant
                    Callable::CallPrim(l, _) => {
                        let mut constant = true;
                        let optimized_args: Vec<(bool, Rc<BodyForm>)> = forms
                            .iter()
                            .skip(1)
                            .map(|a| {
                                let optimized = optimize_expr(
                                    allocator,
                                    opts.clone(),
                                    runner.clone(),
                                    compiler,
                                    a.clone(),
                                );
                                constant = constant
                                    && optimized.as_ref().map(|x| x.0).unwrap_or_else(|| false);
                                optimized
                                    .map(|x| (x.0, x.1))
                                    .unwrap_or_else(|| (false, a.clone()))
                            })
                            .collect();

                        let mut result_list = vec![forms[0].clone()];
                        let mut replaced_args =
                            optimized_args.iter().map(|x| x.1.clone()).collect();
                        result_list.append(&mut replaced_args);
                        let code = BodyForm::Call(l.clone(), result_list);

                        if constant {
                            run(
                                allocator,
                                runner.clone(),
                                opts.prim_map(),
                                code.to_sexp(),
                                Rc::new(SExp::Nil(l)),
                                None,
                                Some(CONST_FOLD_LIMIT),
                            )
                            .map(|x| {
                                let x_borrow: &SExp = x.borrow();
                                Some((true, Rc::new(BodyForm::Quoted(x_borrow.clone()))))
                            })
                            .unwrap_or_else(|_| Some((false, Rc::new(code))))
                        } else {
                            Some((false, Rc::new(code)))
                        }
                    }
                    _ => None,
                })
                .unwrap_or_else(|_| None)
            };

            match forms[0].borrow() {
                BodyForm::Value(SExp::Integer(al, an)) => {
                    examine_call(al.clone(), &u8_from_number(an.clone()))
                }
                BodyForm::Value(SExp::QuotedString(al, _, an)) => examine_call(al.clone(), an),
                BodyForm::Value(SExp::Atom(al, an)) => examine_call(al.clone(), an),
                _ => None,
            }
        }
        BodyForm::Value(SExp::Integer(l, i)) => Some((
            true,
            Rc::new(BodyForm::Quoted(SExp::Integer(l.clone(), i.clone()))),
        )),
        _ => None,
    }
}

// If (1) appears anywhere outside of a quoted expression, it can be replaced with
// () since nil yields itself.
fn null_optimization(sexp: Rc<SExp>, spine: bool) -> (bool, Rc<SExp>) {
    if let SExp::Cons(l, a, b) = sexp.borrow() {
        if let SExp::Atom(_, name) = a.atomize() {
            if (name == vec![1] || name == b"q") && !spine {
                let b_empty = match b.borrow() {
                    SExp::Atom(_, tail) => tail.is_empty(),
                    SExp::QuotedString(_, _, q) => q.is_empty(),
                    SExp::Integer(_, i) => *i == bi_zero(),
                    SExp::Nil(_) => true,
                    _ => false,
                };

                if b_empty {
                    return (true, b.clone());
                } else {
                    return (false, sexp);
                }
            }
        }

        let (oa, opt_a) = null_optimization(a.clone(), false);
        let (ob, opt_b) = null_optimization(b.clone(), true);

        if oa || ob {
            return (true, Rc::new(SExp::Cons(l.clone(), opt_a, opt_b)));
        }
    }

    (false, sexp)
}

#[test]
fn test_null_optimization_basic() {
    let loc = Srcloc::start("*test*");
    let parsed = parse_sexp(loc.clone(), "(2 (1 1) (4 (1) 1))".bytes()).expect("should parse");
    let (did_work, optimized) = null_optimization(parsed[0].clone(), true);
    assert!(did_work);
    assert_eq!(optimized.to_string(), "(2 (1 1) (4 () 1))");
}

#[test]
fn test_null_optimization_skips_quoted() {
    let loc = Srcloc::start("*test*");
    let parsed = parse_sexp(loc.clone(), "(2 (1 (1) (1) (1)) (1))".bytes()).expect("should parse");
    let (did_work, optimized) = null_optimization(parsed[0].clone(), true);
    assert!(did_work);
    assert_eq!(optimized.to_string(), "(2 (1 (1) (1) (1)) ())");
}

#[test]
fn test_null_optimization_ok_not_doing_anything() {
    let loc = Srcloc::start("*test*");
    let parsed = parse_sexp(loc.clone(), "(2 (1 (1) (1) (1)) (3))".bytes()).expect("should parse");
    let (did_work, optimized) = null_optimization(parsed[0].clone(), true);
    assert!(!did_work);
    assert_eq!(optimized.to_string(), "(2 (1 (1) (1) (1)) (3))");
}

// Do final optimizations on the finished CLVM code.
// These should be lightweight transformations that save space.
pub fn finish_optimization(sexp: &SExp) -> SExp {
    let (did_work, optimized) = null_optimization(Rc::new(sexp.clone()), false);
    if did_work {
        let o_borrowed: &SExp = optimized.borrow();
        o_borrowed.clone()
    } else {
        sexp.clone()
    }
}

// Should take a desugared program.
pub fn deinline_opt(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    mut compileform: CompileForm,
    symbol_table: &mut HashMap<String, String>,
) -> Result<SExp, CompileErr> {
    let mut generated_program = codegen(
        allocator,
        runner.clone(),
        opts.clone(),
        &compileform,
        symbol_table,
    )?;
    let mut metric = sexp_scale(&generated_program);
    let flip_helper = |h: &mut HelperForm| {
        if let HelperForm::Defun(inline, defun) = h {
            if matches!(&defun.synthetic, Some(SyntheticType::NoInlinePreference)) {
                *h = HelperForm::Defun(!*inline, defun.clone());
                return true;
            }
        }

        false
    };

    loop {
        let start_metric = metric;

        for i in 0..compileform.helpers.len() {
            // Try flipped.
            let old_helper = compileform.helpers[i].clone();
            if !flip_helper(&mut compileform.helpers[i]) {
                continue;
            }

            let maybe_smaller_program = codegen(
                allocator,
                runner.clone(),
                opts.clone(),
                &compileform,
                symbol_table,
            )?;
            let new_metric = sexp_scale(&maybe_smaller_program);

            // Don't keep this change if it made things worse.
            if new_metric >= metric {
                compileform.helpers[i] = old_helper;
            } else {
                metric = new_metric;
                generated_program = maybe_smaller_program;
            }
        }

        if start_metric == metric {
            break;
        }
    }

    Ok(generated_program)
}
