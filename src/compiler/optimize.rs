use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_zero;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::run;
use crate::compiler::codegen::get_callable;
use crate::compiler::comptypes::{BodyForm, Callable, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen};
#[cfg(test)]
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::compiler::{is_cons, is_operator};
use crate::compiler::evaluate::{build_reflex_captures, Evaluator};
#[cfg(test)]
use crate::compiler::frontend::compile_bodyform;
#[cfg(test)]
use crate::compiler::sexp::parse_sexp;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::u8_from_number;


fn is_at_form(head: Rc<BodyForm>) -> bool {
    match head.borrow() {
        BodyForm::Value(SExp::Atom(_, a)) => a.len() == 1 && a[0] == b'@',
        _ => false,
    }
}

// Return a score for sexp size.
pub fn sexp_scale(sexp: &SExp) -> u64 {
    match sexp {
        SExp::Cons(_,a,b) => {
            let a_scale = sexp_scale(a.borrow());
            let b_scale = sexp_scale(b.borrow());
            1_u64 + a_scale + b_scale
        }
        SExp::Nil(_) => 1,
        SExp::QuotedString(_,_,s) => {
            1_u64 + s.len() as u64
        }
        SExp::Atom(_,n) => {
            1_u64 + n.len() as u64
        }
        SExp::Integer(_,i) => {
            let raw_bits = i.bits();
            let use_bits = if raw_bits > 0 { raw_bits - 1 } else { 0 };
            let bytes = use_bits / 8;
            1_u64 + bytes
        }
    }
}

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

// Unroll loops
//
// A function in this form:
//
// (defun name (A1 A2 ... L ... An)
//   (if L ;; (or (l L)
//     (c (STUFF ... (f L) ...) (name A1 A2 ... (r L) ... An)) ;; STUFF cannot use (r L)
//     L ;; (or ())
//     )
//   )
//
// Can unroll into:
//
//
//  (defun unroll_$_name (A1 A2 ... H ... An) ;; H = (f L)
//     (STUFF ... H ...)
//     )
//
//  (defun name (A1 A2 ... L ... An)
//     (if L ;; (or (l L))
//       (c (unroll_$_name A1 A2 ... (f L) ... An)
//          (name A1 A2 .. (r L) ... An)
//          )
//       L ;; (or ())
//       )
//     )
//
//   (c (unroll_$_name A1 A2 ... (a 5 L) ... An)
//     (c (unroll_$_name A1 A2 ... (a 11 L) ... An)
//        ()))
//
// When L is formed as:
//
//    (c X (c Y (c Z ())))
//
// And
//
//   (c (unroll_$_name A1 A2 ... (a 5 L) ... An)
//     (c (unroll_$_name A1 A2 ... (a 11 L) ... An)
//        (name A1 A2 ... QQQ ... An)))
//
// When L is formed as:
//
//    (c X (c Y (c Z QQQ)))

struct UnrollableList {
    // Any entries that could be recovered.
    entries: Vec<Rc<BodyForm>>,
    tail: Rc<BodyForm>
}

fn is_cons_bf(bf: Rc<BodyForm>) -> bool {
    if let BodyForm::Value(a) = bf.borrow() {
        return is_cons(&a) || is_operator(b'c' as u32, &a);
    }

    false
}

fn recognize_unrollable_list_inner(
    body: Rc<BodyForm>
) -> Result<Option<UnrollableList>, CompileErr> {
    match body.borrow() {
        BodyForm::Call(_, exprs) => {
            if exprs.is_empty() {
                return Ok(None);
            }

            if is_cons_bf(exprs[0].clone()) && exprs.len() == 3 {
                if let Some(mut tail) = recognize_unrollable_list_inner(exprs[2].clone())? {
                    tail.entries.insert(0, exprs[1].clone());
                    return Ok(Some(tail));
                } else {
                    return Ok(None);
                }
            }
        }
        BodyForm::Quoted(SExp::Cons(_,f,r)) => {
            let borrowed_tail: &SExp = r.borrow();
            if let Some(mut tail) = recognize_unrollable_list_inner(Rc::new(BodyForm::Quoted(borrowed_tail.clone())))? {
                let borrowed_head: &SExp = f.borrow();
                tail.entries.insert(0, Rc::new(BodyForm::Quoted(borrowed_head.clone())));
                return Ok(Some(tail));
            }
        }
        BodyForm::Quoted(SExp::Nil(_)) => {
            return Ok(Some(UnrollableList {
                entries: Default::default(),
                tail: body.clone()
            }));
        }
        _ => {}
    }

    Ok(None)
}

// Recognize a list formation in code.
fn recognize_unrollable_list(
    body: Rc<BodyForm>
) -> Result<Option<UnrollableList>, CompileErr> {
    if let Some(res) = recognize_unrollable_list_inner(body)? {
        if res.entries.is_empty() {
            Ok(None)
        } else {
            Ok(Some(res))
        }
    } else {
        Ok(None)
    }
}

#[test]
fn test_recognize_unrollable_basic() {
    let opts = Rc::new(DefaultCompilerOpts::new("*test*"));
    let parsed = parse_sexp(Srcloc::start("*test*"), "(c 101 (c 102 (c 103 (q 2 3))))".bytes()).expect("should parse");
    let compiled = compile_bodyform(opts, parsed[0].clone()).expect("should compile");
    let recognized_unrollable = recognize_unrollable_list(
        Rc::new(compiled)
    ).expect("should be able to determine unrollableness");
    if let Some(unrollable) = recognized_unrollable {
        assert_eq!(unrollable.entries.len(), 5);
        assert!(matches!(unrollable.tail.borrow(), BodyForm::Quoted(SExp::Nil(_))));
    } else {
        assert!(false);
    }
}

// If (1) appears anywhere outside of a quoted expression, it can be replaced with
// () since nil yields itself.
fn null_optimization(sexp: Rc<SExp>, spine: bool) -> (bool, Rc<SExp>) {
    if let SExp::Cons(l,a,b) = sexp.borrow() {
        if let SExp::Atom(_,name) = a.atomize() {
            if (name == vec![1] || name == b"q") && !spine {
                let b_empty =
                    match b.borrow() {
                        SExp::Atom(_,tail) => tail.is_empty(),
                        SExp::QuotedString(_,_,q) => q.is_empty(),
                        SExp::Integer(_,i) => *i == bi_zero(),
                        SExp::Nil(_) => true,
                        _ => false
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

    (false, sexp.clone())
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

fn compile_to_sexp(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compileform: &CompileForm
) -> Result<SExp, CompileErr> {
    let new_program = Rc::new(SExp::Cons(
        compileform.loc.clone(),
        Rc::new(SExp::Atom(compileform.loc.clone(), "mod".as_bytes().to_vec())),
        compileform.to_sexp()
    ));

    let code = opts.compile_program(
        allocator,
        runner.clone(),
        new_program,
        &mut HashMap::new()
    )?;

    Ok(code)
}

fn try_deinline(
    helper: &mut HelperForm
) -> Option<HelperForm> {
    if let Some((currently_inline, current_data)) =
        match helper {
            HelperForm::Defun(inline, data) => {
                Some((inline, data.clone()))
            }
            _ => None
        } {
            if *currently_inline {
                let result = helper.clone();
                *helper = HelperForm::Defun(false, current_data);
                return Some(result);
            }
        };

    None
}

fn try_shrink_with_deinline(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    mut compileform: CompileForm
) -> Result<CompileForm, CompileErr> {
    let no_opt_options = opts.set_frontend_opt(false);
    let baseline_compile = compile_to_sexp(
        allocator,
        runner.clone(),
        no_opt_options.clone(),
        &compileform
    )?;
    let mut current_size = sexp_scale(baseline_compile.borrow());
    let first_size = current_size;
    let mut shrunk = true;

    while shrunk {
        shrunk = false;
        for i in 0..compileform.helpers.len() {
            if let Some(orig) = try_deinline(&mut compileform.helpers[i]) {
                if let Ok(compiled) = compile_to_sexp(
                    allocator,
                    runner.clone(),
                    no_opt_options.clone(),
                    &compileform
                ) {
                    let new_size = sexp_scale(compiled.borrow());
                    if new_size < current_size {
                        shrunk = true;
                        current_size = new_size;
                        continue;
                    } else {
                        compileform.helpers[i] = orig;
                    }
                } else {
                    compileform.helpers[i] = orig;
                }
            }
        }
    }
    Ok(compileform)
}

pub fn fe_opt(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    orig_compileform: CompileForm,
) -> Result<CompileForm, CompileErr> {
    // Test binary size exchanging inlines for non-inlines.
    let compileform = try_shrink_with_deinline(
        allocator,
        runner.clone(),
        opts.clone(),
        orig_compileform
    )?;

    let mut compiler_helpers = compileform.helpers.clone();
    let mut used_names = HashSet::new();

    if !opts.in_defun() {
        for c in compileform.helpers.iter() {
            used_names.insert(c.name().clone());
        }

        for helper in (opts
            .compiler()
            .map(|c| c.orig_help)
            .unwrap_or_else(Vec::new))
        .iter()
        {
            if !used_names.contains(helper.name()) {
                compiler_helpers.push(helper.clone());
            }
        }
    }

    let evaluator = Evaluator::new(opts.clone(), runner.clone(), compiler_helpers.clone());
    let mut optimized_helpers: Vec<HelperForm> = Vec::new();
    for h in compiler_helpers.iter() {
        match &h {
            HelperForm::Defun(inline, defun) => {
                let mut env = HashMap::new();
                build_reflex_captures(&mut env, defun.args.clone());
                let body_rc = evaluator.shrink_bodyform(
                    allocator,
                    defun.args.clone(),
                    &env,
                    defun.body.clone(),
                    true,
                )?;
                let new_helper = HelperForm::Defun(
                    *inline,
                    DefunData {
                        loc: defun.loc.clone(),
                        nl: defun.nl.clone(),
                        kw: defun.kw.clone(),
                        name: defun.name.clone(),
                        args: defun.args.clone(),
                        body: body_rc.clone(),
                        synthetic: defun.synthetic
                    },
                );
                optimized_helpers.push(new_helper);
            }
            _ => {
                optimized_helpers.push(h.clone());
            }
        }
    }

    let new_evaluator = Evaluator::new(opts.clone(), runner.clone(), optimized_helpers.clone());

    let mut env = HashMap::new();
    build_reflex_captures(&mut env, compileform.args.clone());

    let shrunk = new_evaluator.shrink_bodyform(
        allocator,
        compileform.args.clone(),
        &env,
        compileform.exp.clone(),
        true,
    )?;

    Ok(CompileForm {
        loc: compileform.loc.clone(),
        include_forms: compileform.include_forms.clone(),
        args: compileform.args,
        helpers: optimized_helpers.clone(),
        exp: shrunk,
    })
}
