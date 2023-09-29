pub mod strategy;

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
use crate::classic::clvm_tools::stages::stage_2::optimize::optimize_sexp;

use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs, run};
use crate::compiler::codegen::{codegen, get_callable};
use crate::compiler::comptypes::{
    BodyForm, CallSpec, Callable, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm,
    PrimaryCodegen, SyntheticType,
};
use crate::compiler::evaluate::{build_reflex_captures, Evaluator, EVAL_STACK_LIMIT};
use crate::compiler::optimize::strategy::ExistingStrategy;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
#[cfg(test)]
use crate::compiler::sexp::{enlist, parse_sexp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::BasicCompileContext;
use crate::compiler::CompileContextWrapper;
use crate::compiler::StartOfCodegenOptimization;
use crate::util::u8_from_number;

const CONST_FOLD_LIMIT: usize = 10000000;

/// Represents a code generator level optimization result.
/// If revised_definition is different from the one we already have, the compiler
/// must re-generate at least functions that depend on this one.
#[derive(Default, Debug, Clone)]
pub struct CodegenOptimizationResult {
    /// Revised code generator object, if given.
    pub revised_code_generator: Option<PrimaryCodegen>,
    /// If present, the definition of the helperform, if provided, was changed.
    pub revised_definition: Option<HelperForm>,
    /// If present, each key represents the shatree of an environment part that
    /// was rewriten along with its new definition.
    pub revised_environment: Option<HashMap<Vec<u8>, Rc<SExp>>>,
    /// Final generated code if different.
    pub code: Option<Rc<SExp>>,
}

/// Make a formal interface that represents all kinds of optimization we can do.
/// This includes these possible things:
///
/// - Frontend:
///   - Simplification
///   - Constant folding
///   - Inlining and deinlining
///   - SSA optimizations
///     - Deduplication
///     - Constant term propogation
///     - ... etc
///   - Argument list changes which simplify code
///   - Capture removal
///   - Pattern based inlining in loops
///
/// - Start of codegen
///   - Environment layout optimization
///   - Dead code/constant elimination
///   - Leaf function optimization
///   - Leaf main optimization
///
/// - During codegen
///   - Function level code optimizations
///   - Constant compression
///   - Nil and quote simplification
///   - Constant folding
///   - Path folding for (r and (f and composed paths
///   - Cons simplification
///   - Apply elision
///
/// Global optimization must be performed when the code generator is requesting
/// optimizations on the main expression, therefore there is no post-code generator
/// optimization in this scheme.
///
pub trait Optimization {
    /// Represents frontend optimizations
    fn frontend_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr>;

    /// Represents optimization we should do after desugaring, such as deinlining
    fn post_desugar_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr>;

    /// Represents start of codegen optimizations
    /// PrimaryCodegen has computed the environment it wants to use but hasn't
    /// generated any code that depends on it yet.
    fn start_of_codegen_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        to_optimize: StartOfCodegenOptimization,
    ) -> Result<StartOfCodegenOptimization, CompileErr>;

    /// Optimize macro bodies.
    fn macro_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr>;

    fn defun_body_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
        defun: &DefunData,
    ) -> Result<Rc<BodyForm>, CompileErr>;

    fn post_codegen_function_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        helper: Option<&HelperForm>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr>;

    fn pre_final_codegen_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
    ) -> Result<Rc<BodyForm>, CompileErr>;

    fn post_codegen_output_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        generated: SExp,
    ) -> Result<SExp, CompileErr>;

    fn duplicate(&self) -> Box<dyn Optimization>;
}

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

#[test]
fn test_sexp_scale_increases_with_list_of_atoms() {
    let l = Srcloc::start("*test*");
    let one_atom = Rc::new(SExp::Integer(l.clone(), bi_one()));
    let target_scale = 4 + 3 * sexp_scale(one_atom.borrow());
    let list_of_atom = enlist(
        l.clone(),
        &[one_atom.clone(), one_atom.clone(), one_atom.clone()],
    );
    assert_eq!(target_scale, sexp_scale(&list_of_atom));
}

/// Changes (i (not c) a b) into (i c b a)
fn condition_invert_optimize(
    opts: Rc<dyn CompilerOpts>,
    _loc: &Srcloc,
    _forms: &[Rc<BodyForm>],
) -> Option<BodyForm> {
    if let Some(res) = opts.dialect().stepping {
        // Only perform on chialisp above stepping 23.
        if res < 23 {
            return None;
        }
    }

    None
}

/// If a function is called with all constant arguments, we compose the program
/// that runs that function and run it.
///
/// The result is the constant result of invoking the function.
fn constant_fun_result(
    _allocator: &mut Allocator,
    opts: Rc<dyn CompilerOpts>,
    _runner: Rc<dyn TRunProgram>,
    _compiler: &PrimaryCodegen,
    _call_spec: &CallSpec,
) -> Option<Rc<BodyForm>> {
    if let Some(res) = opts.dialect().stepping {
        if res < 23 {
            return None;
        }
    }

    None
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
        BodyForm::Call(l, forms, tail) => {
            // () evaluates to ()
            if forms.is_empty() {
                return Some((true, body));
            } else if is_at_form(forms[0].clone()) {
                return None;
            }

            let examine_call = |al: Srcloc, an: &Vec<u8>| {
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
                    Callable::CallDefun(l, _target) => {
                        if let Some(constant_invocation) = constant_fun_result(
                            allocator,
                            opts.clone(),
                            runner.clone(),
                            compiler,
                            &CallSpec {
                                loc: l,
                                name: an,
                                args: forms,
                                tail: tail.clone(),
                                original: body.clone(),
                            },
                        ) {
                            return Some(
                                optimize_expr(
                                    allocator,
                                    opts.clone(),
                                    runner,
                                    compiler,
                                    constant_invocation.clone(),
                                )
                                .map(|(_, optimize)| (true, optimize))
                                .unwrap_or_else(|| (true, constant_invocation)),
                            );
                        }

                        None
                    }
                    // A primcall is constant if its arguments are constant
                    Callable::CallPrim(l, _) => {
                        let mut constant = true;

                        if let Some(not_invert) = condition_invert_optimize(opts.clone(), &l, forms)
                        {
                            return Some(
                                optimize_expr(
                                    allocator,
                                    opts.clone(),
                                    runner.clone(),
                                    compiler,
                                    Rc::new(not_invert.clone()),
                                )
                                .map(|(_, optimize)| (true, optimize))
                                .unwrap_or_else(|| (true, Rc::new(not_invert))),
                            );
                        }

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
                        // Primitive call: no tail.
                        let code = BodyForm::Call(l.clone(), result_list, None);

                        if constant {
                            run(
                                allocator,
                                runner.clone(),
                                opts.prim_map(),
                                code.to_sexp(),
                                Rc::new(SExp::Nil(l)),
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
        BodyForm::Mod(_l, _cf) => {
            if let Some(stepping) = opts.dialect().stepping {
                if stepping < 23 {
                    return None;
                }
            }

            None
        }
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

// Should take a desugared program.
pub fn deinline_opt(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    mut compileform: CompileForm,
) -> Result<CompileForm, CompileErr> {
    let mut best_compileform = compileform.clone();
    let generated_program = codegen(context, opts.clone(), &best_compileform)?;
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

            let maybe_smaller_program = codegen(context, opts.clone(), &compileform)?;
            let new_metric = sexp_scale(&maybe_smaller_program);

            // Don't keep this change if it made things worse.
            if new_metric >= metric {
                compileform.helpers[i] = old_helper;
            } else {
                metric = new_metric;
                best_compileform = compileform.clone();
            }
        }

        if start_metric == metric {
            break;
        }
    }

    Ok(best_compileform)
}

fn fe_opt(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compileform: CompileForm,
) -> Result<CompileForm, CompileErr> {
    let evaluator = Evaluator::new(opts.clone(), runner.clone(), compileform.helpers.clone());
    let mut optimized_helpers: Vec<HelperForm> = Vec::new();
    for h in compileform.helpers.iter() {
        match h {
            HelperForm::Defun(inline, defun) => {
                let mut env = HashMap::new();
                build_reflex_captures(&mut env, defun.args.clone());
                let body_rc = evaluator.shrink_bodyform(
                    allocator,
                    defun.args.clone(),
                    &env,
                    defun.body.clone(),
                    true,
                    Some(EVAL_STACK_LIMIT),
                )?;
                let new_helper = HelperForm::Defun(
                    *inline,
                    Box::new(DefunData {
                        loc: defun.loc.clone(),
                        nl: defun.nl.clone(),
                        kw: defun.kw.clone(),
                        name: defun.name.clone(),
                        args: defun.args.clone(),
                        orig_args: defun.orig_args.clone(),
                        synthetic: defun.synthetic.clone(),
                        body: body_rc.clone(),
                    }),
                );
                optimized_helpers.push(new_helper);
            }
            obj => {
                optimized_helpers.push(obj.clone());
            }
        }
    }
    let new_evaluator = Evaluator::new(opts.clone(), runner.clone(), optimized_helpers.clone());

    let shrunk = new_evaluator.shrink_bodyform(
        allocator,
        Rc::new(SExp::Nil(compileform.args.loc())),
        &HashMap::new(),
        compileform.exp.clone(),
        true,
        Some(EVAL_STACK_LIMIT),
    )?;

    Ok(CompileForm {
        helpers: optimized_helpers.clone(),
        exp: shrunk,
        ..compileform
    })
}

fn run_optimizer(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    r: Rc<SExp>,
) -> Result<Rc<SExp>, CompileErr> {
    let to_clvm_rs = convert_to_clvm_rs(allocator, r.clone())
        .map(|x| (r.loc(), x))
        .map_err(|e| match e {
            RunFailure::RunErr(l, e) => CompileErr(l, e),
            RunFailure::RunExn(s, e) => CompileErr(s, format!("exception {e}\n")),
        })?;

    let optimized = optimize_sexp(allocator, to_clvm_rs.1, runner)
        .map_err(|e| CompileErr(to_clvm_rs.0.clone(), e.1))
        .map(|x| (to_clvm_rs.0, x))?;

    convert_from_clvm_rs(allocator, optimized.0, optimized.1).map_err(|e| match e {
        RunFailure::RunErr(l, e) => CompileErr(l, e),
        RunFailure::RunExn(s, e) => CompileErr(s, format!("exception {e}\n")),
    })
}

/// Produce the optimization strategy specified by the compiler opts we're given.
pub fn get_optimizer(
    loc: &Srcloc,
    opts: Rc<dyn CompilerOpts>,
) -> Result<Box<dyn Optimization>, CompileErr> {
    if let Some(s) = opts.dialect().stepping {
        if s < 21 {
            return Err(CompileErr(
                loc.clone(),
                format!("minimum language stepping is 21, {s} specified"),
            ));
        } else if s > 22 {
            return Err(CompileErr(
                loc.clone(),
                format!("maximum language stepping is 22 at this time, {s} specified"),
            ));
        }
    }

    Ok(Box::new(ExistingStrategy::new()))
}

/// This small interface takes care of various scenarios that have existed
/// regarding mixing modern chialisp output with classic's optimizer.
pub fn maybe_finalize_program_via_classic_optimizer(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    _opts: Rc<dyn CompilerOpts>, // Currently unused but I want this interface
    // to consider opts in the future when required.
    opt_flag: bool, // Command line flag and other features control this in oldest
    // versions
    unopt_res: &SExp,
) -> Result<Rc<SExp>, CompileErr> {
    if opt_flag {
        run_optimizer(allocator, runner, Rc::new(unopt_res.clone()))
    } else {
        Ok(Rc::new(unopt_res.clone()))
    }
}
