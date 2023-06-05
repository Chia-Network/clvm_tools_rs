use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen};
use crate::compiler::optimize::{CodegenOptimizationResult, CompileContextWrapper, deinline_opt, fe_opt, Optimization, optimize_expr, null_optimization, run_optimizer};
use crate::compiler::sexp::SExp;

/// A basic implementation of Optimization that never transforms anything.
#[derive(Default, Clone)]
pub struct ExistingStrategy {}

impl ExistingStrategy {
    pub fn new() -> Self {
        ExistingStrategy {}
    }
}

impl Optimization for ExistingStrategy {
    fn frontend_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        p0: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        // Not yet turned on for >22
        if opts.frontend_opt() && !(opts.dialect().stepping.map(|d| d > 22).unwrap_or(false)) {
            // Front end optimization
            fe_opt(allocator, runner, opts.clone(), p0)
        } else {
            Ok(p0)
        }
    }

    fn post_desugar_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        if opts.frontend_opt() && opts.dialect().stepping.map(|s| s > 22).unwrap_or(false) {
            let mut symbols = HashMap::new();
            let mut wrapper =
                CompileContextWrapper::new(allocator, runner, &mut symbols, self.duplicate());
            deinline_opt(&mut wrapper.context, opts.clone(), cf)
        } else {
            Ok(cf)
        }
    }

    fn start_of_codegen_optimization(
        &mut self,
        code_generator: PrimaryCodegen,
    ) -> Result<PrimaryCodegen, CompileErr> {
        Ok(code_generator)
    }

    fn function_codegen_optimization(
        &mut self,
        _code_generator: &PrimaryCodegen,
        _hf: Option<HelperForm>,
        _repr: Rc<SExp>,
    ) -> Result<CodegenOptimizationResult, CompileErr> {
        Ok(Default::default())
    }

    fn macro_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        if opts.optimize() {
            run_optimizer(allocator, runner, code)
        } else {
            Ok(code)
        }
    }

    fn defun_body_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
        defun: &DefunData,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let res = if opts.optimize() {
            // Run optimizer on frontend style forms.
            optimize_expr(
                allocator,
                opts.clone(),
                runner.clone(),
                codegen,
                defun.body.clone(),
            )
            .map(|x| x.1)
            .unwrap_or_else(|| defun.body.clone())
        } else {
            defun.body.clone()
        };
        Ok(res)
    }

    fn post_codegen_function_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        if opts.optimize() {
            run_optimizer(allocator, runner, code)
        } else {
            Ok(code)
        }
    }

    fn pre_final_codegen_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        let res = if opts.optimize() {
            optimize_expr(
                allocator,
                opts.clone(),
                runner,
                codegen,
                codegen.final_expr.clone(),
            )
            .map(|x| x.1)
            .unwrap_or_else(|| codegen.final_expr.clone())
        } else {
            codegen.final_expr.clone()
        };

        Ok(res)
    }

    fn post_codegen_output_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        generated: SExp,
    ) -> Result<SExp, CompileErr> {
        if opts.frontend_opt() && opts.dialect().stepping.map(|s| s > 22).unwrap_or(false) {
            let (did_work, optimized) = null_optimization(Rc::new(generated.clone()), false);
            if did_work {
                let o_borrowed: &SExp = optimized.borrow();
                return Ok(o_borrowed.clone());
            }
        }

        Ok(generated)
    }

    fn duplicate(&self) -> Box<dyn Optimization> {
        Box::new(self.clone())
    }
}
