use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen,
};
use crate::compiler::optimize::{
    deinline_opt, null_optimization, optimize_expr, run_optimizer, CodegenOptimizationResult,
    CompileContextWrapper, Optimization,
};
use crate::compiler::sexp::SExp;

/// Captures the strategy for cl23 and above.
/// Until formally released, we can take action in here.
#[derive(Default, Clone)]
pub struct Strategy23 {}

impl Strategy23 {
    pub fn new() -> Self {
        Strategy23 {}
    }
}

impl Optimization for Strategy23 {
    fn frontend_optimization(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        p0: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        // Not yet turned on for >22
        Ok(p0)
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
        repr: Rc<SExp>,
    ) -> Result<CodegenOptimizationResult, CompileErr> {
        let (worked, result) = null_optimization(repr, true);
        if worked {
            return Ok(CodegenOptimizationResult {
                code: Some(result),
                ..Default::default()
            });
        }

        Ok(Default::default())
    }

    fn macro_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        run_optimizer(allocator, runner, code)
    }

    fn defun_body_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
        defun: &DefunData,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        // Run optimizer on frontend style forms.
        Ok(optimize_expr(
            allocator,
            opts.clone(),
            runner.clone(),
            codegen,
            defun.body.clone(),
        )
        .map(|x| x.1)
        .unwrap_or_else(|| defun.body.clone()))
    }

    fn post_codegen_function_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        run_optimizer(allocator, runner, code)
    }

    fn pre_final_codegen_optimize(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        Ok(optimize_expr(
            allocator,
            opts.clone(),
            runner,
            codegen,
            codegen.final_expr.clone(),
        )
        .map(|x| x.1)
        .unwrap_or_else(|| codegen.final_expr.clone()))
    }

    fn post_codegen_output_optimize(
        &mut self,
        _opts: Rc<dyn CompilerOpts>,
        generated: SExp,
    ) -> Result<SExp, CompileErr> {
        Ok(generated)
    }

    fn duplicate(&self) -> Box<dyn Optimization> {
        Box::new(self.clone())
    }
}
