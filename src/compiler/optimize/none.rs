use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen,
};
use crate::compiler::optimize::{CodegenOptimizationResult, Optimization};
use crate::compiler::sexp::SExp;

/// A basic implementation of Optimization that never transforms anything.
#[derive(Default, Clone)]
pub struct NoOptimization {}

impl NoOptimization {
    pub fn new() -> Self {
        NoOptimization {}
    }
}

impl Optimization for NoOptimization {
    fn frontend_optimization(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        p0: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        Ok(p0)
    }

    fn post_desugar_optimization(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        Ok(cf)
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
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        Ok(code)
    }

    fn defun_body_optimization(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        _codegen: &PrimaryCodegen,
        defun: &DefunData,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        Ok(defun.body.clone())
    }

    fn post_codegen_function_optimize(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        Ok(code)
    }

    fn pre_final_codegen_optimize(
        &mut self,
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        Ok(codegen.final_expr.clone())
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
