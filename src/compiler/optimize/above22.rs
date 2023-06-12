use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen,
};
use crate::compiler::optimize::brief::brief_path_selection;
use crate::compiler::optimize::cse::cse_optimize_bodyform;
use crate::compiler::optimize::double_apply::remove_double_apply;
use crate::compiler::optimize::{
    deinline_opt, null_optimization, optimize_expr, run_optimizer, CompileContextWrapper,
    Optimization,
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
        mut p0: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        let mut rebuilt_helpers = Vec::new();
        for h in p0.helpers.iter() {
            if let HelperForm::Defun(inline, d) = h {
                let function_body = cse_optimize_bodyform(&h.loc(), h.name(), d.body.borrow())?;

                // Ok we've got a body that is now a let stack.
                let new_helper = HelperForm::Defun(
                    *inline,
                    DefunData {
                        body: Rc::new(function_body),
                        ..d.clone()
                    },
                );

                rebuilt_helpers.push(new_helper);
            } else {
                rebuilt_helpers.push(h.clone());
            }
        }

        p0.helpers = rebuilt_helpers;
        Ok(p0)
    }

    fn post_desugar_optimization(
        &mut self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        let mut symbols = HashMap::new();
        let mut wrapper =
            CompileContextWrapper::new(allocator, runner, &mut symbols, self.duplicate());
        let res = deinline_opt(&mut wrapper.context, opts.clone(), cf)?;
        Ok(res)
    }

    fn start_of_codegen_optimization(
        &mut self,
        code_generator: PrimaryCodegen,
    ) -> Result<PrimaryCodegen, CompileErr> {
        Ok(code_generator)
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
        _allocator: &mut Allocator,
        _runner: Rc<dyn TRunProgram>,
        _opts: Rc<dyn CompilerOpts>,
        _helper: Option<&HelperForm>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        let (null_worked, result) = null_optimization(code.clone(), true);
        let (double_worked, dbl_result) = remove_double_apply(result);
        let (brief_worked, brief_result) = brief_path_selection(dbl_result.clone());
        if null_worked || double_worked || brief_worked {
            Ok(brief_result)
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
        let (null_worked, result) = null_optimization(Rc::new(generated.clone()), true);
        let (double_worked, dbl_result) = remove_double_apply(result);
        let (brief_worked, brief_result) = brief_path_selection(dbl_result.clone());
        if null_worked || double_worked || brief_worked {
            let borrowed: &SExp = brief_result.borrow();
            Ok(borrowed.clone())
        } else {
            Ok(generated)
        }
    }

    fn duplicate(&self) -> Box<dyn Optimization> {
        Box::new(self.clone())
    }
}
