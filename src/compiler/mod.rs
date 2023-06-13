/// Chialisp debugging.
pub mod cldb;
pub mod cldb_hierarchy;
/// CLVM running.
pub mod clvm;
mod codegen;
/// CompilerOpts which is the main holder of toplevel compiler state.
#[allow(clippy::module_inception)]
pub mod compiler;
/// Types used by compilation, mainly frontend directed, including.
/// - BodyForm - The type of frontend expressions.
/// - CompileErr - The type of errors from compilation.
/// - CompileForm - The type of finished (mod ) forms before code generation.
/// - HelperForm - The type of declarations like macros, constants and functions.
pub mod comptypes;
pub mod debug;
/// Dialect definitions.
pub mod dialect;
pub mod evaluate;
pub mod frontend;
pub mod gensym;
mod inline;
mod lambda;
pub mod optimize;
pub mod preprocessor;
pub mod prims;
pub mod rename;
pub mod repl;
pub mod runtypes;
pub mod sexp;
pub mod srcloc;
pub mod stackvisit;
pub mod typecheck;
pub mod typechia;
pub mod types;
pub mod untype;
pub mod usecheck;

use clvmr::allocator::Allocator;
use std::collections::HashMap;
use std::mem::swap;
use std::rc::Rc;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen,
};
use crate::compiler::optimize::Optimization;
use crate::compiler::sexp::SExp;

/// An object which represents the standard set of mutable items passed down the
/// stack when compiling chialisp.
pub struct BasicCompileContext {
    pub allocator: Allocator,
    pub runner: Rc<dyn TRunProgram>,
    pub symbols: HashMap<String, String>,
    pub optimizer: Box<dyn Optimization>,
}

impl BasicCompileContext {
    fn allocator(&mut self) -> &mut Allocator {
        &mut self.allocator
    }
    fn runner(&self) -> Rc<dyn TRunProgram> {
        self.runner.clone()
    }
    fn symbols(&mut self) -> &mut HashMap<String, String> {
        &mut self.symbols
    }

    /// Called after frontend parsing and preprocessing when we have a complete
    /// picture of the user's intended semantics.
    fn frontend_optimization(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        let runner = self.runner.clone();
        self.optimizer
            .frontend_optimization(&mut self.allocator, runner, opts, cf)
    }

    fn post_desugar_optimization(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        cf: CompileForm,
    ) -> Result<CompileForm, CompileErr> {
        let runner = self.runner.clone();
        self.optimizer
            .post_desugar_optimization(&mut self.allocator, runner, opts, cf)
    }

    /// Shrink the program prior to generating the final environment map and
    /// doing other codegen tasks.  This also serves as a tree-shaking pass.
    fn start_of_codegen_optimization(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        to_optimize: StartOfCodegenOptimization,
    ) -> Result<StartOfCodegenOptimization, CompileErr> {
        let runner = self.runner.clone();
        self.optimizer
            .start_of_codegen_optimization(&mut self.allocator, runner, opts, to_optimize)
    }

    /// Note: must take measures to ensure that the symbols are changed along
    /// with any code that's changed.  It's likely better to do optimizations
    /// at other stages, such as post_codegen_function_optimize.
    fn post_codegen_output_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        generated: SExp,
    ) -> Result<SExp, CompileErr> {
        self.optimizer.post_codegen_output_optimize(opts, generated)
    }

    /// Called when a full macro program optimization is used.
    fn macro_optimization(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        self.optimizer
            .macro_optimization(&mut self.allocator, self.runner.clone(), opts, code)
    }

    /// Called to transform a defun before generating code from it.
    /// Returns a new bodyform.
    fn pre_codegen_function_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
        defun: &DefunData,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        self.optimizer.defun_body_optimization(
            &mut self.allocator,
            self.runner.clone(),
            opts,
            codegen,
            defun,
        )
    }

    /// Called to transform the function body after code generation.
    fn post_codegen_function_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        helper: Option<&HelperForm>,
        code: Rc<SExp>,
    ) -> Result<Rc<SExp>, CompileErr> {
        self.optimizer.post_codegen_function_optimize(
            &mut self.allocator,
            self.runner.clone(),
            opts,
            helper,
            code,
        )
    }

    /// Call in final_codegen to get the final main bodyform to generate
    /// code from.
    fn pre_final_codegen_optimize(
        &mut self,
        opts: Rc<dyn CompilerOpts>,
        codegen: &PrimaryCodegen,
    ) -> Result<Rc<BodyForm>, CompileErr> {
        self.optimizer.pre_final_codegen_optimize(
            &mut self.allocator,
            self.runner.clone(),
            opts,
            codegen,
        )
    }

    pub fn new(
        allocator: Allocator,
        runner: Rc<dyn TRunProgram>,
        symbols: HashMap<String, String>,
        optimizer: Box<dyn Optimization>,
    ) -> Self {
        BasicCompileContext {
            allocator,
            runner,
            symbols,
            optimizer,
        }
    }
}

struct CompileContextWrapper<'a> {
    allocator: &'a mut Allocator,
    symbols: &'a mut HashMap<String, String>,
    context: BasicCompileContext,
}

impl<'a> CompileContextWrapper<'a> {
    pub fn new(
        allocator: &'a mut Allocator,
        runner: Rc<dyn TRunProgram>,
        symbols: &'a mut HashMap<String, String>,
        optimizer: Box<dyn Optimization>,
    ) -> Self {
        let bcc = BasicCompileContext {
            allocator: Allocator::new(),
            runner,
            symbols: HashMap::new(),
            optimizer,
        };
        let mut wrapper = CompileContextWrapper {
            allocator,
            symbols,
            context: bcc,
        };
        wrapper.switch();
        wrapper
    }

    fn switch(&mut self) {
        swap(self.allocator, &mut self.context.allocator);
        swap(self.symbols, &mut self.context.symbols);
    }
}

impl<'a> Drop for CompileContextWrapper<'a> {
    fn drop(&mut self) {
        self.switch();
    }
}

/// Describes the unique inputs and outputs available at the start of code
/// generation.
#[derive(Debug, Clone)]
pub struct StartOfCodegenOptimization {
    program: CompileForm,
    code_generator: PrimaryCodegen,
}
