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
/// Utilities for chialisp dialect choice
pub mod dialect;
pub mod evaluate;
pub mod frontend;
pub mod gensym;
mod inline;
pub mod optimize;
pub mod preprocessor;
pub mod prims;
pub mod rename;
pub mod repl;
pub mod runtypes;
pub mod sexp;
pub mod srcloc;
pub mod stackvisit;
pub mod usecheck;

use clvmr::allocator::Allocator;
use std::collections::HashMap;
use std::mem::swap;
use std::rc::Rc;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::compiler::comptypes::{
    BodyForm, CompileErr, CompileForm, CompilerOpts, DefunData, HelperForm, PrimaryCodegen,
};
use crate::compiler::sexp::SExp;

/// An object which represents the standard set of mutable items passed down the
/// stack when compiling chialisp.
pub struct BasicCompileContext {
    pub allocator: Allocator,
    pub runner: Rc<dyn TRunProgram>,
    pub symbols: HashMap<String, String>,
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

    pub fn new(
        allocator: Allocator,
        runner: Rc<dyn TRunProgram>,
        symbols: HashMap<String, String>,
    ) -> Self {
        BasicCompileContext {
            allocator,
            runner,
            symbols,
        }
    }
}

pub struct CompileContextWrapper<'a> {
    pub allocator: &'a mut Allocator,
    pub symbols: &'a mut HashMap<String, String>,
    pub context: BasicCompileContext,
}

impl<'a> CompileContextWrapper<'a> {
    pub fn new(
        allocator: &'a mut Allocator,
        runner: Rc<dyn TRunProgram>,
        symbols: &'a mut HashMap<String, String>,
    ) -> Self {
        let bcc = BasicCompileContext {
            allocator: Allocator::new(),
            runner,
            symbols: HashMap::new(),
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
