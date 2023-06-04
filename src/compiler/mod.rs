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
mod optimize;
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

use std::collections::HashMap;
use std::mem::swap;
use std::rc::Rc;
use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::compiler::optimize::Optimization;

/// An object which represents the standard set of mutable items passed down the
/// stack when compiling chialisp.
pub struct BasicCompileContext {
    pub allocator: Allocator,
    pub runner: Rc<dyn TRunProgram>,
    pub symbols: HashMap<String, String>,
    pub optimizer: Box<dyn Optimization>,
}

trait CompileContext {
    fn allocator(&mut self) -> &mut Allocator;
    fn runner(&self) -> Rc<dyn TRunProgram>;
    fn symbols(&mut self) -> &mut HashMap<String, String>;
    fn run_optimizer<F,R>(&mut self, f: F) -> R
    where F: Fn(&mut dyn Optimization) -> R;
}

impl CompileContext for BasicCompileContext {
    fn allocator(&mut self) -> &mut Allocator {
        &mut self.allocator
    }
    fn runner(&self) -> Rc<dyn TRunProgram> {
        self.runner.clone()
    }
    fn symbols(&mut self) -> &mut HashMap<String, String> {
        &mut self.symbols
    }
    fn run_optimizer<F,R>(&mut self, f: F) -> R
    where F: Fn(&mut dyn Optimization) -> R
    {
        f(self.optimizer.as_mut())
    }
}

impl BasicCompileContext {
    pub fn new(
        allocator: Allocator,
        runner: Rc<dyn TRunProgram>,
        symbols: HashMap<String, String>,
        optimizer: Box<dyn Optimization>,
    ) -> Self {
        BasicCompileContext {
            allocator, runner, symbols, optimizer
        }
    }
}

struct CompileContextWrapper<'a> {
    allocator: &'a mut Allocator,
    symbols: &'a mut HashMap<String, String>,
    context: BasicCompileContext
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
            runner: runner,
            symbols: HashMap::new(),
            optimizer: optimizer
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
