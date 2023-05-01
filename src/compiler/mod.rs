use std::collections::HashMap;
use std::rc::Rc;
use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::platform::argparse::{
    ArgumentParser, ArgumentValue
};

use crate::compiler::comptypes::{CompileErr, CompileForm, CompilerOpts};
use crate::compiler::sexp::SExp;

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
///
pub mod debug;
pub mod evaluate;
pub mod frontend;
pub mod gensym;
mod inline;
mod optimize;
pub mod preprocessor;
pub mod prims;
pub mod rename;
pub mod repl;
pub mod runtypes;
pub mod sexp;
pub mod srcloc;
pub mod stackvisit;
#[cfg(feature="test-constant-deinline")]
pub mod test_deinline;
pub mod usecheck;

/// The type of compilers.  Use features to change this type.
#[cfg(not(feature="test-constant-deinline"))]
pub type UseCompilerVariant = crate::compiler::compiler::BasicCompiler;
#[cfg(feature="test-constant-deinline")]
pub type UseCompilerVariant = crate::compiler::test_deinline::Compiler;

pub trait CompilerTask {
    type Save;

    fn get_allocator<'a>(&'a mut self) -> &'a mut Allocator;
    fn get_symbol_table<'a>(&'a mut self) -> &'a mut HashMap<String, String>;
    fn empty_save_state(&self) -> Self::Save;
    fn swap_save_state(&mut self, save: &mut Self::Save);

    fn for_new_program<'a, F, R>(&'a mut self, f: F) -> R where F: Fn(&mut Self) -> R {
        let mut old_save = self.empty_save_state();
        self.swap_save_state(&mut old_save);
        let res = f(self);
        self.swap_save_state(&mut old_save);
        res
    }

    fn setup_new_options(&mut self, argparse: &mut ArgumentParser);

    fn evaluate_cmd_options(&mut self, options: &HashMap<String, ArgumentValue>);
    fn evaluate_python_options(&mut self, options: &HashMap<String, String>);

    fn do_frontend_step(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, pre_forms: &[Rc<SExp>]) -> Result<CompileForm, CompileErr>;
    fn do_frontend_pre_desugar_opt(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr>;
    fn do_desugaring(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr>;
    // Insert a post desugaring optimization step when needed.
    fn do_code_generation(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<SExp, CompileErr>;
    // Insert a post code generation optimization step when needed.
}
