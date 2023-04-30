use std::collections::HashMap;
use std::rc::Rc;
use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

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
pub mod usecheck;

/// The type of compilers.  Use features to change this type.
pub type UseCompilerVariant = crate::compiler::compiler::BasicCompiler;

pub trait CompilerTask {
    fn get_allocator<'a>(&'a mut self) -> &'a mut Allocator;
    fn get_symbol_table<'a>(&'a mut self) -> &'a mut HashMap<String, String>;
    fn for_new_program<'a, F, R>(&'a mut self, f: F) -> R where F: Fn(&mut Self) -> R;

    fn do_frontend_step(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, pre_forms: &[Rc<SExp>]) -> Result<CompileForm, CompileErr>;
    fn do_frontend_pre_desugar_opt(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr>;
    fn do_desugaring(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr>;
    // Insert a post desugaring optimization step when needed.
    fn do_code_generation(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<SExp, CompileErr>;
    // Insert a post code generation optimization step when needed.
}
