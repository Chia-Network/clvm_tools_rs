use std::borrow::Borrow;
use std::collections::HashMap;
use std::mem::swap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::platform::argparse::{
    Argument, ArgumentParser, ArgumentValue, TArgOptionAction
};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::CompilerTask;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, CompilerOpts};
use crate::compiler::compiler::BasicCompiler;
use crate::compiler::gensym::gensym;
use crate::compiler::prims::{primapply, primcons, primquote};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

/// Represents as program with all the constant values that would otherwise have
/// allowed the main expression to be optimized away pulled out and placed in
/// constants.
///
/// Gives a method to compose a recombined program to run.
pub struct ProgramWithConstants {
    pub program: CompileForm,
    pub constants: Rc<SExp>
}

fn replace_constant_with_symbol(collected: &mut HashMap<Vec<u8>, Rc<SExp>>, q: &SExp) -> BodyForm {
    let new_name = gensym(b"lifted_constant".to_vec());
    collected.insert(new_name.clone(), Rc::new(q.clone()));
    BodyForm::Value(SExp::Atom(q.loc(), new_name))
}

fn lift_constants_bodyform(collected: &mut HashMap<Vec<u8>, Rc<SExp>>, bf: &BodyForm) -> BodyForm {
    match bf {
        BodyForm::Quoted(q) => {
            replace_constant_with_symbol(collected, &q)
        },
        BodyForm::Value(SExp::Atom(_l,a)) => {
            bf.clone()
        },
        BodyForm::Value(q) => {
            replace_constant_with_symbol(collected, &q)
        },
        BodyForm::Call(l, args) => {
            let new_args = args.iter().map(|a| {
                lift_constants_bodyform(collected, &a)
            }).map(Rc::new).collect();
            BodyForm::Call(l.clone(), new_args)
        },
        BodyForm::Let(kind, letdata) => {
            let new_bindings = letdata.bindings.iter().map(|b| {
                let new_body = lift_constants_bodyform(collected, b.body);
                Binding {
                    body: new_body,
                    .. b.clone()
                }
            }).collect();
            let new_body = lift_constants_bodyform(collected, letdata.body);
            BodyForm::Let(kind, LetData {
                bindings: new_bindings,
                body: new_body,
                .. letdata.clone()
            })
        },
        // We're just removing obstacles to emitting executable code so
        // we don't need to treat lambda or mod objects here.
        _ => { bf.clone() }
    }
}

fn create_value_tree<F>(constants: &Vec<(Vec<u8>, Rc<SExp>)>, l: &Srcloc, start: usize, end: usize, f: &F) -> Rc<SExp> where F: Fn(Vec<u8>, Rc<SExp>) -> Rc<SExp> {
    let interval_len = end - start;
    if interval_len == 0 {
        Rc::new(SExp::Nil(l.clone()))
    } else if interval_len == 1 {
        f(constants[start].0.clone(), constants[start].1.clone())
    } else {
        let mid = start + ((end - start) / 2);
        let left_half = create_value_tree(constants, l, start, mid, f);
        let right_half = create_value_tree(constants, l, mid, end, f);
        Rc::new(SExp::Cons(l.clone(), left_half, right_half))
    }
}

fn key_to_atom(k: Vec<u8>, v: Rc<SExp>) -> Rc<SExp> {
    Rc::new(SExp::Atom(v.loc(), k.to_vec()))
}

fn value_from_pair(k: Vec<u8>, v: Rc<SExp>) -> Rc<SExp> { v.clone() }

fn create_lifted_constants_args_prefix(constants: &HashMap<Vec<u8>, Rc<SExp>>, l: &Srcloc) -> (Rc<SExp>, Rc<SExp>) {
    let pairs: Vec<(Vec<u8>, Rc<SExp>)> =
        constants.iter().map(|(k,v)| (k.clone(), v.clone())).collect();
    let names = create_value_tree(&pairs, l, 0, pairs.len(), &key_to_atom);
    let values = create_value_tree(&pairs, l, 0, pairs.len(), &value_from_pair);
    (names, values)
}

impl ProgramWithConstants {
    pub fn make_testable(cf: CompileForm) -> Self {
        let mut lifted_constants = HashMap::new();
        let new_body =
            lift_constants_bodyform(&mut lifted_constants, cf.exp.borrow());
        let (new_args_prefix, new_args_values) =
            create_lifted_constants_args_prefix(&lifted_constants, &cf.loc);
        let new_args_for_program =
            Rc::new(SExp::Cons(
                cf.args.loc(),
                new_args_prefix,
                cf.args.clone()
            ));
        ProgramWithConstants {
            program: CompileForm {
                args: new_args_for_program,
                exp: Rc::new(new_body),
                .. cf.clone()
            },
            constants: new_args_values
        }
    }

    pub fn make_runnable(&self, code: Rc<SExp>) -> SExp {
        primapply(
            code.loc(),
            Rc::new(primquote(code.loc(), code.clone())),
            Rc::new(primcons(
                code.loc(),
                Rc::new(primquote(
                    code.loc(),
                    self.constants.clone()
                )),
                Rc::new(SExp::Atom(code.loc(), vec![1])) // Whole env
            ))
        )
    }
}

enum OperationState {
    NotYetRun,
    ResultExpected(ProgramWithConstants)
}

#[derive(Default)]
pub struct Compiler {
    basic: BasicCompiler,

    enabled: Option<OperationState>,
}

#[derive(Default)]
pub struct SaveState {
    basic: <BasicCompiler as CompilerTask>::Save,

    enabled: Option<OperationState>
}

// Deinline constants so code can be tested.
// This prevents full evaluation at compile time regardless of any optimization
// (even sophisticated optimization in the future).
//
// Given any CompileForm, identify constants in the main expression and turn them
// into arguments.
//
// Output the program and the arguments separately as
// (CompileForm, Rc<SExp>)
// where the constants have been added as a first parameter.
//
// (mod (X) ...) -> (mod (constants X) ...)
//
// What's desired is that we get the same result as the original program by
// applying this program with its constants:
//
// (a program (c constants 1))

// Set up arguments for running with deinlining.
impl CompilerTask for Compiler {
    type Save = SaveState;

    fn get_allocator<'a>(&'a mut self) -> &'a mut Allocator {
        self.basic.get_allocator()
    }

    fn get_symbol_table<'a>(&'a mut self) -> &'a mut HashMap<String, String> {
        self.basic.get_symbol_table()
    }

    fn empty_save_state(&self) -> Self::Save { Default::default() }
    fn swap_save_state(&mut self, save: &mut Self::Save) {
        self.basic.swap_save_state(&mut save.basic);
        swap(&mut self.enabled, &mut save.enabled);
    }

    fn setup_new_options(&mut self, argparse: &mut ArgumentParser) {
        self.basic.setup_new_options(argparse);
        argparse.add_argument(
            vec!["--test-deinline".to_string()],
            Argument::new()
                .set_action(TArgOptionAction::StoreTrue)
                .set_help("Deinline constants to enable chialisp testing in chialisp".to_string())
        );
    }

    fn evaluate_cmd_options(&mut self, options: &HashMap<String, ArgumentValue>) {
        self.basic.evaluate_cmd_options(options);
        let do_enable = options.get("test_deinline").map(|a| {
            if let ArgumentValue::ArgBool(b) = a {
                *b
            } else {
                false
            }
        }).unwrap_or_else(|| false);
        eprintln!("do_enable {do_enable}");
        self.enabled = if do_enable {
            Some(OperationState::NotYetRun)
        } else {
            None
        }
    }

    fn evaluate_python_options(&mut self, options: &HashMap<String, String>) {
        self.basic.evaluate_python_options(options);
        let do_enable = options.get("test-deinline").map(|_| true).unwrap_or_else(|| false);
        self.enabled = if do_enable {
            Some(OperationState::NotYetRun)
        } else {
            None
        }
    }

    fn do_frontend_step(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, pre_forms: &[Rc<SExp>]) -> Result<CompileForm, CompileErr> {
        let res = self.basic.do_frontend_step(runner, opts, pre_forms)?;

        if matches!(self.enabled, Some(OperationState::NotYetRun)) {
            let transformation = ProgramWithConstants::make_testable(res);
            let result_program = transformation.program.clone();
            eprintln!("result_program {}", result_program.to_sexp());
            self.enabled = Some(OperationState::ResultExpected(transformation));
            Ok(result_program)
        } else {
            Ok(res)
        }
    }

    fn do_frontend_pre_desugar_opt(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr> {
        self.basic.do_frontend_pre_desugar_opt(runner, opts, cf)
    }

    fn do_desugaring(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<CompileForm, CompileErr> {
        self.basic.do_desugaring(runner, opts, cf)
    }

    fn do_code_generation(&mut self, runner: Rc<dyn TRunProgram>, opts: Rc<dyn CompilerOpts>, cf: CompileForm) -> Result<SExp, CompileErr> {
        let res = self.basic.do_code_generation(runner, opts, cf)?;
        if let Some(OperationState::ResultExpected(pwc)) = &self.enabled {
            Ok(pwc.make_runnable(Rc::new(res)))
        } else {
            Ok(res.clone())
        }
    }
}
