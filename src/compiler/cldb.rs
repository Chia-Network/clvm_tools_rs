use std::borrow::Borrow;
use std::collections::{ BTreeMap, HashMap };
use std::mem::swap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;
use num_bigint::ToBigInt;

use crate::classic::clvm_tools::stages::stage_0::{
    TRunProgram
};
use crate::compiler::clvm::{RunStep, run_step, get_history_len};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

#[derive(Clone, Debug)]
pub struct PriorResult{
    reference: usize,
    value: Rc<SExp>,
}

fn format_arg_inputs(args: &Vec<PriorResult>) -> String {
    let value_strings: Vec<String> = args
        .iter()
        .map(|pr| {
            return pr.reference.to_string();
        })
        .collect();
    return value_strings.join(", ");
}

fn get_arg_associations(
    associations: &HashMap<Number, PriorResult>,
    args: Rc<SExp>,
) -> Vec<PriorResult> {
    let mut arg_exp: Rc<SExp> = args;
    let mut result: Vec<PriorResult> = Vec::new();
    loop {
        match arg_exp.borrow() {
            SExp::Cons(_, arg, rest) => {
                match arg
                    .get_number()
                    .ok()
                    .as_ref()
                    .and_then(|n| associations.get(n))
                {
                    Some(n) => {
                        result.push(n.clone());
                    }
                    _ => {}
                }
                arg_exp = rest.clone();
            }
            _ => {
                return result;
            }
        }
    }
}

pub trait CldbEnvironment {
    fn add_context(
        &self,
        s: &SExp,
        c: &SExp,
        args: Option<Rc<SExp>>,
        context_result: &mut BTreeMap<String, String>
    );
    fn add_function(
        &self,
        s: &SExp,
        context_result: &mut BTreeMap<String, String>
    );
}

pub struct CldbRun {
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    env: Box<dyn CldbEnvironment>,

    step: RunStep,

    ended: bool,
    to_print: BTreeMap<String, String>,
    in_expr: bool,
    row: usize,

    outputs_to_step: HashMap::<Number, PriorResult>

}

impl CldbRun {
    pub fn new(
        runner: Rc<dyn TRunProgram>,
        prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
        env: Box<dyn CldbEnvironment>,
        step: RunStep,
    ) -> Self {
        CldbRun {
            runner: runner,
            prim_map: prim_map,
            env: env,
            step: step,
            ended: false,
            to_print: BTreeMap::new(),
            in_expr: false,
            row: 0,
            outputs_to_step: HashMap::<Number, PriorResult>::new()
        }
    }

    pub fn is_ended(&self) -> bool { self.ended }
    pub fn step(
        &mut self,
        allocator: &mut Allocator,
    ) -> Option<BTreeMap<String, String>> {
        let mut produce_result = false;
        let mut result = BTreeMap::new();
        let new_step = run_step(
            allocator,
            self.runner.clone(),
            self.prim_map.clone(),
            &self.step
        );

        match &new_step {
            Ok(RunStep::OpResult(l, x, p)) => {
                if self.in_expr {
                    let history_len = get_history_len(p.clone());
                    self.to_print.insert("Result-Location".to_string(), l.to_string());
                    self.to_print.insert("Value".to_string(), x.to_string());
                    self.to_print.insert("Row".to_string(), self.row.to_string());
                    match x.get_number().ok() {
                        Some(n) => {
                            self.outputs_to_step.insert(
                                n,
                                PriorResult {
                                    reference: self.row,
                                    value: x.clone(),
                                },
                            );
                        }
                        _ => {}
                    }
                    self.in_expr = false;
                    swap(&mut self.to_print, &mut result);
                    produce_result = true;
                }
            }
            Ok(RunStep::Done(l, x)) => {
                self.to_print.insert("Final-Location".to_string(), l.to_string());
                self.to_print.insert("Final".to_string(), x.to_string());

                self.ended = true;
                swap(&mut self.to_print, &mut result);
                produce_result = true;
            }
            Ok(RunStep::Step(sexp, c, p)) => {}
            Ok(RunStep::Op(sexp, c, a, None, p)) => {
                let history_len = get_history_len(p.clone());
                self.to_print.insert("Operator-Location".to_string(), a.loc().to_string());
                self.to_print.insert("Operator".to_string(), sexp.to_string());
                match sexp.get_number().ok() {
                    Some(v) => {
                        if v == 11_u32.to_bigint().unwrap() {
                            let arg_associations =
                                get_arg_associations(&self.outputs_to_step, a.clone());
                            let args = format_arg_inputs(&arg_associations);
                            self.to_print.insert("Argument-Refs".to_string(), args);
                        }
                    }
                    _ => {}
                }
                self.env.add_context(sexp.borrow(), c.borrow(), Some(a.clone()), &mut self.to_print);
                self.env.add_function(sexp, &mut self.to_print);
                self.in_expr = true;
            }
            Ok(RunStep::Op(sexp, c, a, Some(v), p)) => {}
            Err(RunFailure::RunExn(l, s)) => {
                self.to_print.insert("Throw-Location".to_string(), l.to_string());
                self.to_print.insert("Throw".to_string(), s.to_string());

                swap(&mut self.to_print, &mut result);
                produce_result = true;
            }
            Err(RunFailure::RunErr(l, s)) => {
                self.to_print.insert("Failure-Location".to_string(), l.to_string());
                self.to_print.insert("Failure".to_string(), s.to_string());

                swap(&mut self.to_print, &mut result);
                produce_result = true;
            }
        }

        self.step = new_step.unwrap_or_else(|_| self.step.clone());
        if produce_result {
            self.row += 1;
            Some(result)
        } else {
            None
        }
    }
}

pub struct CldbRunEnv {
    input_file: Option<String>,
    program_lines: Vec<String>
}

impl CldbRunEnv {
    pub fn new(input_file: Option<String>, program_lines: Vec<String>) -> Self {
        CldbRunEnv {
            input_file: input_file,
            program_lines: program_lines
        }
    }

    fn extract_text(
        &self,
        l: &Srcloc
    ) -> Option<String> {
        let use_line = if l.line < 1 { None } else { Some(l.line - 1) };
        let use_col = use_line.and_then(|_| if l.col < 1 { None } else { Some(l.col - 1) });
        let end_col = use_col.map(|c| l.until.map(|u| u.1 - 1).unwrap_or_else(|| c + 1));
        use_line
            .and_then(|use_line| {
                use_col.and_then(|use_col| {
                    end_col.and_then(|end_col| Some((use_line, use_col, end_col)))
                })
            })
            .and_then(|coords| {
                let use_line = coords.0;
                let mut use_col = coords.1;
                let mut end_col = coords.2;

                if use_line >= self.program_lines.len() {
                    None
                } else {
                    let line_text = self.program_lines[use_line].to_string();
                    if use_col >= line_text.len() {
                        None
                    } else if end_col >= line_text.len() {
                        end_col = line_text.len();
                        Some(line_text[use_col..end_col].to_string())
                    } else {
                        Some(line_text[use_col..end_col].to_string())
                    }
                }
            })
    }

    fn whether_is_apply(
        &self,
        s: &SExp,
        collector: &mut BTreeMap<String, String>,
        if_true: &dyn Fn(&mut BTreeMap<String, String>),
        if_false: &dyn Fn(&mut BTreeMap<String, String>)
    ) {
        match s {
            SExp::Integer(_, i) => {
                if *i == 2_i32.to_bigint().unwrap() {
                    if_true(collector);
                    return;
                }
            }
            _ => {}
        }

        if_false(collector);
    }
}

impl CldbEnvironment for CldbRunEnv {
    fn add_context(
        &self,
        s: &SExp,
        c: &SExp,
        args: Option<Rc<SExp>>,
        context_result: &mut BTreeMap<String, String>
    ) {
        self.whether_is_apply(
            s,
            context_result,
            &|context_result| match c {
                SExp::Cons(_, a, b) => {
                    context_result.insert("Env".to_string(), a.to_string());
                    context_result.insert("Env-Args".to_string(), b.to_string());
                }
                _ => {
                    context_result.insert("Function-Context".to_string(), c.to_string());
                }
            },
            &|context_result| match &args {
                Some(a) => {
                    context_result.insert("Arguments".to_string(), a.to_string());
                }
                _ => {}
            },
        );
    }

    fn add_function(
        &self,
        s: &SExp,
        context_result: &mut BTreeMap<String, String>
    ) {
        self.whether_is_apply(
            s,
            context_result,
            &|_context_result| {},
            &|context_result| match self.extract_text(&s.loc()) {
                Some(name) => {
                    if Some(s.loc().file.to_string()) == self.input_file.clone() {
                        context_result.insert("Function".to_string(), name);
                    }
                }
                _ => {}
            },
        );
    }
}
