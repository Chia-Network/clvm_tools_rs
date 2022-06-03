use std::borrow::Borrow;
use std::collections::{BTreeMap, HashMap};
use std::mem::swap;
use std::rc::Rc;

use clvm_rs::allocator;
use clvm_rs::allocator::{Allocator, NodePtr};
use clvm_rs::reduction::EvalErr;
use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm_tools::sha256tree::sha256tree;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm;
use crate::compiler::clvm::{convert_from_clvm_rs, run_step, RunStep};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

#[derive(Clone, Debug)]
pub struct PriorResult {
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

pub trait CldbRunnable {
    fn replace_step(&self, step: &RunStep) -> Option<Result<RunStep, RunFailure>>;
}

pub trait CldbEnvironment {
    fn add_context(
        &self,
        s: &SExp,
        c: &SExp,
        args: Option<Rc<SExp>>,
        context_result: &mut BTreeMap<String, String>,
    );
    fn add_function(&self, s: &SExp, context_result: &mut BTreeMap<String, String>);
    fn get_override(&self, s: &RunStep) -> Option<Result<RunStep, RunFailure>>;
}

pub struct CldbRun {
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    env: Box<dyn CldbEnvironment>,

    step: RunStep,

    ended: bool,
    final_result: Option<Rc<SExp>>,
    to_print: BTreeMap<String, String>,
    in_expr: bool,
    row: usize,

    outputs_to_step: HashMap<Number, PriorResult>,
}

impl CldbRun {
    pub fn new(
        runner: Rc<dyn TRunProgram>,
        prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
        env: Box<dyn CldbEnvironment>,
        step: RunStep,
    ) -> Self {
        CldbRun {
            runner,
            prim_map,
            env,
            step,
            ended: false,
            final_result: None,
            to_print: BTreeMap::new(),
            in_expr: false,
            row: 0,
            outputs_to_step: HashMap::<Number, PriorResult>::new(),
        }
    }

    pub fn is_ended(&self) -> bool {
        self.ended
    }

    pub fn final_result(&self) -> Option<Rc<SExp>> {
        self.final_result.clone()
    }

    pub fn step(&mut self, allocator: &mut Allocator) -> Option<BTreeMap<String, String>> {
        let mut produce_result = false;
        let mut result = BTreeMap::new();
        let new_step = match self.env.get_override(&self.step) {
            Some(v) => v,
            _ => run_step(
                allocator,
                self.runner.clone(),
                self.prim_map.clone(),
                &self.step,
            ),
        };

        // Allow overrides by consumers.

        match &new_step {
            Ok(RunStep::OpResult(l, x, _p)) => {
                if self.in_expr {
                    self.to_print
                        .insert("Result-Location".to_string(), l.to_string());
                    self.to_print.insert("Value".to_string(), x.to_string());
                    self.to_print
                        .insert("Row".to_string(), self.row.to_string());
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
                self.to_print
                    .insert("Final-Location".to_string(), l.to_string());
                self.to_print.insert("Final".to_string(), x.to_string());

                self.ended = true;
                self.final_result = Some(x.clone());
                swap(&mut self.to_print, &mut result);
                produce_result = true;
            }
            Ok(RunStep::Step(_sexp, _c, _p)) => {}
            Ok(RunStep::Op(sexp, c, a, None, _p)) => {
                self.to_print
                    .insert("Operator-Location".to_string(), a.loc().to_string());
                self.to_print
                    .insert("Operator".to_string(), sexp.to_string());
                match sexp.get_number().ok() {
                    Some(v) => {
                        if v == 11_u32.to_bigint().unwrap() {
                            // Build source tree for hashes.
                            let arg_associations =
                                get_arg_associations(&self.outputs_to_step, a.clone());
                            let args = format_arg_inputs(&arg_associations);
                            self.to_print.insert("Argument-Refs".to_string(), args);
                        }
                    }
                    _ => {}
                }
                self.env.add_context(
                    sexp.borrow(),
                    c.borrow(),
                    Some(a.clone()),
                    &mut self.to_print,
                );
                self.env.add_function(sexp, &mut self.to_print);
                self.in_expr = true;
            }
            Ok(RunStep::Op(_sexp, _c, _a, Some(_v), _p)) => {}
            Err(RunFailure::RunExn(l, s)) => {
                self.to_print
                    .insert("Throw-Location".to_string(), l.to_string());
                self.to_print.insert("Throw".to_string(), s.to_string());

                swap(&mut self.to_print, &mut result);
                self.ended = true;
                produce_result = true;
            }
            Err(RunFailure::RunErr(l, s)) => {
                self.to_print
                    .insert("Failure-Location".to_string(), l.to_string());
                self.to_print.insert("Failure".to_string(), s.to_string());

                swap(&mut self.to_print, &mut result);
                self.ended = true;
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

pub struct CldbNoOverride {
    symbol_table: HashMap<String, String>,
}

impl CldbRunnable for CldbNoOverride {
    fn replace_step(&self, _step: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        None
    }
}

impl CldbNoOverride {
    pub fn new() -> Self {
        CldbNoOverride {
            symbol_table: HashMap::new(),
        }
    }

    pub fn new_symbols(symbol_table: HashMap<String, String>) -> Self {
        CldbNoOverride { symbol_table }
    }
}

// Allow the caller to examine environment and return an expression that
// will be quoted.
pub trait CldbSingleBespokeOverride {
    fn get_override(&self, env: Rc<SExp>) -> Result<Rc<SExp>, RunFailure>;
}

pub struct CldbOverrideBespokeCode {
    symbol_table: HashMap<String, String>,
    overrides: HashMap<String, Box<dyn CldbSingleBespokeOverride>>,
}

impl CldbOverrideBespokeCode {
    pub fn new(
        symbol_table: HashMap<String, String>,
        overrides: HashMap<String, Box<dyn CldbSingleBespokeOverride>>,
    ) -> Self {
        CldbOverrideBespokeCode {
            symbol_table,
            overrides,
        }
    }

    fn find_function_and_override_if_needed(
        &self,
        sexp: Rc<SExp>,
        _c: Rc<SExp>,
        f: Rc<SExp>,
        args: Rc<SExp>,
        p: Rc<RunStep>,
    ) -> Option<Result<RunStep, RunFailure>> {
        let fun_hash = clvm::sha256tree(f.clone());
        let fun_hash_str = Bytes::new(Some(BytesFromType::Raw(fun_hash))).hex();

        self.symbol_table
            .get(&fun_hash_str)
            .and_then(|funname| self.overrides.get(funname))
            .map(|override_fn| {
                override_fn
                    .get_override(args.clone())
                    .map(|new_exp| RunStep::OpResult(sexp.loc(), new_exp.clone(), p.clone()))
            })
    }
}

impl CldbRunnable for CldbOverrideBespokeCode {
    fn replace_step(&self, step: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        match step {
            RunStep::Op(sexp, c, a, None, p) => match sexp.borrow() {
                SExp::Integer(_, i) => {
                    if *i == 2_u32.to_bigint().unwrap() {
                        match a.borrow() {
                            SExp::Cons(_, f, args) => self.find_function_and_override_if_needed(
                                sexp.clone(),
                                c.clone(),
                                f.clone(),
                                args.clone(),
                                p.clone(),
                            ),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
}

pub struct CldbRunEnv {
    input_file: Option<String>,
    program_lines: Vec<String>,
    overrides: Box<dyn CldbRunnable>,
}

impl CldbRunEnv {
    pub fn new(
        input_file: Option<String>,
        program_lines: Vec<String>,
        runnable: Box<dyn CldbRunnable>,
    ) -> Self {
        CldbRunEnv {
            input_file,
            program_lines,
            overrides: runnable,
        }
    }

    fn extract_text(&self, l: &Srcloc) -> Option<String> {
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
                let use_col = coords.1;
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
        if_false: &dyn Fn(&mut BTreeMap<String, String>),
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
        context_result: &mut BTreeMap<String, String>,
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

    fn add_function(&self, s: &SExp, context_result: &mut BTreeMap<String, String>) {
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

    fn get_override(&self, s: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        self.overrides.replace_step(s)
    }
}

pub fn hex_to_modern_sexp_inner(
    allocator: &mut Allocator,
    symbol_table: &HashMap<String, String>,
    loc: Srcloc,
    program: NodePtr,
) -> Result<Rc<SExp>, EvalErr> {
    let hash = sha256tree(allocator, program);
    let hash_str = hash.hex();
    let srcloc = symbol_table
        .get(&hash_str)
        .map(|f| Srcloc::start(f))
        .unwrap_or_else(|| loc.clone());

    match allocator.sexp(program) {
        allocator::SExp::Pair(a, b) => Ok(Rc::new(SExp::Cons(
            srcloc.clone(),
            hex_to_modern_sexp_inner(allocator, symbol_table, srcloc.clone(), a)?,
            hex_to_modern_sexp_inner(allocator, symbol_table, srcloc, b)?,
        ))),
        _ => convert_from_clvm_rs(allocator, srcloc, program).map_err(|_| {
            EvalErr(
                Allocator::null(allocator),
                "clvm_rs allocator failed".to_string(),
            )
        }),
    }
}

pub fn hex_to_modern_sexp(
    allocator: &mut Allocator,
    symbol_table: &HashMap<String, String>,
    loc: Srcloc,
    input_program: &String,
) -> Result<Rc<SExp>, RunFailure> {
    let input_serialized = Bytes::new(Some(BytesFromType::Hex(input_program.to_string())));

    let mut stream = Stream::new(Some(input_serialized.clone()));
    let sexp = sexp_from_stream(allocator, &mut stream, Box::new(SimpleCreateCLVMObject {}))
        .map(|x| x.1)
        .map_err(|_| RunFailure::RunErr(loc.clone(), "Bad conversion from hex".to_string()))?;

    hex_to_modern_sexp_inner(allocator, symbol_table, loc.clone(), sexp).map_err(|_| {
        RunFailure::RunErr(loc, "Failed to convert from classic to modern".to_string())
    })
}
