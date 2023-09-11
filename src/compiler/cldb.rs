use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::mem::swap;
use std::rc::Rc;

use clvm_rs::allocator;
use clvm_rs::allocator::{Allocator, NodePtr};
use clvm_rs::reduction::EvalErr;
use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{
    Bytes, BytesFromType, Stream, UnvalidatedBytesFromType,
};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
//use crate::classic::clvm::syntax_error::SyntaxErr;
use crate::classic::clvm_tools::sha256tree::sha256tree;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm;
use crate::compiler::clvm::{apply_op, choose_path, convert_from_clvm_rs, convert_to_clvm_rs, PrimOverride, run_step, RunStep, truthy, generate_argument_refs};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{First, SExp, NodeSel, SelectNode, ThisNode, enlist};
use crate::compiler::srcloc::Srcloc;
#[cfg(feature = "debug-print")]
use crate::util::{u8_from_number, number_from_u8};
use crate::util::Number;

#[cfg(feature = "debug-print")]
fn print_atom() -> SExp {
    SExp::Atom(Srcloc::start("*print*"), b"$print$".to_vec())
}

type JitMap = HashMap<(u64, u64), ClvmShortCircuit>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ConvKey {
    SExpPtr(u64),
    NodePtr(NodePtr)
}
type ConvMap = HashMap<ConvKey, (Rc<SExp>, NodePtr)>;

#[derive(Clone, Debug)]
pub struct PriorResult {
    reference: usize,
    // value: Rc<SExp>, // In future, we'll want to know the value produced.
}

fn format_arg_inputs(args: &[PriorResult]) -> String {
    let value_strings: Vec<String> = args.iter().map(|pr| pr.reference.to_string()).collect();
    value_strings.join(", ")
}

fn get_arg_associations(
    associations: &HashMap<Number, PriorResult>,
    args: Rc<SExp>,
) -> Vec<PriorResult> {
    let mut arg_exp: Rc<SExp> = args;
    let mut result: Vec<PriorResult> = Vec::new();
    loop {
        if let SExp::Cons(_, arg, rest) = arg_exp.borrow() {
            if let Some(n) = arg
                .get_number()
                .ok()
                .as_ref()
                .and_then(|n| associations.get(n))
            {
                result.push(n.clone());
            }
            arg_exp = rest.clone();
        } else {
            return result;
        }
    }
}

/// An interface which allows consumers to inject their own functionality into
/// cldb runs, including possibly mocking functions, performing tracing and
/// other desired things.  The result of the operation can be dictated when
/// the runnable is asked to replace the step state.
pub trait CldbRunnable {
    fn replace_step(&self, step: &RunStep) -> Option<Result<RunStep, RunFailure>>;
}

#[derive(Debug, Clone)]
pub enum ClvmLinearInstruction {
    Error(RunFailure),
    Literal(Rc<SExp>),
    Operator(Vec<u8>, usize), // Operator, number of arguments
    Path(Vec<u8>),
    PushEnv,
    PopEnv,
    Swap,
    Apply,
}

#[derive(Debug, Clone, Default)]
pub struct ClvmShortCircuit {
    pub instructions: Vec<ClvmLinearInstruction>
}

/// A CldbEnvironment is a container for a function-oriented view of clvm programs
/// when running in Cldb.
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

/// CldbRun is the main object used to run CLVM code in a stepwise way.  The main
/// advantage of CldbRun over clvmr's runner is that the caller observes a new
/// step being returned after it asks for each step to be run.  The progress of
/// evaulation is observable and hopefully understandable and in an order which,
/// combined with observing the RunStep can help with debugging.
///
/// CldmbRun contains a RunStep and moves evaluation forward every time its step
/// method is called, along with having some convenience methods, like being able
/// to ask whether the run ended and what the final result was (if it completed).
///
/// The result is a map of key value pairs indicating various information about
/// the run.
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

    perform_jit: bool,
    allocator: RefCell<Allocator>,
    stored_conversions: RefCell<ConvMap>,
    stored_jit: RefCell<JitMap>,
}

#[cfg(feature = "debug-print")]
fn humanize(a: Rc<SExp>) -> Rc<SExp> {
    match a.borrow() {
        SExp::Integer(l, i) => {
            // If it has a nice string representation then show that.
            let bytes_of_int = u8_from_number(i.clone());
            if bytes_of_int.len() > 2 && bytes_of_int.iter().all(|b| *b >= 32 && *b < 127) {
                Rc::new(SExp::QuotedString(l.clone(), b'\'', bytes_of_int))
            } else {
                a.clone()
            }
        }
        SExp::Cons(l, a, b) => {
            let new_a = humanize(a.clone());
            let new_b = humanize(b.clone());
            Rc::new(SExp::Cons(l.clone(), new_a, new_b))
        }
        _ => a.clone(),
    }
}

#[cfg(feature = "debug-print")]
fn is_print_request(a: &SExp) -> Option<(Srcloc, Rc<SExp>)> {
    if let SExp::Cons(l, f, r) = a {
        if &print_atom() == f.borrow() {
            return Some((l.clone(), humanize(r.clone())));
        }
    }

    None
}

fn jit_generate_tail(jit_mut: &mut JitMap, jitted: &mut ClvmShortCircuit, num_args: &mut usize, tail: Rc<SExp>) {
    if let SExp::Cons(_, here, farther_tail) = tail.borrow() {
        jit_generate_tail(jit_mut, jitted, num_args, farther_tail.clone());

        *num_args += 1;
        jit_sexp(jit_mut, jitted, here.clone());
    } else if truthy(tail.clone()) {
        jitted.instructions.push(ClvmLinearInstruction::Error(RunFailure::RunErr(tail.loc(), "improper tail in operator".to_string())));
    }
}

fn is_quote_atom(expr: Rc<SExp>) -> bool {
    *expr == SExp::Atom(expr.loc(), vec![1])
}

fn is_apply_atom(expr: Rc<SExp>, tail: Rc<SExp>) -> Result<(Rc<SExp>, Rc<SExp>), ()> {
    if let NodeSel::Cons(h, First::Here(t)) =
        NodeSel::Cons(ThisNode::Here, First::Here(ThisNode::Here)).select_nodes(tail).map_err(|_: (Srcloc, String)| ())?
    {
        if *expr == SExp::Atom(expr.loc(), vec![2]) {
            return Ok((h.clone(), t.clone()));
        }
    }

    Err(())
}

fn jit_sexp(jit_mut: &mut JitMap, jitted: &mut ClvmShortCircuit, expr: Rc<SExp>) {
    if let SExp::Cons(_, ahead, atail) = expr.borrow() {
        jit_generate(jit_mut, jitted, ahead.clone(), atail.clone());
    } else if let SExp::Atom(_, v) = expr.atomize() { // Path or nil-like
        if v.is_empty() {
            jitted.instructions.push(ClvmLinearInstruction::Literal(expr.clone()));
        } else {
            jitted.instructions.push(ClvmLinearInstruction::Path(v.clone()));
        }
    } else {
        jitted.instructions.push(ClvmLinearInstruction::Literal(expr.clone()));
    }
}

fn jit_generate(jit_mut: &mut JitMap, jitted: &mut ClvmShortCircuit, head: Rc<SExp>, tail: Rc<SExp>) {
    if is_quote_atom(head.clone()) {
        jitted.instructions.push(ClvmLinearInstruction::Literal(tail.clone()));
    } else if let Ok((apply_code, apply_env)) = is_apply_atom(head.clone(), tail.clone()) {
        jit_sexp(jit_mut, jitted, apply_env);
        jit_sexp(jit_mut, jitted, apply_code);

        jitted.instructions.push(ClvmLinearInstruction::Swap);
        jitted.instructions.push(ClvmLinearInstruction::PushEnv);
        jitted.instructions.push(ClvmLinearInstruction::Apply);
        jitted.instructions.push(ClvmLinearInstruction::PopEnv);
    } else {
        let mut num_args = 0;

        jit_generate_tail(jit_mut, jitted, &mut num_args, tail.clone());

        if let SExp::Atom(_, v) = head.atomize().borrow() {
            jitted.instructions.push(ClvmLinearInstruction::Operator(v.clone(), num_args));
        } else {
            jitted.instructions.push(ClvmLinearInstruction::Error(RunFailure::RunErr(tail.loc(), "improper operator".to_string())));
}
    }
}

impl PrimOverride for CldbRun {
    fn try_handle(
        &self,
        head: Rc<SExp>,
        context: Rc<SExp>,
        tail: Rc<SExp>,
    ) -> Result<Option<Rc<SExp>>, RunFailure> {
        if !self.perform_jit {
            return Ok(None);
        }

        let allocator: &mut Allocator = &mut self.allocator.borrow_mut();
        let jit_mut: &mut JitMap = &mut self.stored_jit.borrow_mut();
        let jit_stored: &mut ConvMap = &mut self.stored_conversions.borrow_mut();

        if let Some(l) = tail.proper_list() {
            let mut recombined_tail = Rc::new(SExp::Nil(tail.loc()));
            let quote_atom = Rc::new(SExp::Atom(tail.loc(), vec![1]));
            for item in l.iter().rev() {
                let quoted_item = Rc::new(SExp::Cons(
                    item.loc(),
                    quote_atom.clone(),
                    Rc::new(item.clone())
                ));
                recombined_tail = Rc::new(SExp::Cons(
                    item.loc(),
                    quoted_item,
                    recombined_tail
                ));
            }
            let res = self.jit_compile_and_run(allocator, jit_mut, jit_stored, head, context, recombined_tail);
            res.map(Some)
        } else {
            Ok(None)
        }
    }
}

impl CldbRun {
    /// Create a new CldbRun for running a program.
    /// Takes an CldbEnvironment and a prepared RunStep, which will be stepped
    /// through.  The CldbEnvironment specifies places where the consumer has the
    /// ability to examine the run step and possibly alter the result of execution.
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
            perform_jit: false,
            allocator: RefCell::new(Allocator::new()),
            stored_jit: RefCell::new(HashMap::new()),
            stored_conversions: RefCell::new(HashMap::new()),
        }
    }

    pub fn set_use_jit(&mut self, use_jit: bool) {
        self.perform_jit = use_jit;
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
                Some(self),
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
                    if let Ok(n) = x.get_number() {
                        self.outputs_to_step.insert(
                            n,
                            PriorResult {
                                reference: self.row,
                                // value: x.clone(), // for future
                            },
                        );
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
                if let Ok(v) = sexp.get_number() {
                    if v == 11_u32.to_bigint().unwrap() {
                        // Build source tree for hashes.
                        let arg_associations =
                            get_arg_associations(&self.outputs_to_step, a.clone());
                        let args = format_arg_inputs(&arg_associations);
                        self.to_print.insert("Argument-Refs".to_string(), args);
                    } else if v == 34_u32.to_bigint().unwrap() {
                        #[cfg(feature = "debug-print")]
                        // Handle diagnostic output.
                        if let Some((loc, outputs)) = is_print_request(a) {
                            self.to_print
                                .insert("Print-Location".to_string(), loc.to_string());
                            self.to_print
                                .insert("Print".to_string(), outputs.to_string());
                        }
                    }
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

    pub fn current_step(&self) -> RunStep {
        self.step.clone()
    }

    fn cache_sexp_conversion(&self, allocator: &mut Allocator, jit_stored: &mut ConvMap, value: Rc<SExp>) -> Result<NodePtr, RunFailure> {
        let ptr = ConvKey::SExpPtr(Rc::as_ptr(&value) as u64);
        if let Some((_, res)) = jit_stored.get(&ptr) {
            return Ok(*res);
        }

        if let SExp::Cons(_, a, b) = value.borrow() {
            let cached_a = self.cache_sexp_conversion(allocator, jit_stored, a.clone())?;
            let cached_b = self.cache_sexp_conversion(allocator, jit_stored, b.clone())?;
            let new_cons = allocator.new_pair(cached_a, cached_b).map_err(|_| RunFailure::RunErr(value.loc(), "Failed to alloc cons".to_string()))?;
            let pair = (value.clone(), new_cons);
            jit_stored.insert(ConvKey::NodePtr(new_cons), pair.clone());
            jit_stored.insert(ptr, pair);
            Ok(new_cons)
        } else {
            let converted_val = convert_to_clvm_rs(allocator, value.clone())?;
            let pair = (value.clone(), converted_val);
            jit_stored.insert(ConvKey::NodePtr(converted_val), pair.clone());
            jit_stored.insert(ptr, pair);
            Ok(converted_val)
        }
    }

    fn cache_node_conversion(&self, allocator: &mut Allocator, jit_stored: &mut ConvMap, loc: Srcloc, value: NodePtr) -> Result<Rc<SExp>, RunFailure> {
        if let Some((res, _)) = jit_stored.get(&ConvKey::NodePtr(value)) {
            return Ok(res.clone());
        }

        let converted =
            convert_from_clvm_rs(allocator, loc, value)?;

            // if let allocator::SExp::Pair(a, b) = allocator.sexp(value) {
            //     let back_a = self.cache_node_conversion(allocator, jit_stored, loc.clone(), a)?;
            //     let back_b = self.cache_node_conversion(allocator, jit_stored, loc.clone(), b)?;
            //     Rc::new(SExp::Cons(loc.clone(), back_a, back_b))
            // } else {
            //     convert_from_clvm_rs(allocator, loc, value)?
            // };

        let new_ptr = ConvKey::SExpPtr(Rc::as_ptr(&converted) as u64);
        jit_stored.insert(new_ptr, (converted.clone(), value));
        jit_stored.insert(ConvKey::NodePtr(value), (converted.clone(), value));
        Ok(converted)
    }

    fn jit_apply_op(&self, allocator: &mut Allocator, jit_mut: &mut JitMap, jit_stored: &mut ConvMap, runner: Rc<dyn TRunProgram>, end_env: Srcloc, head: Rc<SExp>, rest: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
        let wrapped_args = Rc::new(SExp::Cons(
            end_env.clone(),
            Rc::new(SExp::Nil(end_env.clone())),
            rest.clone(),
        ));
        let application = Rc::new(SExp::Cons(
            end_env,
            head.clone(),
            generate_argument_refs(5_i32.to_bigint().unwrap(), rest),
        ));

        let converted_app = self.cache_sexp_conversion(allocator, jit_stored, application.clone())?;
        let converted_args = self.cache_sexp_conversion(allocator, jit_stored, wrapped_args.clone())?;

        let out_node =
            runner
            .run_program(allocator, converted_app, converted_args, None)
            .map_err(|e| {
                RunFailure::RunErr(
                    head.loc(),
                    format!("{} in {application} {wrapped_args}", e.1),
                )
            })?;

        // convert_from_clvm_rs(allocator, head.loc(), out_node.1)
        self.cache_node_conversion(allocator, jit_stored, head.loc(), out_node.1)
    }

    fn jit_run(&self, allocator: &mut Allocator, jit_mut: &mut JitMap, jit_stored: &mut ConvMap, jit_code: &ClvmShortCircuit, env: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
        let mut val_stack: Vec<Rc<SExp>> = Vec::new();
        let mut env_stack = vec![env.clone()];

        for inst in jit_code.instructions.iter() {
            let end_env = env_stack[env_stack.len()-1].clone();
            match inst {
                ClvmLinearInstruction::Swap => {
                    let vslen = val_stack.len();
                    if vslen < 2 {
                        // XXX fix loc.
                        return Err(RunFailure::RunErr(end_env.loc(), format!("{inst:?} {end_env}")));
                    }

                    let tmp = val_stack[vslen-1].clone();
                    val_stack[vslen-1] = val_stack[vslen-2].clone();
                    val_stack[vslen-2] = tmp;
                },
                ClvmLinearInstruction::Path(v) => {
                    let the_path = number_from_u8(&v);
                    val_stack.push(choose_path(
                        end_env.loc(),
                        the_path.clone(),
                        the_path,
                        end_env.clone(),
                        end_env
                    )?);
                },
                ClvmLinearInstruction::Literal(v) => {
                    val_stack.push(v.clone());
                },
                ClvmLinearInstruction::Operator(o, n) => {
                    let mut rest = Rc::new(SExp::Nil(end_env.loc()));
                    for arg in val_stack.iter().rev().take(*n).rev().cloned() {
                        rest = Rc::new(SExp::Cons(
                            end_env.loc(),
                            arg.clone(),
                            rest.clone()
                        ));
                    }
                    val_stack.truncate(val_stack.len() - n);
                    let head = Rc::new(SExp::Atom(env.loc(), o.clone()));

                    if o == &[34] {
                        // Handle diagnostic output.
                        if let Some((loc, outputs)) = is_print_request(rest.borrow()) {
                            eprintln!("Print: {outputs}");
                        }
                    }

                    val_stack.push(self.jit_apply_op(
                        allocator,
                        jit_mut,
                        jit_stored,
                        self.runner.clone(),
                        end_env.loc(),
                        head,
                        rest
                    )?);
                },
                ClvmLinearInstruction::PushEnv => {
                    if let Some(v) = val_stack.pop() {
                        env_stack.push(v.clone());
                    } else {
                        return Err(RunFailure::RunErr(env.loc(), "empty val stack in pushenv".to_string()));
                    }
                },
                ClvmLinearInstruction::PopEnv => {
                    env_stack.pop();
                }
                ClvmLinearInstruction::Apply => {
                    if let Some(program) = val_stack.pop() {
                        let key_expr = Rc::as_ptr(&program);
                        let key = (0, key_expr as u64);
                        if let SExp::Cons(_, head, tail) = program.borrow() {
                            val_stack.push(self.jit_compile_and_run(allocator, jit_mut, jit_stored, head.clone(), end_env.clone(), tail.clone())?);
                        } else if let Some(res) = jit_mut.get(&key).cloned() {
                            val_stack.push(self.jit_run(allocator, jit_mut, jit_stored, &res, end_env)?);
                        } else {
                            let mut new_jit = ClvmShortCircuit::default();
                            jit_sexp(jit_mut, &mut new_jit, program);
                            jit_mut.insert(key, new_jit.clone());
                            val_stack.push(self.jit_run(allocator, jit_mut, jit_stored, &new_jit, end_env)?);
                        }
                    } else {
                        return Err(RunFailure::RunErr(env.loc(), "empty val stack in apply".to_string()));
                    }
                },
                _ => todo!()
            }
        }

        assert_eq!(val_stack.len(), 1);
        if let Some(v) = val_stack.pop() {
            return Ok(v.clone());
        }

        Err(RunFailure::RunErr(env.loc(), "val stack empty".to_string()))
    }

    fn jit_compile_and_run(&self, allocator: &mut Allocator, jit_mut: &mut JitMap, jit_stored: &mut ConvMap, head: Rc<SExp>, context: Rc<SExp>, tail: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
        let head_index = Rc::as_ptr(&head) as u64;
        let tail_index = Rc::as_ptr(&context) as u64;
        let idx = (head_index, tail_index);

        if let Some(res) = jit_mut.get(&idx).cloned() {
            // There's a previous just expression.
            return self.jit_run(allocator, jit_mut, jit_stored, &res, context);
        }

        let mut jit_code = ClvmShortCircuit::default();
        jit_generate(jit_mut, &mut jit_code, head, tail);
        jit_mut.insert(idx, jit_code.clone());
        let res = self.jit_run(allocator, jit_mut, jit_stored, &jit_code, context)?;
        Ok(res)
    }
}

/// A simple implementation of CldbEnvironment that does not override anything.
pub struct CldbNoOverride {}

impl CldbRunnable for CldbNoOverride {
    fn replace_step(&self, _step: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        None
    }
}

impl CldbNoOverride {
    pub fn new() -> Self {
        CldbNoOverride {}
    }

    pub fn new_symbols(_symbol_table: HashMap<String, String>) -> Self {
        CldbNoOverride {}
    }
}

impl Default for CldbNoOverride {
    fn default() -> Self {
        CldbNoOverride::new()
    }
}

/// Allow the caller to examine environment and return an expression that
/// will be quoted, used in conjunction with CldbEnvironment.
pub trait CldbSingleBespokeOverride {
    fn get_override(&self, env: Rc<SExp>) -> Result<Rc<SExp>, RunFailure>;
}

/// Provides a collection of overrides to be used with CldbEnvironment and
/// CldbRun to support use cases like examining the arguments given to a
/// specific function while CLVM code is executing or to mock functions in
/// a CLVM program.
pub struct CldbOverrideBespokeCode {
    symbol_table: HashMap<String, String>,
    overrides: HashMap<String, Box<dyn CldbSingleBespokeOverride>>,
}

impl CldbOverrideBespokeCode {
    /// Given the symbol table of a compiled CLVM program and a hashmap from
    /// function names to override specifications, provie a ClvmEnvironment that
    /// overrides the targeted functions with the given overrides, which are
    /// objects the consumer implements CldbSingleBespokeOverride for.
    ///
    /// These can do whatever the user likes, from inspecting the arguments
    /// to replacing the result.
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
        let fun_hash = clvm::sha256tree(f);
        let fun_hash_str = Bytes::new(Some(BytesFromType::Raw(fun_hash))).hex();

        self.symbol_table
            .get(&fun_hash_str)
            .and_then(|funname| self.overrides.get(funname))
            .map(|override_fn| {
                override_fn
                    .get_override(args.clone())
                    .map(|new_exp| RunStep::OpResult(sexp.loc(), new_exp, p.clone()))
            })
    }
}

impl CldbRunnable for CldbOverrideBespokeCode {
    fn replace_step(&self, step: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        match step {
            RunStep::Op(sexp, context, arguments, None, parent) => match sexp.borrow() {
                SExp::Integer(_, i) => {
                    if *i == 2_u32.to_bigint().unwrap() {
                        match arguments.borrow() {
                            SExp::Cons(_, first, args) => self
                                .find_function_and_override_if_needed(
                                    sexp.clone(),
                                    context.clone(),
                                    first.clone(),
                                    args.clone(),
                                    parent.clone(),
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

/// A small collection of information about the running program, including the
/// name of the source file and the lines of the program.  When present, this
/// allows names to be picked out of the source base and locations to be accurate.
///
/// Also provides a CldbRunnable that specifies the user's overrides.
pub struct CldbRunEnv {
    input_file: Option<String>,
    program_lines: Rc<Vec<String>>,
    overrides: Box<dyn CldbRunnable>,
}

impl CldbRunEnv {
    /// Make a new CldbRunEnv given useful information about the program being
    /// run.
    pub fn new(
        input_file: Option<String>,
        program_lines: Rc<Vec<String>>,
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
        let use_col = use_line.and(if l.col < 1 { None } else { Some(l.col - 1) });
        let end_col = use_col.map(|c| l.until.as_ref().map(|u| u.col - 1).unwrap_or_else(|| c + 1));
        use_line
            .and_then(|use_line| {
                use_col.and_then(|use_col| end_col.map(|end_col| (use_line, use_col, end_col)))
            })
            .and_then(|coords| {
                let use_line = coords.0;
                let use_col = coords.1;
                let end_col = coords.2;

                if use_line >= self.program_lines.len() {
                    None
                } else {
                    let line_text = self.program_lines[use_line].to_string();
                    if use_col >= line_text.len() {
                        None
                    } else {
                        Some(
                            line_text
                                .chars()
                                .take(end_col)
                                .skip(use_col)
                                .collect::<String>(),
                        )
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
        if let SExp::Integer(_, i) = s {
            if *i == 2_i32.to_bigint().unwrap() {
                if_true(collector);
                return;
            }
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
            &|context_result| {
                if let Some(a) = &args {
                    context_result.insert("Arguments".to_string(), a.to_string());
                }
            },
        );
    }

    fn add_function(&self, s: &SExp, context_result: &mut BTreeMap<String, String>) {
        self.whether_is_apply(
            s,
            context_result,
            &|_context_result| {},
            &|context_result| {
                if let Some(name) = self.extract_text(&s.loc()) {
                    if Some(s.loc().file.to_string()) == self.input_file.clone() {
                        context_result.insert("Function".to_string(), name);
                    }
                }
            },
        );
    }

    fn get_override(&self, s: &RunStep) -> Option<Result<RunStep, RunFailure>> {
        self.overrides.replace_step(s)
    }
}

fn hex_to_modern_sexp_inner(
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

/// A function which, given hex input, produces equivalent SExp.
/// All produced SExp have the location given in loc.
pub fn hex_to_modern_sexp(
    allocator: &mut Allocator,
    symbol_table: &HashMap<String, String>,
    loc: Srcloc,
    input_program: &str,
) -> Result<Rc<SExp>, RunFailure> {
    let input_serialized = Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(
        input_program.to_string(),
    )))
    .map_err(|e| RunFailure::RunErr(loc.clone(), e.to_string()))?;

    let mut stream = Stream::new(Some(input_serialized));
    let sexp = sexp_from_stream(allocator, &mut stream, Box::new(SimpleCreateCLVMObject {}))
        .map(|x| x.1)
        .map_err(|_| RunFailure::RunErr(loc.clone(), "Bad conversion from hex".to_string()))?;

    hex_to_modern_sexp_inner(allocator, symbol_table, loc.clone(), sexp).map_err(|_| {
        RunFailure::RunErr(loc, "Failed to convert from classic to modern".to_string())
    })
}
