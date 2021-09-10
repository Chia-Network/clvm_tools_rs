use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::{
    EvalErr,
    Response
};

use clvm_rs::run_program::{
    OperatorHandler,
    PreEval,
    run_program
};

pub type TOperatorDict = HashMap<String, Vec<u8>>;

pub struct OpRouter {
    routes: HashMap<Vec<u8>, Rc<dyn OperatorHandler>>
}

impl<'a> OperatorHandler for OpRouter {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        match allocator.sexp(op) {
            SExp::Atom(b) => {
                match self.routes.get(&allocator.buf(&b).to_vec()) {
                    Some(handler) => {
                        return handler.op(allocator, op, sexp, max_cost);
                    },
                    _ => {
                        return Err(EvalErr(op, "unknown operator".to_string()));
                    }
                }
            },
            _ => {
                return Err(EvalErr(op, "unknown pair operator".to_string()));
            }
        }
    }
}

pub struct RunProgramOption {
    operator_lookup: TOperatorDict,
    max_cost: Option<Cost>,
    pre_eval_f: Option<PreEval>,
    strict: bool
}

pub trait TRunProgram<'a> {
    fn run_program(&self, allocator: &'a mut Allocator, program: NodePtr, args: NodePtr, option: Option<RunProgramOption>) -> Response;
}

pub struct DefaultProgramRunner {
    quote_kw_vec: Vec<u8>,
    apply_kw_vec: Vec<u8>
}

impl<'a> DefaultProgramRunner {
    pub fn new() -> Self {
        return DefaultProgramRunner {
            apply_kw_vec: vec!('a' as u8),
            quote_kw_vec: vec!('q' as u8),
        };
    }
}

impl<'a> OperatorHandler for DefaultProgramRunner {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, args: NodePtr, max_cost: Cost) -> Response {
        return Err(EvalErr(allocator.null(), "lol".to_string()));
    }
}

impl<'a> TRunProgram<'a> for DefaultProgramRunner {
    fn run_program(&self, allocator: &'a mut Allocator, program: NodePtr, args: NodePtr, option: Option<RunProgramOption>) -> Response {
        let mut max_cost = 0;

        match &option {
            Some(o) => {
                match o.max_cost {
                    Some(c) => { max_cost = c; },
                    _ => { }
                }
            },
            _ => { }
        }

        let op_router = OpRouter { routes: HashMap::new() };
        let res = run_program(
            allocator,
            program,
            args,
            &self.quote_kw_vec,
            &self.apply_kw_vec,
            max_cost,
            &op_router,
            option.and_then(|o| o.pre_eval_f)
        );
        return res;
    }
}
