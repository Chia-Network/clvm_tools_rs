use clvm_rs::allocator::{Allocator, NodePtr};
use clvm_rs::chia_dialect::{ChiaDialect, NO_UNKNOWN_OPS};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::Response;

use clvm_rs::run_program::{run_program_with_pre_eval, PreEval};

pub struct RunProgramOption<'inside> {
    pub max_cost: Option<Cost>,
    pub pre_eval_f: Option<&'inside mut dyn PreEval>,
    pub strict: bool,
}

pub trait TRunProgram {
    fn run_program<'inside, 'a: 'inside>(
        &'a self,
        allocator: &'a mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption<'inside>>,
    ) -> Response;
}

pub struct DefaultProgramRunner {
    dialect: ChiaDialect
}

impl DefaultProgramRunner {
    pub fn new() -> Self {
        DefaultProgramRunner {
            dialect: ChiaDialect::new(NO_UNKNOWN_OPS)
        }
    }
}

impl Default for DefaultProgramRunner {
    fn default() -> Self {
        DefaultProgramRunner::new()
    }
}

impl TRunProgram for DefaultProgramRunner {
    fn run_program<'inside, 'a: 'inside>(
        &'a self,
        allocator: &'a mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption<'inside>>,
    ) -> Response {
        let max_cost = option.as_ref().and_then(|o| o.max_cost).unwrap_or(0);
        run_program_with_pre_eval(
            allocator,
            &self.dialect,
            program,
            args,
            max_cost,
            option.and_then(|p| p.pre_eval_f)
        )
    }
}
