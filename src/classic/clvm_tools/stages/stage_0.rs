use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::cost::Cost;
use clvm_rs::f_table::{f_lookup_for_hashmap, FLookup};
use clvm_rs::more_ops::op_unknown;
use clvm_rs::operator_handler::OperatorHandler;
use clvm_rs::reduction::{EvalErr, Reduction, Response};

use clvm_rs::run_program::{run_program, PreEval};

pub type TOperatorDict = HashMap<String, Vec<u8>>;

pub struct OpQuote {}

impl OperatorHandler for OpQuote {
    fn op(
        &self,
        _allocator: &mut Allocator,
        _op: NodePtr,
        sexp: NodePtr,
        _max_cost: Cost,
    ) -> Response {
        Ok(Reduction(1, sexp))
    }
}

#[derive(Clone)]
pub struct OpRouter {
    routes: HashMap<Vec<u8>, Rc<dyn OperatorHandler>>,
    f_lookup: FLookup,
    strict: bool,
}

impl OpRouter {
    fn new() -> Self {
        let mut opcode_lookup_by_name = HashMap::<String, Vec<u8>>::new();
        for (v, s) in [
            (3, "op_if"),
            (4, "op_cons"),
            (5, "op_first"),
            (6, "op_rest"),
            (7, "op_listp"),
            (8, "op_raise"),
            (9, "op_eq"),
            (10, "op_gr_bytes"),
            (11, "op_sha256"),
            (12, "op_substr"),
            (13, "op_strlen"),
            (14, "op_concat"),
            (16, "op_add"),
            (17, "op_subtract"),
            (18, "op_multiply"),
            (19, "op_div"),
            (20, "op_divmod"),
            (21, "op_gr"),
            (22, "op_ash"),
            (23, "op_lsh"),
            (24, "op_logand"),
            (25, "op_logior"),
            (26, "op_logxor"),
            (27, "op_lognot"),
            (29, "op_point_add"),
            (30, "op_pubkey_for_exp"),
            (32, "op_not"),
            (33, "op_any"),
            (34, "op_all"),
            (36, "op_softfork"),
        ]
        .iter()
        {
            let v: Vec<u8> = vec![*v as u8];
            opcode_lookup_by_name.insert(s.to_string(), v);
        }

        let f_lookup = f_lookup_for_hashmap(opcode_lookup_by_name);

        let mut routes: HashMap<Vec<u8>, Rc<dyn OperatorHandler>> = HashMap::new();
        routes.insert(vec![1], Rc::new(OpQuote {}));

        OpRouter {
            routes,
            f_lookup,
            strict: true,
        }
    }

    pub fn add_handler(&mut self, op: &Vec<u8>, handler: Rc<dyn OperatorHandler>) {
        self.routes.insert(op.to_vec(), handler);
    }

    pub fn showtable(&self) -> String {
        let keys: Vec<Vec<u8>> = self.routes.keys().map(|v| v.to_vec()).collect();
        format!("{:?}", keys)
    }
}

impl<'a> OperatorHandler for OpRouter {
    fn op(
        &self,
        allocator: &mut Allocator,
        op: NodePtr,
        sexp: NodePtr,
        max_cost: Cost,
    ) -> Response {
        match allocator.sexp(op) {
            SExp::Atom(b) => {
                let buf = &allocator.buf(&b).to_vec();
                match self.routes.get(buf) {
                    Some(handler) => handler.op(allocator, op, sexp, max_cost),
                    _ => {
                        if buf.len() == 1 {
                            if let Some(f) = self.f_lookup[buf[0] as usize] {
                                return f(allocator, sexp, max_cost);
                            }
                        }
                        if self.strict {
                            Err(EvalErr(op, "unimplemented operator".to_string()))
                        } else {
                            op_unknown(allocator, op, sexp, max_cost)
                        }
                    }
                }
            }
            _ => Err(EvalErr(op, "unknown pair operator".to_string())),
        }
    }
}

pub struct RunProgramOption {
    pub operator_lookup: Option<TOperatorDict>,
    pub max_cost: Option<Cost>,
    pub pre_eval_f: Option<PreEval>,
    pub strict: bool,
}

pub trait TRunProgram {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response;
}

#[derive(Clone)]
pub struct DefaultProgramRunner {
    pub router: OpRouter,
    quote_kw_vec: Vec<u8>,
    apply_kw_vec: Vec<u8>,
}

impl DefaultProgramRunner {
    pub fn new() -> Self {
        DefaultProgramRunner {
            router: OpRouter::new(),
            apply_kw_vec: vec![2 as u8],
            quote_kw_vec: vec![1 as u8],
        }
    }

    pub fn add_handler(&mut self, op: &Vec<u8>, handler: Rc<dyn OperatorHandler>) {
        self.router.add_handler(&op.to_vec(), handler);
    }
}

impl TRunProgram for DefaultProgramRunner {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response {
        let mut max_cost = 0;

        match &option {
            Some(o) => match o.max_cost {
                Some(c) => {
                    max_cost = c;
                }
                _ => {}
            },
            _ => {}
        }

        run_program(
            allocator,
            &self.quote_kw_vec,
            &self.apply_kw_vec,
            &self.router,
            program,
            args,
            max_cost,
            option.and_then(|o| o.pre_eval_f),
        )
    }
}
