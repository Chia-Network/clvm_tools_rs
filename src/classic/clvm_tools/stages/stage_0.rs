use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::cost::Cost;
use clvm_rs::f_table::{
    f_lookup_for_hashmap,
    FLookup
};
use clvm_rs::more_ops::op_unknown;
use clvm_rs::reduction::{
    EvalErr,
    Reduction,
    Response
};

use clvm_rs::run_program::{
    OperatorHandler,
    PreEval,
    run_program
};

pub type TOperatorDict = HashMap<String, Vec<u8>>;

pub struct OpQuote { }

impl<'a> OperatorHandler for OpQuote {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        return Ok(Reduction(1, sexp));
    }
}

pub struct OpRouter {
    routes: HashMap<Vec<u8>, Rc<dyn OperatorHandler>>,
    f_lookup: FLookup,
    strict: bool,
}

impl<'a> OperatorHandler for OpRouter {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        match allocator.sexp(op) {
            SExp::Atom(b) => {
                let buf = &allocator.buf(&b).to_vec();
                match self.routes.get(buf) {
                    Some(handler) => {
                        return handler.op(allocator, op, sexp, max_cost);
                    },
                    _ => {
                        if buf.len() == 1 {
                            if let Some(f) = self.f_lookup[buf[0] as usize] {
                                return f(allocator, sexp, max_cost);
                            }
                        }
                        if self.strict {
                            return Err(EvalErr(op, "unimplemented operator".to_string()))
                        } else {
                            op_unknown(allocator, op, sexp, max_cost)
                        }
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

impl DefaultProgramRunner {
    pub fn new() -> Self {
        return DefaultProgramRunner {
            apply_kw_vec: vec!(2 as u8),
            quote_kw_vec: vec!(1 as u8),
        };
    }
}

impl<'a> OperatorHandler for DefaultProgramRunner {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, args: NodePtr, max_cost: Cost) -> Response {
        return Err(EvalErr(allocator.null(), "lol".to_string()));
    }
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

        let mut routes : HashMap<Vec<u8>, Rc<dyn OperatorHandler>> = HashMap::new();
        routes.insert(vec!(1), Rc::new(OpQuote {}));

        return OpRouter {
            routes: routes,
            f_lookup: f_lookup,
            strict: true,
        };
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

        let op_router = OpRouter::new();
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
