use std::collections::HashMap;
use std::rc::Rc;

use js_sys::{Function, Reflect};
use clvmr::{Allocator, ChiaDialect, NO_UNKNOWN_OPS, ENABLE_BLS_OPS, ENABLE_SECP_OPS, run_program_with_pre_eval};
use clvmr::allocator::{NodePtr, SExp};
use clvmr::cost::Cost;
use clvmr::dialect::{Dialect, OperatorSet};
use clvmr::reduction::{EvalErr, Reduction, Response};

use wasm_bindgen::JsValue;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::{RunProgramOption, TRunProgram};
use clvm_tools_rs::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs};
use clvm_tools_rs::compiler::srcloc::Srcloc;

use crate::jsval::sexp_from_js_object;
use crate::objects::convert_to_program;

/// A dialect that allows javascript code to add operators to a clvm runner.
/// This can be used for a variety of purposes, but allows the calpoker driver
/// to run code to an exception by starting an isolated VM.
pub struct JsEnrichedCLVM {
    loc: Srcloc,
    base_dialect: Rc<dyn Dialect>,
    extra_ops: HashMap<Vec<u8>, Function>,
}

impl JsEnrichedCLVM {
    pub fn new(loc: Srcloc, extra_ops: HashMap<Vec<u8>, Function>) -> Self {
        let base_dialect = Rc::new(ChiaDialect::new(
            NO_UNKNOWN_OPS | ENABLE_BLS_OPS | ENABLE_SECP_OPS,
        ));
        JsEnrichedCLVM {
            loc,
            base_dialect,
            extra_ops,
        }
    }

    // Return the extension operator system to use while compiling based on user
    // preference.
    fn get_operators_extension(&self) -> OperatorSet {
        OperatorSet::BLS
    }
}

impl Dialect for JsEnrichedCLVM {
    fn quote_kw(&self) -> &[u8] {
        &[1]
    }

    fn apply_kw(&self) -> &[u8] {
        &[2]
    }

    fn softfork_kw(&self) -> &[u8] {
        &[36]
    }

    // The softfork operator comes with an extension argument.
    fn softfork_extension(&self, _ext: u32) -> OperatorSet { OperatorSet::BLS }

    fn op(
        &self,
        allocator: &mut Allocator,
        op: NodePtr,
        sexp: NodePtr,
        max_cost: Cost,
        _extension: OperatorSet,
    ) -> Response {
        let make_eval_obj = |allocator: &mut Allocator| -> Result<NodePtr, EvalErr> {
            allocator.new_pair(op, sexp)
        };
        let run_failure_to_response_err = |allocator: &mut Allocator, _e| -> EvalErr {
            let eval_obj =
                match make_eval_obj(allocator) {
                    Ok(eval_obj) => eval_obj,
                    Err(e) => { return e; }
                };
            EvalErr(eval_obj, format!("Failure in data conversion"))
        };

        let js_err_to_response_err = |allocator: &mut Allocator, e: JsValue| {
            let eval_obj =
                match make_eval_obj(allocator) {
                    Ok(eval_obj) => eval_obj,
                    Err(e) => { return e; }
                };

            if let Some(string_res) = e.as_string() {
                EvalErr(eval_obj, format!("Failure returned from injected operator: {string_res}"));
            }

            EvalErr(eval_obj, format!("Failure returned from injected operator"))
        };

        // Check for an operator in the operators given to us that matches the
        // hex representation of the operator name.
        let extensions_to_clvmr_during_compile = self.get_operators_extension();

        match allocator.sexp(op) {
            SExp::Atom => {
                // use of op obvious.
                let opbuf = allocator.atom(op);
                if let Some(extra_op) = self.extra_ops.get(opbuf) {
                    // Setup arguments.
                    let converted_sexp = convert_from_clvm_rs(allocator, self.loc.clone(), sexp).map_err(|e| run_failure_to_response_err(allocator, e))?;
                    let call_args = js_sys::Array::new();
                    let arg = convert_to_program(converted_sexp).map_err(|e| js_err_to_response_err(allocator, e))?;
                    call_args.set(0, arg);

                    let operator_result = Reflect::apply(
                        extra_op,
                        &JsValue::null(),
                        &call_args,
                    ).map_err(|e| js_err_to_response_err(allocator, e))?;

                    let from_javascript_program = sexp_from_js_object(self.loc.clone(), &operator_result);
                    if let Some(sexp) = from_javascript_program {
                        // Success path.
                        let as_clvm_rs = convert_to_clvm_rs(allocator, sexp).map_err(|e| run_failure_to_response_err(allocator, e))?;
                        return Ok(Reduction(1,as_clvm_rs));
                    }

                    // Error path: no possible conversion.
                    let eval_obj = make_eval_obj(allocator)?;
                    return Err(EvalErr(eval_obj, "Injected operator returned unconvertible value".to_string()));
                }

                let extensions_to_clvmr_during_compile = self.get_operators_extension();

                self.base_dialect.op(
                    allocator,
                    op,
                    sexp,
                    max_cost,
                    extensions_to_clvmr_during_compile,
                )
            }
            _ => self.base_dialect.op(
                allocator,
                op,
                sexp,
                max_cost,
                extensions_to_clvmr_during_compile,
            ),
        }
    }

    fn allow_unknown_ops(&self) -> bool {
        false
    }
}

impl TRunProgram for JsEnrichedCLVM {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response {
        let max_cost = option.as_ref().and_then(|o| o.max_cost).unwrap_or(0);
        run_program_with_pre_eval(
            allocator,
            self,
            program,
            args,
            max_cost,
            option.and_then(|o| o.pre_eval_f),
        )
    }
}
