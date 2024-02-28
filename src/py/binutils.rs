use std::collections::HashMap;

use crate::classic::clvm::__type_compatibility__::t;
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm::sexp::{sexp_as_bin, First, NodeSel, Rest, SelectNode, ThisNode};
use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use pyo3::prelude::*;
use pyo3::exceptions::PyException;
use pyo3::types::{PyBytes,PyTuple};

use crate::classic::clvm_tools::binutils;
use crate::classic::clvm_tools::ir::reader::read_ir;

create_exception!(mymodule, ConvError, PyException);

fn convert_to_external(allocator: &Allocator, cons: &PyAny, from_bytes: &PyAny, node: NodePtr) -> PyResult<PyObject> {
    let mut stack: Vec<NodePtr> = vec![node];
    let mut finished = HashMap::new();
    let mut conv_map = HashMap::new();

    while let Some(n) = stack.pop() {
        match allocator.sexp(n) {
            SExp::Pair(a,b) => {
                stack.push(a);
                stack.push(b);
                conv_map.insert(n, (a, b));
            }
            SExp::Atom => {
                let converted: PyObject =
                    Python::with_gil(|py| {
                        let bytes = PyBytes::new(py, allocator.atom(n));
                        let args = PyTuple::new(py, &[bytes]);
                        from_bytes.call1(args)
                    })?.into();
                finished.insert(n, converted);
            }
        }
    }

    let check_cvt_map = |conv_map: &HashMap<NodePtr, (NodePtr, NodePtr)>, n| -> Option<(NodePtr, NodePtr)> {
        if let Some(res) = conv_map.get(&n) {
            return Some(res.clone());
        }

        None
    };

    // Convert conses.
    stack.push(node);
    while let Some(n) = stack.pop() {
        if let Some(res) = finished.get(&n) {
            continue;
        }
        if let Some((a, b)) = check_cvt_map(&conv_map, n) {
            if let (Some(a), Some(b)) = (finished.get(&a), finished.get(&b)) {
                let result: PyObject = Python::with_gil(|py| {
                    let args = PyTuple::new(py, &[&a, &b]);
                    cons.call1(args)
                })?.into();
                conv_map.remove(&n);
                finished.insert(n, result);
                continue;
            }

            stack.push(n);
            stack.push(a);
            stack.push(b);
        }
    }

    if let Some(res) = finished.get(&node) {
        return Ok(res.clone());
    } else {
        return Err(ConvError::new_err("error converting assembled value"));
    }
}

#[pyfunction]
pub fn assemble_generic(cons: &PyAny, from_bytes: &PyAny, args: String) -> PyResult<PyObject>
{
    let mut allocator = Allocator::new();
    let assembled = binutils::assemble(&mut allocator, &args)
        .map_err(|e| ConvError::new_err(e.to_string()))?;
    convert_to_external(&allocator, cons, from_bytes, assembled)
}

pub fn create_binutils_module(py: Python) -> PyResult<&'_ PyModule> {
    let m = PyModule::new(py, "binutils")?;
    m.add_function(wrap_pyfunction!(assemble_generic, m)?)?;
    Ok(m)
}
