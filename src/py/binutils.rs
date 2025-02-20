use std::collections::HashMap;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use clvm_rs::allocator::{Allocator, NodePtr, SExp};

use pyo3::exceptions::PyException;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyTuple};

use crate::classic::clvm_tools::binutils;

create_exception!(mymodule, ConvError, PyException);

fn convert_to_external(
    allocator: &Allocator,
    cons: Bound<'_, PyAny>,
    from_bytes: Bound<'_, PyAny>,
    root_node: NodePtr,
) -> PyResult<PyObject> {
    let mut stack: Vec<NodePtr> = vec![root_node];
    let mut finished = HashMap::new();

    while let Some(node) = stack.last() {
        let node = *node; // To avoid borrowing issues with the stack
        match allocator.sexp(node) {
            SExp::Pair(left, right) => {
                let left_finished = finished.contains_key(&left);
                let right_finished = finished.contains_key(&right);

                if left_finished && right_finished {
                    stack.pop();

                    let result: PyObject = Python::with_gil(|py| {
                        let a = finished.get(&left).unwrap();
                        let b = finished.get(&right).unwrap();
                        let args = PyTuple::new_bound(py, [a, b]);
                        cons.call1(args)
                    })?
                    .into();

                    finished.insert(node, result);
                } else {
                    if !left_finished {
                        stack.push(left);
                    }
                    if !right_finished {
                        stack.push(right);
                    }
                }
            }
            SExp::Atom => {
                stack.pop();

                if let std::collections::hash_map::Entry::Vacant(e) = finished.entry(node) {
                    let converted: PyObject = Python::with_gil(|py| {
                        let atom = allocator.atom(node);
                        let bytes = PyBytes::new_bound(py, atom.as_ref());
                        let args = PyTuple::new_bound(py, &[bytes]);
                        from_bytes.call1(args)
                    })?
                    .into();
                    e.insert(converted);
                }
            }
        }
    }

    finished
        .get(&root_node)
        .cloned()
        .ok_or_else(|| ConvError::new_err("error converting assembled value"))
}

#[pyfunction]
pub fn assemble_generic(cons: Bound<'_, PyAny>, from_bytes: Bound<'_, PyAny>, args: String) -> PyResult<PyObject> {
    let mut allocator = Allocator::new();
    let assembled =
        binutils::assemble(&mut allocator, &args).map_err(|e| ConvError::new_err(e.to_string()))?;
    convert_to_external(&allocator, cons, from_bytes, assembled)
}

#[pyfunction]
pub fn disassemble_generic(program_bytes: Bound<'_, PyBytes>) -> PyResult<String> {
    let mut allocator = Allocator::new();
    let mut stream = Stream::new(Some(Bytes::new(Some(BytesFromType::Raw(
        program_bytes.as_bytes().to_vec(),
    )))));

    let sexp = sexp_from_stream(
        &mut allocator,
        &mut stream,
        Box::new(SimpleCreateCLVMObject {}),
    )
    .map_err(|e| ConvError::new_err(e.to_string()))?;

    let disassembled = binutils::disassemble(&allocator, sexp.1, Some(0));
    Ok(disassembled)
}

pub fn create_binutils_module(py: Python) -> PyResult<Bound<'_, PyModule>> {
    let m = PyModule::new_bound(py, "binutils")?;
    m.add_function(wrap_pyfunction!(assemble_generic, m.clone())?)?;
    m.add_function(wrap_pyfunction!(disassemble_generic, m.clone())?)?;
    Ok(m)
}
