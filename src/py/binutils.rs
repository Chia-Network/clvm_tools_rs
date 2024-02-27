use crate::classic::clvm::__type_compatibility__::t;
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm::sexp::{sexp_as_bin, First, NodeSel, Rest, SelectNode, ThisNode};
use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use pyo3::prelude::*;

use crate::classic::clvm_tools::binutils;
use crate::classic::clvm_tools::ir::reader::read_ir;

#[pyfunction]
pub fn assemble(args: String) -> PyResult<String> {
    let mut allocator = Allocator::new();
    let assembled = binutils::assemble(&mut allocator, &args)
        .map_err(|e| e.to_string())
        .map(|sexp| t(sexp, sexp_as_bin(&mut allocator, sexp).hex()))
        .unwrap();
    Ok(assembled.rest().to_string())
}

pub fn create_binutils_module(py: Python) -> PyResult<&'_ PyModule> {
    let m = PyModule::new(py, "binutils")?;
    m.add_function(wrap_pyfunction!(assemble, m)?)?;
    Ok(m)
}
