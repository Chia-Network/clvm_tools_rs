use pyo3::prelude::*;
use pyo3::create_exception;
use pyo3::exceptions::PyException;
use pyo3::wrap_pyfunction;

use crate::classic::clvm_tools::clvmc;

#[pyfunction]
fn compile_clvm(input_path: String, output_path: String, search_paths: Vec<String>) -> PyResult<String> {
    clvmc::compile_clvm(&input_path, &output_path, &search_paths).map_err(|s| {
        PyException::new_err(s)
    })
}

#[pymodule]
fn clvm_tools_rs(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(compile_clvm, m)?)?;
    Ok(())
}
