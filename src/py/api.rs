use pyo3::exceptions::PyException;
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::clvmc;
use crate::classic::clvm_tools::cmds::{OpcConversion, TConversion};

// Thanks: https://www.reddit.com/r/rust/comments/bkkpkz/pkgversion_access_your_crates_version_number_as/
#[pyfunction]
fn get_version() -> PyResult<String> {
    Ok(env!("CARGO_PKG_VERSION").to_string())
}

#[pyfunction(arg3 = "[]")]
fn compile_clvm(
    input_path: &PyAny,
    output_path: String,
    search_paths: Vec<String>,
) -> PyResult<String> {
    let has_atom = input_path.hasattr("atom")?;
    let has_pair = input_path.hasattr("pair")?;

    let real_input_path = if has_atom {
        input_path.getattr("atom").and_then(|x| x.str())
    } else if has_pair {
        input_path
            .getattr("pair")
            .and_then(|x| x.get_item(0))
            .and_then(|x| x.str())
    } else {
        input_path.extract()
    }?;

    let mut path_string = real_input_path.to_string();

    if !std::path::Path::new(&path_string).exists() && !path_string.ends_with(".clvm") {
        path_string = path_string + ".clvm";
    };

    clvmc::compile_clvm(&path_string, &output_path, &search_paths)
        .map_err(|s| PyException::new_err(s))
}

#[pyfunction]
fn assemble(input_text: String) -> PyResult<String> {
    let conv = OpcConversion {};
    let mut allocator = Allocator::new();
    conv.invoke(&mut allocator, &input_text)
        .map(|r| r.rest().clone())
        .map_err(|e| PyException::new_err(e))
}

#[pymodule]
fn clvm_tools_rs(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(compile_clvm, m)?)?;
    m.add_function(wrap_pyfunction!(get_version, m)?)?;
    m.add_function(wrap_pyfunction!(assemble, m)?)?;
    Ok(())
}
