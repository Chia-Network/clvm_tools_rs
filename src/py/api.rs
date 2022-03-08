use pyo3::exceptions::PyException;
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

use crate::classic::clvm_tools::clvmc;

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

#[pymodule]
fn clvm_tools_rs(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(compile_clvm, m)?)?;
    Ok(())
}
