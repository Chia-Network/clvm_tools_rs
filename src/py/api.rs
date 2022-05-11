use pyo3::exceptions::PyException;
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyString};
use pyo3::wrap_pyfunction;

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::thread;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::clvmc;
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::cldb::{hex_to_modern_sexp, CldbRun, CldbRunEnv};
use crate::compiler::clvm::start_step;
use crate::compiler::prims;
use crate::compiler::srcloc::Srcloc;

create_exception!(mymodule, CldbError, PyException);

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

#[pyclass]
struct PythonRunStep {
    ended: bool,

    tx: Sender<bool>,
    rx: Receiver<(bool, Option<BTreeMap<String, String>>)>,
}

#[pymethods]
impl PythonRunStep {
    fn is_ended(&self) -> PyResult<bool> {
        return Ok(self.ended);
    }

    fn drop(&mut self) {
        // If we can't send here then there's probably nothing we can do anyway.
        let _ = self.tx.send(true);
    }

    fn step(&mut self) -> PyResult<Option<PyObject>> {
        if self.ended {
            return Ok(None);
        }

        // Let the runner know we want another step.
        self.tx
            .send(false)
            .map_err(|e| CldbError::new_err("error sending to service thread"))?;

        // Receive the step result.
        let res = self
            .rx
            .recv()
            .map_err(|e| CldbError::new_err("error receiving from service thread"))?;

        if res.0 {
            self.ended = true;
        }

        // Return a dict if one was returned.
        let dict_result = res.1.map(|m| {
            Python::with_gil(|py| {
                let dict = PyDict::new(py);
                for (k, v) in m.iter() {
                    let _ = dict.set_item(PyString::new(py, k), PyString::new(py, v));
                }
                dict.to_object(py)
            })
        });
        Ok(dict_result)
    }
}

#[pyfunction]
fn start_clvm_program(
    hex_prog: String,
    hex_args: String,
    symbol_table: Option<HashMap<String, String>>,
) -> PyResult<PythonRunStep> {
    let (command_tx, command_rx) = mpsc::channel();
    let (result_tx, result_rx) = mpsc::channel();

    let t = thread::spawn(move || {
        let mut allocator = Allocator::new();
        let runner = Rc::new(DefaultProgramRunner::new());
        let mut prim_map = HashMap::new();
        let cmd_input = command_rx;
        let result_output = result_tx;
        let prog_srcloc = Srcloc::start(&"*program*".to_string());
        let args_srcloc = Srcloc::start(&"*args*".to_string());

        for p in prims::prims().iter() {
            prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
        }

        let program = match hex_to_modern_sexp(
            &mut allocator,
            &symbol_table.unwrap_or_else(|| HashMap::new()),
            prog_srcloc.clone(),
            &hex_prog,
        ) {
            Ok(v) => v,
            Err(_) => {
                return;
            }
        };
        let args = match hex_to_modern_sexp(
            &mut allocator,
            &HashMap::new(),
            args_srcloc.clone(),
            &hex_args,
        ) {
            Ok(v) => v,
            Err(_) => {
                return;
            }
        };

        let step = start_step(program.clone(), args.clone());
        let cldbenv = CldbRunEnv::new(None, vec![]);
        let mut cldbrun = CldbRun::new(runner, Rc::new(prim_map), Box::new(cldbenv), step);
        loop {
            match cmd_input.recv() {
                Ok(end_run) => {
                    if end_run || cldbrun.is_ended() {
                        let _ = result_output.send((true, None));
                        return;
                    }

                    let result = cldbrun.step(&mut allocator);
                    let is_ended = cldbrun.is_ended();
                    match result_output.send((is_ended, result)) {
                        Ok(_) => {}
                        Err(_) => {
                            return;
                        }
                    }
                }
                Err(_) => {
                    let _ = result_output.send((true, None));
                    return;
                }
            }
        }
    });

    Ok(PythonRunStep {
        ended: false,
        tx: command_tx,
        rx: result_rx,
    })
}

#[pymodule]
fn clvm_tools_rs(py: Python, m: &PyModule) -> PyResult<()> {
    m.add("CldbError", py.get_type::<CldbError>())?;
    m.add_function(wrap_pyfunction!(compile_clvm, m)?)?;
    m.add_function(wrap_pyfunction!(get_version, m)?)?;
    m.add_function(wrap_pyfunction!(start_clvm_program, m)?)?;
    m.add_class::<PythonRunStep>()?;
    Ok(())
}
