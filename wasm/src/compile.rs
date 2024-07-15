use std::collections::HashMap;
use std::convert::TryFrom;
use std::rc::Rc;

use wasm_bindgen::prelude::*;
use wasm_bindgen::{JsCast, JsValue};

use clvmr::Allocator;

use clvm_tools_rs::classic::clvm::__type_compatibility__::Stream;
use clvm_tools_rs::classic::clvm_tools::clvmc::compile_clvm_inner;
use clvm_tools_rs::compiler::BasicCompileContext;
use clvm_tools_rs::compiler::compiler::{DefaultCompilerOpts, compile_pre_forms};
use clvm_tools_rs::compiler::comptypes::{CompileErr, CompilerOpts, CompilerOutput, HasCompilerOptsDelegation};
use clvm_tools_rs::compiler::preprocessor::gather_dependencies;
use clvm_tools_rs::compiler::sexp::{decode_string, SExp};
use clvm_tools_rs::compiler::srcloc::Srcloc;

use crate::api::create_clvm_runner_err;
use crate::jsval::{js_pair, object_to_value};

fn make_compile_output(result_stream: &Stream, symbol_table: &HashMap<String, String>) -> JsValue {
    let output_hex = result_stream.get_value().hex();
    let array = js_sys::Array::new();
    array.set(
        0,
        js_pair(JsValue::from_str("hex"), JsValue::from_str(&output_hex)),
    );
    let symbol_array = js_sys::Array::new();
    for (idx, (k, v)) in symbol_table.iter().enumerate() {
        symbol_array.set(idx as u32, js_pair(JsValue::from_str(k), JsValue::from_str(v)));
    }
    let symbol_object = object_to_value(&js_sys::Object::from_entries(&symbol_array).unwrap());
    array.set(1, js_pair(JsValue::from_str("symbols"), symbol_object));
    object_to_value(&js_sys::Object::from_entries(&array).unwrap())
}

#[derive(Clone)]
pub struct JsCompilerOpts {
    opts: Rc<dyn CompilerOpts>,
    options: JsValue,
}

impl JsCompilerOpts {
    pub fn new(opts: Rc<dyn CompilerOpts>, options: JsValue) -> Self {
        JsCompilerOpts { opts, options }
    }
}

impl HasCompilerOptsDelegation for JsCompilerOpts {
    fn compiler_opts(&self) -> Rc<dyn CompilerOpts> {
        todo!()
    }

    fn update_compiler_opts<F>(
        &self,
        f: F
    ) -> Rc<dyn CompilerOpts>
    where
        F: FnOnce(Rc<dyn CompilerOpts>) -> Rc<dyn CompilerOpts>
    {
        let new_opts = f(self.opts.clone());
        Rc::new(JsCompilerOpts { opts: new_opts, options: self.options.clone() })
    }

    fn override_read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, Vec<u8>), CompileErr> {
        if filename.starts_with("*") {
            return self.opts.read_new_file(inc_from, filename);
        }

        let read_new_file_kw = JsValue::from_str("read_new_file");
        if let Ok(res) = js_sys::Reflect::get(&self.options, &read_new_file_kw) {
            let dirs = self.opts.get_search_paths();
            let call_fun: &js_sys::Function = res.unchecked_ref();
            let args = js_sys::Array::new();
            args.set(0_u32, JsValue::from_str(&filename));
            let dirs_array = js_sys::Array::new();
            for (i, d) in dirs.iter().enumerate() {
                dirs_array.set(i as u32, JsValue::from_str(d));
            }
            args.set(1_u32, dirs_array.unchecked_ref::<JsValue>().clone());
            let res = js_sys::Reflect::apply(
                &call_fun,
                &JsValue::null(),
                &args,
            ).map_err(|e| {
                if let Some(result_string) = e.as_string() {
                    CompileErr(Srcloc::start(&inc_from), format!("error reading {filename}: {result_string}"))
                } else {
                    CompileErr(Srcloc::start(&inc_from), format!("error reading {filename}"))
                }
            })?;

            let res_array: js_sys::Array = js_sys::Array::try_from(res).map_err(|_| {
                CompileErr(Srcloc::start(&inc_from), format!("error reading {filename}: could not convert result from injected reader"))
            })?;

            if res_array.iter().len() != 2 {
                return Err(CompileErr(Srcloc::start(&inc_from), format!("error reading {filename}: not an array from injected reader")));
            }

            let res_name = res_array.get(0);
            let res_data = res_array.get(1);

            if let (Some(name), Some(data)) = (res_name.as_string(), res_data.as_string()) {
                return Ok((name.clone(), data.as_bytes().to_vec()));
            } else {
                return Err(CompileErr(Srcloc::start(&inc_from), "could not convert result to string".to_string()));
            }
        }

        Err(CompileErr(
            Srcloc::start(&inc_from),
            format!("could not find {filename} to include"),
        ))
    }
    fn override_write_new_file(&self, _: &str, _: &[u8]) -> Result<(), CompileErr> {
        todo!()
    }
    fn override_compile_program(
        &self,
        context: &mut BasicCompileContext,
        sexp: Rc<SExp>,
    ) -> Result<CompilerOutput, CompileErr> {
        let me = Rc::new(self.clone());
        compile_pre_forms(context, me, &[sexp])
    }
}

fn convert_search_paths(search_paths_js: &[JsValue]) -> Result<Vec<String>, String> {
    let mut search_paths: Vec<String> = Vec::new();

    for j in search_paths_js
        .iter()
    {
        if let Some(s) = j.as_string() {
            search_paths.push(s);
        } else {
            return Err("could not convert all paths".to_string());
        }
    }

    Ok(search_paths)
}

// Compile a program, giving
// {"hex": "02392349234...", "symbols":{...}}
// or
// {"error": ...}
#[wasm_bindgen]
pub fn compile(input_js: JsValue, filename_js: JsValue, search_paths_js: Vec<JsValue>, options: JsValue) -> JsValue {
    let mut allocator = Allocator::new();
    let mut symbol_table = HashMap::new();
    let mut includes = Vec::new();
    let mut result_stream = Stream::new(None);

    let input = input_js.as_string().unwrap();
    let filename = filename_js.as_string().unwrap();
    let search_paths =
        match convert_search_paths(&search_paths_js) {
            Ok(paths) => paths,
            Err(e) => {
                return create_clvm_runner_err(e);
            }
        };

    let original_opts = Rc::new(DefaultCompilerOpts::new(&filename));
    let opts = Rc::new(JsCompilerOpts::new(original_opts, options))
        .set_search_paths(&search_paths);

    match compile_clvm_inner(
        &mut allocator,
        opts,
        &mut symbol_table,
        &mut includes,
        &filename,
        &input,
        &mut result_stream,
        false,
    ) {
        Ok(_) => make_compile_output(&result_stream, &symbol_table),
        Err(e) => create_clvm_runner_err(e),
    }
}

// Do get_dependencies on a program giving a list of dependencies.
#[wasm_bindgen]
pub fn get_dependencies(input_js: JsValue, filename_js: JsValue, search_paths_js: Vec<JsValue>, options: JsValue) -> Result<Vec<JsValue>, JsValue> {
    let input = input_js.as_string().unwrap();
    let filename = filename_js.as_string().unwrap();
    let search_paths = convert_search_paths(&search_paths_js)?;

    let original_opts = Rc::new(DefaultCompilerOpts::new(&filename));
    let opts = Rc::new(JsCompilerOpts::new(original_opts, options))
        .set_search_paths(&search_paths);

    let result_list = gather_dependencies(opts, &filename, &input).map_err(|e| {
        JsValue::from_str(&format!("{}: {}\n", e.0, e.1))
    })?.into_iter().map(|path| {
        JsValue::from_str(&decode_string(&path.name))
    }).collect();

    Ok(result_list)
}
