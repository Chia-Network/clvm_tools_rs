use std::collections::HashMap;
use std::rc::Rc;

use wasm_bindgen::prelude::*;
use wasm_bindgen::{JsCast, JsValue};

use clvmr::Allocator;

use clvm_tools_rs::classic::clvm::__type_compatibility__::Stream;
use clvm_tools_rs::classic::clvm_tools::stages::stage_0::TRunProgram;
use clvm_tools_rs::classic::clvm_tools::clvmc::compile_clvm_inner;
use clvm_tools_rs::compiler::CompileContextWrapper;
use clvm_tools_rs::compiler::compiler::{DefaultCompilerOpts, compile_pre_forms};
use clvm_tools_rs::compiler::comptypes::{CompileErr, CompilerOpts, PrimaryCodegen};
use clvm_tools_rs::compiler::dialect::AcceptedDialect;
use clvm_tools_rs::compiler::optimize::get_optimizer;
use clvm_tools_rs::compiler::sexp::SExp;
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

impl CompilerOpts for JsCompilerOpts {
    fn filename(&self) -> String {
        self.opts.filename()
    }
    fn code_generator(&self) -> Option<PrimaryCodegen> {
        self.opts.code_generator()
    }
    fn dialect(&self) -> AcceptedDialect {
        self.opts.dialect()
    }
    fn in_defun(&self) -> bool {
        self.opts.in_defun()
    }
    fn stdenv(&self) -> bool {
        self.opts.stdenv()
    }
    fn optimize(&self) -> bool {
        self.opts.optimize()
    }
    fn frontend_opt(&self) -> bool {
        self.opts.frontend_opt()
    }
    fn frontend_check_live(&self) -> bool {
        self.opts.frontend_check_live()
    }
    fn start_env(&self) -> Option<Rc<SExp>> {
        self.opts.start_env()
    }
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>> {
        self.opts.prim_map()
    }
    fn disassembly_ver(&self) -> Option<usize> {
        self.opts.disassembly_ver()
    }
    fn get_search_paths(&self) -> Vec<String> {
        self.opts.get_search_paths()
    }

    fn set_dialect(&self, dialect: AcceptedDialect) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_dialect(dialect);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_search_paths(dirs);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_disassembly_ver(&self, ver: Option<usize>) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_disassembly_ver(ver);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_in_defun(new_in_defun);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_stdenv(new_stdenv);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_optimize(&self, optimize: bool) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_optimize(optimize);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_frontend_opt(&self, optimize: bool) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_frontend_opt(optimize);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_frontend_check_live(&self, check: bool) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_frontend_check_live(check);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_code_generator(&self, new_code_generator: PrimaryCodegen) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_code_generator(new_code_generator);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_start_env(start_env);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }
    fn set_prim_map(&self, prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>) -> Rc<dyn CompilerOpts> {
        let inner_opts_new = self.opts.set_prim_map(prims);
        Rc::new(JsCompilerOpts {
            opts: inner_opts_new,
            .. self.clone()
        })
    }

    fn read_new_file(
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

            if let Some(result_string) = res.as_string() {
                return Ok((filename.clone(), result_string.as_bytes().to_vec()));
            } else {
                return Err(CompileErr(Srcloc::start(&inc_from), "could not convert result to string".to_string()));
            }
        }

        Err(CompileErr(
            Srcloc::start(&inc_from),
            format!("could not find {filename} to include"),
        ))
    }
    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr> {
        let me = Rc::new(self.clone());
        let mut context_wrapper = CompileContextWrapper::new(
            allocator,
            runner,
            symbol_table,
            get_optimizer(&sexp.loc(), me.clone())?,
        );
        compile_pre_forms(&mut context_wrapper.context, me, &[sexp])
    }
}

// Compile a program, giving
// {"hex": "02392349234...", "symbols":{...}}
// or
// {"error": ...}
#[wasm_bindgen]
pub fn compile(input_js: JsValue, filename_js: JsValue, search_paths_js: Vec<JsValue>, options: JsValue) -> JsValue {
    let mut allocator = Allocator::new();
    let mut symbol_table = HashMap::new();
    let mut result_stream = Stream::new(None);

    let input = input_js.as_string().unwrap();
    let filename = filename_js.as_string().unwrap();
    let search_paths: Vec<String> = search_paths_js
        .iter()
        .map(|j| j.as_string().unwrap())
        .collect();

    let original_opts = Rc::new(DefaultCompilerOpts::new(&filename));
    let opts = Rc::new(JsCompilerOpts::new(original_opts, options))
        .set_search_paths(&search_paths);
    match compile_clvm_inner(
        &mut allocator,
        opts,
        &mut symbol_table,
        &filename,
        &input,
        &mut result_stream,
        false,
    ) {
        Ok(_) => make_compile_output(&result_stream, &symbol_table),
        Err(e) => create_clvm_runner_err(e),
    }
}
