use js_sys;
use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::swap;
use std::rc::Rc;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use wasm_bindgen::prelude::*;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};
use crate::compiler::cldb::{
    CldbRunnable,
    CldbOverrideBespokeCode,
    CldbSingleBespokeOverride,
    CldbRun,
    CldbRunEnv,
    hex_to_modern_sexp
};
use crate::compiler::clvm::start_step;
use crate::compiler::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::wasm::jsval::{
    btreemap_to_object,
    get_property,
    js_object_from_sexp,
    js_pair,
    object_to_value,
    sexp_from_js_object
};

#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

struct JsRunStep {
    allocator: Allocator,
    runner: Rc<dyn TRunProgram>,
    prim_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    cldbrun: CldbRun,
}

thread_local! {
    static NEXT_ID: AtomicUsize = {
        return AtomicUsize::new(0);
    };
    static RUNNERS: RefCell<HashMap<i32, JsRunStep>> = {
        return RefCell::new(HashMap::new());
    };
}

fn insert_runner(this_id: i32, runner: JsRunStep) {
    RUNNERS.with(|runcell| {
        runcell.replace_with(|coll| {
            let mut work_collection = HashMap::new();
            swap(coll, &mut work_collection);
            work_collection.insert(this_id, runner);
            work_collection
        });
    });
}

fn remove_runner(this_id: i32) {
    RUNNERS.with(|runcell| {
        runcell.replace_with(|coll| {
            let mut work_collection = HashMap::new();
            swap(coll, &mut work_collection);
            work_collection.remove(&this_id);
            work_collection
        });
    });
}

fn with_runner<F,V>(this_id: i32, f: F) -> Option<V>
    where
    F : FnOnce(&mut JsRunStep) -> Option<V>
{
    let mut result = None;
    RUNNERS.with(|runcell| {
        runcell.replace_with(|coll| {
            let mut work_collection = HashMap::new();
            swap(coll, &mut work_collection);
            match work_collection.get_mut(&this_id) {
                Some(r_ref) => {
                    result = f(r_ref);
                },
                _ => { }
            }
            work_collection
        });
    });
    result
}

fn create_clvm_runner_err(error: String) -> JsValue {
    let array = js_sys::Array::new();
    array.set(0, js_pair(JsValue::from_str("error"), JsValue::from_str(&error)));
    return object_to_value(&js_sys::Object::from_entries(&array).unwrap());
}

fn create_clvm_runner_run_failure(err: &RunFailure) -> JsValue {
    match err {
        RunFailure::RunErr(l,e) => {
            return create_clvm_runner_err(format!("{}: Error {}", l.to_string(), e));
        },
        RunFailure::RunExn(l,e) => {
            return create_clvm_runner_err(format!("{}: Exn {}", l.to_string(), e.to_string()))
        }
    }
}

struct JsBespokeOverride { fun: js_sys::Function }

impl CldbSingleBespokeOverride for JsBespokeOverride {
    // We've been called so compose a javascript-compatible value to pass out
    // based on the env.
    // When the user returns, try to convert the result back to sexp.
    fn get_override(&self, env: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
        let args = js_sys::Array::new();
        args.set(0, js_object_from_sexp(env.clone()));
        self.fun.apply(&JsValue::null(), &args).map_err(|e| {
            let eval = js_sys::Array::from(&e);
            RunFailure::RunErr(env.loc(), format!("exception from javascript: {}", eval.to_string()))
        }).and_then(|v| {
            sexp_from_js_object(env.loc(), &v).map(|s| Ok(s)).
                unwrap_or_else(|| {
                    Err(RunFailure::RunErr(env.loc(), "javascript passed in a value that can't be converted to sexp".to_string()))
                })
        })
    }
}

/* Given a program in text (utf-8) form and arguments, compile the program and
 * return a runner object.
 */
#[wasm_bindgen]
pub fn create_clvm_runner(hex_prog: String, args_js: JsValue, symbols: js_sys::Object, overrides: js_sys::Object) -> JsValue {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let args_srcloc = Srcloc::start(&"*args*".to_string());
    let prog_srcloc = Srcloc::start(&"*program*".to_string());
    let mut prim_map = HashMap::new();
    let mut symbol_table = HashMap::new();
    let mut override_funs: HashMap<String, Box<dyn CldbSingleBespokeOverride>> = HashMap::new();

    let args =
        match sexp_from_js_object(args_srcloc.clone(), &args_js) {
            Some(v) => v,
            None => {
                return create_clvm_runner_run_failure(
                    &RunFailure::RunErr(
                        args_srcloc.clone(),
                        "failed to convert args to sexp".to_string()
                    )
                );
            }
        };

    for ent in js_sys::Object::keys(&symbols).values() {
        let key = ent.unwrap().as_string().unwrap();
        let val = get_property(&symbols, &key).unwrap().as_string().unwrap();
        symbol_table.insert(key, val);
    }

    for ent in js_sys::Object::keys(&overrides).values() {
        let key = ent.unwrap().as_string().unwrap();
        let val = get_property(&overrides, &key).unwrap();
        match js_sys::Function::try_from(&val) {
            Some(f) => {
                override_funs.insert(
                    key,
                    Box::new(JsBespokeOverride { fun: f.clone() })
                );
            },
            _ => { }
        }
    }

    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }

    let program = match hex_to_modern_sexp(
        &mut allocator,
        &symbol_table,
        prog_srcloc.clone(),
        &hex_prog,
    ) {
        Ok(v) => v,
        Err(e) => { return create_clvm_runner_run_failure(&e); }
    };

    let runner_override: Box<dyn CldbRunnable> =
        Box::new(CldbOverrideBespokeCode::new(symbol_table.clone(), override_funs));
    let prim_map_rc = Rc::new(prim_map);
    let step = start_step(program.clone(), args.clone());
    let cldbenv = CldbRunEnv::new(None, vec![], runner_override);
    let cldbrun = CldbRun::new(runner.clone(), prim_map_rc.clone(), Box::new(cldbenv), step);

    let this_id = NEXT_ID.with(|n| n.fetch_add(1, Ordering::SeqCst) as i32);
    insert_runner(this_id, JsRunStep {
        allocator,
        runner,
        prim_map: prim_map_rc,
        cldbrun
    });

    return JsValue::from(this_id);
}

#[wasm_bindgen]
pub fn final_value(runner: i32) -> JsValue {
    with_runner(runner, |r| {
        r.cldbrun.final_result().map(|v| js_object_from_sexp(v))
    }).unwrap_or_else(|| JsValue::null())
}

#[wasm_bindgen]
pub fn remove_clvm_runner(runner: i32) {
    remove_runner(runner);
}

// Run until the given step, returning the current machine state.
#[wasm_bindgen]
pub fn run_step(runner: i32) -> JsValue {
    with_runner(runner, |r| {
        if r.cldbrun.is_ended() {
            return None;
        }

        r.cldbrun.step(&mut r.allocator)
    }).map(|result_hash| btreemap_to_object(result_hash.iter())).
        unwrap_or_else(|| JsValue::null())
}
