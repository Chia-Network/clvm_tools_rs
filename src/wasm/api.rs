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
    js_object_from_sexp,
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

fn create_clvm_runner_err(error: String) -> String {
    let mut err_hash = HashMap::new();
    err_hash.insert("error".to_string(), error);
    serde_json::to_string(&err_hash).unwrap()
}

fn create_clvm_runner_run_failure(err: &RunFailure) -> String {
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
pub fn create_clvm_runner(hex_prog: String, hex_args: String, symbols: js_sys::Object, overrides: js_sys::Object) -> String {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let prog_srcloc = Srcloc::start(&"*program*".to_string());
    let args_srcloc = Srcloc::start(&"*args*".to_string());
    let mut prim_map = HashMap::new();
    let mut symbol_table = HashMap::new();
    let mut override_funs: HashMap<String, Box<dyn CldbSingleBespokeOverride>> = HashMap::new();

    for ent in js_sys::Object::entries(&symbols).values() {
        let pair = js_sys::Array::from(&ent.unwrap());
        let key = pair.at(0);
        let val = pair.at(1);
        match (key.as_string(), val.as_string()) {
            (Some(k), Some(v)) => { symbol_table.insert(k.clone(), v.clone()); },
            _ => { }
        }
    }

    for ent in js_sys::Object::entries(&overrides).values() {
        let pair = js_sys::Array::from(&ent.unwrap());
        let key = pair.at(0);
        let val = pair.at(1);
        match (key.as_string(), js_sys::Function::try_from(&val)) {
            (Some(k), Some(f)) => {
                override_funs.insert(
                    k.clone(),
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
    let args = match hex_to_modern_sexp(
        &mut allocator,
        &HashMap::new(),
        args_srcloc.clone(),
        &hex_args,
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

    return this_id.to_string();
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
