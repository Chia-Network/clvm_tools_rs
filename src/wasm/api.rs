use core::sync::atomic::AtomicUsize;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Mutex;

use wasm_bindgen::prelude::*;

#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

struct Runner {
    
}

lazy_static! {
    static ref next_id: AtomicUsize = {
        return AtomicUsize::new(0);
    };
    static ref runners: Mutex<RefCell<HashMap<i32, Runner>>> = {
        return Mutex::new(RefCell::new(HashMap::new()));
    };
}

/* Given a program in text (utf-8) form and arguments, compile the program and
 * return a runner object.
 */
#[wasm_bindgen]
pub fn create_clvm_runner(program: &[u8], args: &[u8]) -> i32 {
    
    return 0;
}

#[wasm_bindgen]
pub fn remove_clvm_runner(runner: i32) {
}

// Run until the given step, returning the current machine state.
#[wasm_bindgen]
pub fn run_until_step(runner: i32, step: i32) -> Vec<u8> {
    return Vec::new();
}
