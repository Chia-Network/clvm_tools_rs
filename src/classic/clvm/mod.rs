use std::collections::HashMap;

pub mod __type_compatibility__;
pub mod as_rust;
pub mod CLVMObject;
pub mod casts;
pub mod costs;
pub mod core_ops;
pub mod EvalError;
pub mod more_ops;
pub mod serialize;
pub mod SExp;

lazy_static! {
    static ref keyword_from_atom : HashMap<String, String> = {
        HashMap::new()
    };
    static ref keyword_to_atom : HashMap<String, String> = {
        HashMap::new()
    };
}

pub fn KEYWORD_FROM_ATOM() -> &'static HashMap<String, String> {
    return &keyword_from_atom;
}

pub fn KEYWORD_TO_ATOM() -> &'static HashMap<String, String> {
    return &keyword_to_atom;
}
