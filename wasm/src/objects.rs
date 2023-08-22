use js_sys;
use js_sys::{Array, JsString, Reflect};
use num_traits::cast::ToPrimitive;
use std::borrow::Borrow;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

use clvmr::Allocator;
use clvm_tools_rs::classic::clvm::__type_compatibility__::{Bytes, Stream, UnvalidatedBytesFromType};
use clvm_tools_rs::classic::clvm::serialize::{SimpleCreateCLVMObject, sexp_to_stream, sexp_from_stream};
use clvm_tools_rs::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use clvm_tools_rs::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs, sha256tree, truthy};
use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

use crate::api::{create_clvm_runner_err, get_next_id};
use crate::jsval::sexp_from_js_object;

const DEFAULT_CACHE_ENTRIES: usize = 1024;

struct FunctionWrapperDesc {
    export_name: &'static str,
    member_name: &'static str,
}

#[derive(Clone)]
pub struct ObjectCacheMember {
    pub modern: Rc<SExp>,
}

struct ObjectCache {
    cache_data: HashMap<i32, ObjectCacheMember>,
    cache_order: Vec<i32>,
    cache_length: usize,
}

pub struct JsCacheValue {
    pub entry: i32,
    pub content: String
}

pub fn js_cache_value_from_js(jsval: &JsValue) -> Result<JsCacheValue, JsValue> {
    let entry = js_sys::Reflect::get(
        jsval,
        &JsString::from("id")
    )?.as_f64().ok_or(JsString::from("id was not a number"))?;
    let content = js_sys::Reflect::get(
        jsval,
        &JsString::from("content")
    )?.as_string().ok_or(JsString::from("content was not a string"))?;

    Ok(JsCacheValue { entry: entry as i32, content })
}

impl Default for ObjectCache {
    fn default() -> Self {
        ObjectCache {
            cache_data: HashMap::default(),
            cache_order: Vec::default(),
            cache_length: DEFAULT_CACHE_ENTRIES,
        }
    }
}

impl ObjectCache {
    fn create_or_update_cache_entry(&mut self, id: i32, cache_member: ObjectCacheMember) {
        if id < 0 {
            // Special nil handling.
            return;
        }

        if self.cache_order.len() > self.cache_length {
            self.cache_data.remove(&self.cache_order[0]);
            self.cache_order.remove(0);
        }

        self.cache_data.insert(id, cache_member);
        self.cache_order.push(id);
    }

    fn create_entry_from_sexp(&mut self, id: i32, sexp: Rc<SExp>) -> Result<String, JsValue> {
        let mut allocator = Allocator::new();
        let node = convert_to_clvm_rs(
            &mut allocator,
            sexp.clone()
        ).map_err(|_| js_sys::JsString::from("could not convert to clvm"))?;
        let mut stream = Stream::new(None);
        sexp_to_stream(&mut allocator, node, &mut stream);

        self.create_or_update_cache_entry(id, ObjectCacheMember {
            modern: sexp.clone(),
        });

        Ok(stream.get_value().hex())
    }

    fn find_or_create_entry_from_hex(&mut self, entry: i32, content: &str) -> Result<ObjectCacheMember, JsValue> {
        if let Some(res) = self.cache_data.get(&entry) {
            return Ok(res.clone());
        }

        let mut allocator = Allocator::new();
        let bytes_from_hex = Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(content.to_string()))).map_err(|_| JsString::from("could not parse hex"))?;
        let mut stream = Stream::new(Some(bytes_from_hex));
        let parsed = sexp_from_stream(
            &mut allocator,
            &mut stream,
            Box::new(SimpleCreateCLVMObject {})
        )
            .map(|x| x.1)
            .map_err(|_| JsString::from("could not parse sexp from hex"))?;
        let srcloc = Srcloc::start("*var*");
        let modern = convert_from_clvm_rs(
            &mut allocator,
            srcloc,
            parsed
        ).map_err(|_| JsString::from("could not realize parsed sexp"))?;

        let cache_entry = ObjectCacheMember {
            modern
        };
        self.create_or_update_cache_entry(entry, cache_entry.clone());

        Ok(cache_entry)
    }
}

static PROGRAM_FUNCTIONS: &'static [FunctionWrapperDesc] = &[
    FunctionWrapperDesc {
        export_name: "toString",
        member_name: "to_string_internal",
    },
    FunctionWrapperDesc {
        export_name: "as_pair",
        member_name: "as_pair_internal",
    },
    FunctionWrapperDesc {
        export_name: "listp",
        member_name: "listp_internal",
    },
    FunctionWrapperDesc {
        export_name: "nullp",
        member_name: "nullp_internal",
    },
    FunctionWrapperDesc {
        export_name: "as_int",
        member_name: "as_int_internal",
    },
    FunctionWrapperDesc {
        export_name: "as_bigint",
        member_name: "as_bigint_internal",
    },
    FunctionWrapperDesc {
        export_name: "as_bin",
        member_name: "as_bin_internal",
    },
    FunctionWrapperDesc {
        export_name: "first",
        member_name: "first_internal",
    },
    FunctionWrapperDesc {
        export_name: "rest",
        member_name: "rest_internal",
    },
    FunctionWrapperDesc {
        export_name: "cons",
        member_name: "cons_internal",
    },
    FunctionWrapperDesc {
        export_name: "run",
        member_name: "run_internal",
    },
];

static TUPLE_FUNCTIONS: &'static [FunctionWrapperDesc] = &[
    FunctionWrapperDesc {
        export_name: "to_program",
        member_name: "tuple_to_program_internal",
    },
];

thread_local! {
    static OBJECT_CACHE: RefCell<ObjectCache> = {
        return RefCell::new(ObjectCache::default());
    };
    static PROGRAM_PROTOTYPE: RefCell<Option<JsValue>> = RefCell::new(None);
    static TUPLE_PROTOTYPE: RefCell<Option<JsValue>> = RefCell::new(None);
    static SRCLOC: Srcloc = Srcloc::start("*var*");
}

fn create_cached_sexp(id: i32, sexp: Rc<SExp>) -> Result<String, JsValue> {
    if !truthy(sexp.clone()) {
        return Ok("80".to_string());
    }
    OBJECT_CACHE.with(|ocache| {
        let mut mut_object_cache_ref: RefMut<ObjectCache> = ocache.borrow_mut();
        mut_object_cache_ref.create_entry_from_sexp(id, sexp)
    })
}

fn get_srcloc() -> Srcloc {
    SRCLOC.with(|s| s.clone())
}

pub fn find_cached_sexp(entry: i32, content: &str) -> Result<ObjectCacheMember, JsValue> {
    if content == "80" {
        return Ok(ObjectCacheMember {
            modern: Rc::new(SExp::Nil(get_srcloc()))
        });
    }

    OBJECT_CACHE.with(|ocache| {
        let mut mut_object_cache_ref: RefMut<ObjectCache> = ocache.borrow_mut();
        mut_object_cache_ref.find_or_create_entry_from_hex(entry, content)
    })
}

// Strategy for Program objects.
// We'll provide a Program object that allows users to have something that
// acts js-y but conserves compute time when possible.
//
// The result object we'll give back contain a string representation of the
// program they're associated with but also a cache hint.  If the cache object
// doesn't exist we'll re-parse the hex and re-cache it.
//
// The object is structured like this:
//
// {"cache-hint":33, "hex":"ff..."}
//
// Cache hints are never reused, and cleared when the counter transitions from
// low half to high half or vice versa.
//
// The object's prototype will include methods for Program, such as cons and call
// the real static methods of Program.
#[wasm_bindgen(inspectable)]
pub struct Program { }

// Build prototype
fn get_program_prototype() -> Result<JsValue, JsValue> {
    // We've already built the program prototype object.
    if let Some(pp) = PROGRAM_PROTOTYPE.with(|pp| pp.borrow().clone()) {
        return Ok(pp);
    }

    let prototype = js_sys::Object::new();

    let program_self = js_sys::eval("Program")?;
    for func_wrapper_desc in PROGRAM_FUNCTIONS.iter() {
        let to_string_fun = js_sys::Function::new_with_args(
            "",
            &format!("const t = this; return function() {{ let args = Array.prototype.slice.call(arguments); args.unshift(this); return t.{}.apply(null, args); }}", func_wrapper_desc.member_name)
        );

        let to_string_final = to_string_fun.call0(&program_self)?;
        js_sys::Reflect::set(
            &prototype,
            &js_sys::JsString::from(func_wrapper_desc.export_name),
            &to_string_final,
        )?;
    }

    PROGRAM_PROTOTYPE.with(|pp| {
        pp.replace(Some(prototype.clone().into()));
    });

    Ok(prototype.into())
}

fn get_tuple_prototype() -> Result<JsValue, JsValue> {
    if let Some(pp) = TUPLE_PROTOTYPE.with(|pp| pp.borrow().clone()) {
        return Ok(pp);
    }

    let prototype = js_sys::Object::new();

    let program_self = js_sys::eval("Program")?;
    for func_wrapper_desc in TUPLE_FUNCTIONS.iter() {
        let to_string_fun = js_sys::Function::new_with_args(
            "",
            &format!("const t = this; return function() {{ let args = Array.prototype.slice.call(arguments); args.unshift(this); return t.{}.apply(null, args); }}", func_wrapper_desc.member_name)
        );

        let to_string_final = to_string_fun.call0(&program_self)?;
        js_sys::Reflect::set(
            &prototype,
            &js_sys::JsString::from(func_wrapper_desc.export_name),
            &to_string_final,
        )?;
    }

    TUPLE_PROTOTYPE.with(|pp| {
        pp.replace(Some(prototype.clone().into()));
    });

    Ok(prototype.into())
}

pub fn finish_new_object(id: i32, encoded_hex: &str) -> Result<JsValue, JsValue> {
    let prototype = get_program_prototype()?;

    let new_object = js_sys::Object::new();
    js_sys::Reflect::set_prototype_of(
        &new_object,
        &prototype
    )?;

    js_sys::Reflect::set(
        &new_object,
        &js_sys::JsString::from("content"),
        &js_sys::JsString::from(encoded_hex),
    )?;
    js_sys::Reflect::set(
        &new_object,
        &js_sys::JsString::from("id"),
        &js_sys::Number::from(id),
    )?;

    Ok(new_object.into())
}

#[wasm_bindgen]
impl Program {
    #[wasm_bindgen]
    pub fn to(input: &JsValue) -> Result<JsValue, JsValue> {
        let loc = get_srcloc();
        let sexp = sexp_from_js_object(loc, input).map(Ok).unwrap_or_else(|| Err(create_clvm_runner_err(format!("unable to convert to value"))))?;

        let new_id = get_next_id();

        let encoded = create_cached_sexp(new_id, sexp)?;

        // Build the object
        finish_new_object(new_id, &encoded)
    }

    #[wasm_bindgen]
    pub fn from_hex(input: &str) -> Result<JsValue, JsValue> {
        let new_id = get_next_id();
        let obj = finish_new_object(new_id, input)?;
        Program::to(&obj)
    }

    #[wasm_bindgen]
    pub fn null() -> Result<JsValue, JsValue> {
        let new_id = get_next_id();
        let encoded = create_cached_sexp(new_id, Rc::new(SExp::Nil(get_srcloc())))?;

        finish_new_object(new_id, &encoded)
    }

    #[wasm_bindgen]
    pub fn sha256tree_internal(obj: &JsValue) -> Result<Vec<u8>, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;
        Ok(sha256tree(cached.modern.clone()))
    }

    #[wasm_bindgen]
    pub fn to_string_internal(obj: &JsValue) -> Result<JsValue, JsValue> {
        js_sys::Reflect::get(
            obj,
            &js_sys::JsString::from("content"),
        )
    }

    #[wasm_bindgen]
    pub fn as_pair_internal(obj: &JsValue) -> Result<JsValue, JsValue> {
        let prototype = get_tuple_prototype()?;
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;

        if let SExp::Cons(_, a, b) = cached.modern.borrow() {
            let id_a = get_next_id();
            let new_cached_a = create_cached_sexp(id_a, a.clone())?;
            let object_a = finish_new_object(id_a, &new_cached_a)?;
            let id_b = get_next_id();
            let new_cached_b = create_cached_sexp(id_b, b.clone())?;
            let object_b = finish_new_object(id_b, &new_cached_b)?;

            let result_value = Array::new();
            Reflect::set(
                &result_value,
                &JsString::from("0"),
                &object_a,
            )?;
            Reflect::set(
                &result_value,
                &JsString::from("1"),
                &object_b,
            )?;
            Reflect::set_prototype_of(
                &result_value,
                &prototype
            )?;
            return Ok(result_value.into());
        }

        Ok(JsValue::null())
    }

    #[wasm_bindgen]
    pub fn listp_internal(obj: &JsValue) -> Result<bool, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        Ok(cacheval.content.starts_with("ff"))
    }

    #[wasm_bindgen]
    pub fn nullp_internal(obj: &JsValue) -> Result<bool, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        Ok(cacheval.content == "80")
    }

    #[wasm_bindgen]
    pub fn as_int_internal(obj: &JsValue) -> Result<i32, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;
        let number = cached.modern.get_number().map_err(|_| JsString::from("not a number"))?;
        (number.to_i32()).ok_or(JsString::from("number out of range").into())
    }

    #[wasm_bindgen]
    pub fn as_bigint_internal(obj: &JsValue) -> Result<js_sys::BigInt, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;
        let number = cached.modern.get_number().map_err(|_| JsString::from("not a number"))?;
        let num_string = number.to_string();
        let num_str: &str = &num_string;
        js_sys::BigInt::new(&JsString::from(num_str)).map_err(|_| JsString::from("couldn't construct bigint").into())
    }

    #[wasm_bindgen]
    pub fn first_internal(obj: &JsValue) -> Result<JsValue, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;
        if let SExp::Cons(_, a, _) = cached.modern.borrow() {
            let id_a = get_next_id();
            let new_cached_a = create_cached_sexp(id_a, a.clone())?;
            return finish_new_object(id_a, &new_cached_a);
        }

        Err(JsString::from("not a cons").into())
    }

    #[wasm_bindgen]
    pub fn rest_internal(obj: &JsValue) -> Result<JsValue, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;
        if let SExp::Cons(_, _, a) = cached.modern.borrow() {
            let id_a = get_next_id();
            let new_cached_a = create_cached_sexp(id_a, a.clone())?;
            return finish_new_object(id_a, &new_cached_a);
        }

        Err(JsString::from("not a cons").into())
    }

    #[wasm_bindgen]
    pub fn cons_internal(obj: &JsValue, other: &JsValue) -> Result<JsValue, JsValue> {
        let cacheval = js_cache_value_from_js(obj)?;
        let cached = find_cached_sexp(cacheval.entry, &cacheval.content)?;

        let other_val = js_cache_value_from_js(other)?;
        let other_cache = find_cached_sexp(other_val.entry, &other_val.content)?;

        let new_id = get_next_id();
        let new_sexp = Rc::new(SExp::Cons(get_srcloc(), cached.modern.clone(), other_cache.modern.clone()));
        let new_cached = create_cached_sexp(new_id, new_sexp)?;
        finish_new_object(new_id, &new_cached)
    }

    #[wasm_bindgen]
    pub fn run_internal(obj: &JsValue, args: &JsValue) -> Result<JsValue, JsValue> {
        let progval = js_cache_value_from_js(obj)?;
        let prog_cache = find_cached_sexp(progval.entry, &progval.content)?;

        let argval = js_cache_value_from_js(args)?;
        let arg_cache = find_cached_sexp(argval.entry, &argval.content)?;

        let mut allocator = Allocator::new();
        let prog_classic = convert_to_clvm_rs(
            &mut allocator,
            prog_cache.modern.clone()
        ).map_err(|_| {
            let err: JsValue = JsString::from("error converting program").into();
            err
        })?;
        let arg_classic = convert_to_clvm_rs(
            &mut allocator,
            arg_cache.modern.clone()
        ).map_err(|_| {
            let err: JsValue = JsString::from("error converting args").into();
            err
        })?;

        let runner = DefaultProgramRunner::default();
        let run_result =
            runner.run_program(
                &mut allocator,
                prog_classic,
                arg_classic,
                None
            ).map_err(|e| {
                let err_str: &str = &e.1;
                let err: JsValue = JsString::from(err_str).into();
                err
            })?;
        let modern_result = convert_from_clvm_rs(
            &mut allocator,
            get_srcloc(),
            run_result.1
        ).map_err(|_| {
            let err: JsValue = JsString::from("error converting result").into();
            err
        })?;
        let result_id = get_next_id();
        let new_cached_result = create_cached_sexp(result_id, modern_result)?;
        finish_new_object(result_id, &new_cached_result)
    }

    #[wasm_bindgen]
    pub fn tuple_to_program_internal(obj: &JsValue) -> Result<JsValue, JsValue> {
        let a = js_sys::Reflect::get(
            obj,
            &JsString::from("0"),
        )?;
        let b = js_sys::Reflect::get(
            obj,
            &JsString::from("1"),
        )?;
        Program::cons_internal(&a, &b)
    }

    #[wasm_bindgen]
    pub fn as_bin_internal(obj: &JsValue) -> Result<Vec<u8>, JsValue> {
        let convert = Reflect::get(
            obj,
            &JsString::from("content"),
        )?.as_string().ok_or(JsString::from("content wasn't a hex string"))?;
        let bytes = Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(convert))).map_err(|_| JsString::from("could not convert to binary data"))?;
        Ok(bytes.data().clone())
    }
}
