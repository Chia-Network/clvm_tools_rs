use js_sys;
use js_sys::{Array, BigInt, Object};
use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

use wasm_bindgen::prelude::*;

pub fn array_to_value(v: Array) -> JsValue {
    let jref: &JsValue = v.as_ref();
    jref.clone()
}

pub fn object_to_value(v: &Object) -> JsValue {
    let jref: &JsValue = v.as_ref();
    jref.clone()
}

pub fn js_pair(a: JsValue, b: JsValue) -> JsValue {
    let pair_array = Array::new();
    pair_array.set(0, a);
    pair_array.set(1, b);
    array_to_value(pair_array)
}

pub fn js_from_location(l: Srcloc) -> JsValue {
    let loc_array = Array::new();
    let file_copy: &String = l.file.borrow();
    loc_array.set(
        0,
        js_pair(JsValue::from_str("file"), JsValue::from_str(&file_copy)),
    );
    loc_array.set(
        1,
        js_pair(JsValue::from_str("line"), JsValue::from_f64(l.line as f64)),
    );
    loc_array.set(
        2,
        js_pair(JsValue::from_str("col"), JsValue::from_f64(l.col as f64)),
    );
    match l.until {
        Some((tl, tc)) => {
            let til_array = Array::new();
            til_array.set(
                0,
                js_pair(JsValue::from_str("line"), JsValue::from_f64(tl as f64)),
            );
            til_array.set(
                1,
                js_pair(JsValue::from_str("col"), JsValue::from_f64(tc as f64)),
            );
            loc_array.set(
                3,
                object_to_value(Object::from_entries(&til_array).as_ref().unwrap()),
            );
        }
        _ => {}
    }
    object_to_value(Object::from_entries(&loc_array).as_ref().unwrap())
}

pub fn js_object_from_sexp(v: Rc<SExp>) -> JsValue {
    match v.borrow() {
        SExp::Nil(_) => JsValue::null(),
        SExp::Integer(_, i) => JsValue::bigint_from_str(&i.to_string()),
        SExp::QuotedString(_, _, q) => {
            JsValue::from_str(&Bytes::new(Some(BytesFromType::Raw(q.clone()))).decode())
        }
        SExp::Atom(_, q) => {
            JsValue::from_str(&Bytes::new(Some(BytesFromType::Raw(q.clone()))).decode())
        }
        SExp::Cons(l, a, b) => v
            .proper_list()
            .map(|lst| {
                let array = Array::new();
                for i in 0..lst.len() {
                    array.set(i as u32, js_object_from_sexp(Rc::new(lst[i].clone())));
                }
                array_to_value(array)
            })
            .unwrap_or_else(|| {
                let array = Array::new();
                array.set(
                    0,
                    js_pair(JsValue::from_str("location"), js_from_location(l.clone())),
                );
                let pair: JsValue = js_pair(
                    JsValue::from_str("pair"),
                    js_pair(
                        js_object_from_sexp(a.clone()),
                        js_object_from_sexp(b.clone()),
                    ),
                );
                array.set(1, pair);
                object_to_value(&Object::from_entries(&array).unwrap())
            }),
    }
}

pub fn get_property(o: &Object, name: &str) -> Option<JsValue> {
    Object::try_from(&Object::get_own_property_descriptor(
        o,
        &JsValue::from_str(name),
    ))
    .and_then(|desc_obj| match Object::try_from(desc_obj) {
        Some(o) => {
            for pj in Object::entries(o).values() {
                let pair = Array::from(&pj.unwrap());
                let propname = pair.get(0).as_string();
                if propname == Some("value".to_string()) {
                    return Some(pair.get(1));
                }
            }
            None
        }
        _ => None,
    })
}

fn location_lc_pair(o: &Object) -> Option<(usize, usize)> {
    get_property(o, "line").and_then(|l| l.as_f64()).map(|l| {
        (
            l as usize,
            get_property(o, "col")
                .and_then(|c| c.as_f64())
                .map(|c| c as usize)
                .unwrap_or_else(|| 0),
        )
    })
}

fn location(o: &Object) -> Option<Srcloc> {
    Object::try_from(o)
        .and_then(|lo| get_property(lo, "file").and_then(|f| f.as_string()))
        .and_then(|f| location_lc_pair(o).map(|(l, c)| (f, l, c)))
        .map(|(f, l, c)| Srcloc {
            file: Rc::new(f),
            line: l,
            col: c,
            until: get_property(o, "until")
                .and_then(|lo| Object::try_from(&lo).map(|o| o.clone()))
                .and_then(|lo| location_lc_pair(&lo)),
        })
}

pub fn sexp_from_js_object(sstart: Srcloc, v: &JsValue) -> Option<Rc<SExp>> {
    if v.is_bigint() {
        BigInt::new(v)
            .ok()
            .and_then(|v| v.to_string(10).ok())
            .and_then(|v| v.as_string())
            .and_then(|v| v.parse::<Number>().ok())
            .map(|x| Rc::new(SExp::Integer(sstart.clone(), x)))
    } else if Array::is_array(v) {
        let a = Array::from(v);
        let mut result_value = Rc::new(SExp::Nil(Srcloc::start(&"*js*".to_string())));
        for i_rev in 0..a.length() {
            let i = a.length() - i_rev - 1;
            match sexp_from_js_object(sstart.clone(), &a.get(i)) {
                Some(nv) => {
                    result_value = Rc::new(SExp::Cons(nv.loc(), nv, result_value));
                }
                _ => {}
            }
        }
        Some(result_value)
    } else {
        Object::try_from(v)
            .map(|o| {
                let loc = get_property(o, "location")
                    .and_then(|o| Object::try_from(&o).map(|o| o.clone()))
                    .and_then(|o| location(&o))
                    .unwrap_or_else(|| sstart.clone());
                get_property(o, "pair")
                    .and_then(|p| {
                        let pa = Array::from(&p);
                        sexp_from_js_object(sstart.clone(), &pa.get(0)).map(|a| (pa, a))
                    })
                    .and_then(|(pa, a)| {
                        sexp_from_js_object(sstart.clone(), &pa.get(1))
                            .map(|b| Rc::new(SExp::Cons(loc, a, b)))
                    })
            })
            .unwrap_or_else(|| {
                v.as_string()
                    .map(|s| Some(Rc::new(SExp::Atom(sstart.clone(), s.as_bytes().to_vec()))))
                    .unwrap_or_else(|| {
                        let n = js_sys::Number::new(&v);
                        Some(Rc::new(SExp::Integer(
                            sstart.clone(),
                            (n.value_of() as i64).to_bigint().unwrap(),
                        )))
                    })
            })
    }
}

pub fn btreemap_to_object<'a>(iter: impl Iterator<Item = (&'a String, &'a String)>) -> JsValue {
    let entries = Array::new();
    for pv in iter {
        let pair = Array::new();
        pair.set(0, JsValue::from_str(&pv.0));
        pair.set(1, JsValue::from_str(&pv.1));
        let pair_ref: &JsValue = pair.as_ref();
        entries.set(entries.length(), pair_ref.clone());
    }
    object_to_value(&Object::from_entries(&entries).as_ref().unwrap())
}

pub fn read_string_to_string_map(
    symbols: &js_sys::Object,
) -> Result<HashMap<String, String>, String> {
    let mut result = HashMap::new();
    for ent in js_sys::Object::keys(&symbols).values() {
        let key = ent.unwrap().as_string().unwrap();
        match get_property(&symbols, &key).unwrap().as_string() {
            Some(val) => {
                result.insert(key, val);
            }
            _ => {
                return Err(format!("key {} wasn't string", key));
            }
        }
    }
    Ok(result)
}
