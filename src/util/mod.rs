use num_bigint::BigInt;
use unicode_segmentation::UnicodeSegmentation;

pub type Number = BigInt;

pub fn number_from_u8(v: &[u8]) -> Number {
    let len = v.len();
    if len == 0 {
        0.into()
    } else {
        Number::from_signed_bytes_be(v)
    }
}

pub fn u8_from_number(v: Number) -> Vec<u8> {
    v.to_signed_bytes_be()
}

pub fn index_of_match<F, T>(cb: F, haystack: &[T]) -> i32
where
    F: Fn(&T) -> bool,
{
    for (i, ch) in haystack.iter().enumerate() {
        if cb(ch) {
            return i as i32;
        }
    }
    -1
}

pub fn skip_leading(s: &str, dash: &str) -> String {
    return s.graphemes(true).skip_while(|ch| dash == *ch).collect();
}

pub fn collapse<A>(r: Result<A, A>) -> A {
    match r {
        Ok(a) => a,
        Err(e) => e,
    }
}
