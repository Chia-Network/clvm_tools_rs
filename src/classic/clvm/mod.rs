use std::collections::HashMap;

pub mod __type_compatibility__;
pub mod as_rust;
pub mod casts;
pub mod costs;
pub mod serialize;
pub mod sexp;

struct KwAtomPair {
    v: u8,
    n: &'static str,
}

const KW_PAIRS: [KwAtomPair; 32] = [
    KwAtomPair { v: 0x01, n: "q" },
    KwAtomPair { v: 0x02, n: "a" },
    KwAtomPair { v: 0x03, n: "i" },
    KwAtomPair { v: 0x04, n: "c" },
    KwAtomPair { v: 0x05, n: "f" },
    KwAtomPair { v: 0x06, n: "r" },
    KwAtomPair { v: 0x07, n: "l" },
    KwAtomPair { v: 0x08, n: "x" },
    KwAtomPair { v: 0x09, n: "=" },
    KwAtomPair { v: 0x0a, n: ">s" },
    KwAtomPair {
        v: 0x0b,
        n: "sha256",
    },
    KwAtomPair {
        v: 0x0c,
        n: "substr",
    },
    KwAtomPair {
        v: 0x0d,
        n: "strlen",
    },
    KwAtomPair {
        v: 0x0e,
        n: "concat",
    },
    KwAtomPair { v: 0x10, n: "+" },
    KwAtomPair { v: 0x11, n: "-" },
    KwAtomPair { v: 0x12, n: "*" },
    KwAtomPair { v: 0x13, n: "/" },
    KwAtomPair {
        v: 0x14,
        n: "divmod",
    },
    KwAtomPair { v: 0x15, n: ">" },
    KwAtomPair { v: 0x16, n: "ash" },
    KwAtomPair { v: 0x17, n: "lsh" },
    KwAtomPair {
        v: 0x18,
        n: "logand",
    },
    KwAtomPair {
        v: 0x19,
        n: "logior",
    },
    KwAtomPair {
        v: 0x1a,
        n: "logxor",
    },
    KwAtomPair {
        v: 0x1b,
        n: "lognot",
    },
    KwAtomPair {
        v: 0x1d,
        n: "point_add",
    },
    KwAtomPair {
        v: 0x1e,
        n: "pubkey_for_exp",
    },
    KwAtomPair { v: 0x20, n: "not" },
    KwAtomPair { v: 0x21, n: "any" },
    KwAtomPair { v: 0x22, n: "all" },
    KwAtomPair {
        v: 0x24,
        n: "softfork",
    },
];

lazy_static! {
    pub static ref KEYWORD_FROM_ATOM_: HashMap<Vec<u8>, String> = {
        let mut result = HashMap::new();
        for pair in KW_PAIRS {
            result.insert(vec![pair.v], pair.n.to_string());
        }
        result
    };
    pub static ref KEYWORD_TO_ATOM_: HashMap<String, Vec<u8>> = {
        let mut result = HashMap::new();
        for pair in KW_PAIRS {
            result.insert(pair.n.to_string(), vec![pair.v]);
        }
        result
    };
}

pub fn keyword_from_atom() -> &'static HashMap<Vec<u8>, String> {
    &KEYWORD_FROM_ATOM_
}

pub fn keyword_to_atom() -> &'static HashMap<String, Vec<u8>> {
    &KEYWORD_TO_ATOM_
}
