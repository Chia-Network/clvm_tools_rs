use std::fmt::Display;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType};
use crate::classic::clvm::casts::By;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TreeHash {
    s: String,
}

impl Display for TreeHash {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        formatter.write_str(&self.s)
    }
}

impl TreeHash {
    pub fn new_from_sexp(allocator: &mut Allocator, r: NodePtr) -> Self {
        TreeHash {
            s: sha256tree(allocator, r).hex(),
        }
    }
}

pub fn sha256tree(allocator: &mut Allocator, v: NodePtr) -> Bytes {
    match allocator.sexp(v) {
        SExp::Pair(l, r) => {
            let left = sha256tree(allocator, l);
            let right = sha256tree(allocator, r);
            sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![2])))
                    .concat(&left)
                    .concat(&right)
                    .data(),
            )
        }
        SExp::Atom => {
            let v_atom = By::new(allocator, v);
            sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![1])))
                    .concat(&Bytes::new(Some(
                        // only v in scope.
                        BytesFromType::Raw(v_atom.to_vec()),
                    )))
                    .data(),
            )
        }
    }
}
