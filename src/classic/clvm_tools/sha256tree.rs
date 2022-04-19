use clvm_rs::allocator::{Allocator, NodePtr, SExp};

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType};

pub fn sha256tree<'a>(allocator: &'a mut Allocator, v: NodePtr) -> Bytes {
    match allocator.sexp(v) {
        SExp::Pair(l, r) => {
            let left = sha256tree(allocator, l);
            let right = sha256tree(allocator, r);
            sha256(
                Bytes::new(Some(BytesFromType::Raw(vec![2])))
                    .concat(&left)
                    .concat(&right),
            )
        }
        SExp::Atom(a) => sha256(
            Bytes::new(Some(BytesFromType::Raw(vec![1]))).concat(&Bytes::new(Some(
                BytesFromType::Raw(allocator.buf(&a).to_vec()),
            ))),
        ),
    }
}
