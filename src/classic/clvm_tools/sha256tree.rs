use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    SHA256
};
use crate::classic::clvm::CLVMObject::CLVMObject;
use crate::classic::clvm::SExp::SExp;

pub fn sha256tree(v: &SExp) -> Bytes {
    match v {
        CLVMObject::Pair(l,r) => {
            let left = sha256tree(&*l);
            let right = sha256tree(&*r);
            return SHA256(
                Bytes::new(Some(BytesFromType::Raw(vec!(2)))).
                    concat(&left).concat(&right)
            );
        },
        CLVMObject::Atom(a) => {
            return SHA256(
                Bytes::new(Some(BytesFromType::Raw(vec!(1)))).
                    concat(a)
            );
        }
    }
}
