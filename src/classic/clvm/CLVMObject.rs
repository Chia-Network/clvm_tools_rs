use crate::classic::clvm::__type_compatibility__::{Bytes, Tuple};
use crate::classic::clvm::EvalError::EvalError;

pub enum CLVMObject {
    Atom(Bytes),
    Pair(Tuple<Box<CLVMObject>, Box<CLVMObject>>)
}

pub fn nil() -> CLVMObject {
    return CLVMObject::Atom(Bytes::new(None));
}

/*
  This class implements the CLVM Object protocol in the simplest possible way,
  by just having an "atom" and a "pair" field
 */
impl CLVMObject {
    pub fn new() -> Self {
        return nil();
    }

    pub fn isAtom(obj: CLVMObject) -> bool {
        match obj {
            CLVMObject::Atom(_) => true,
            _ => false
        }
    }

    pub fn isCons(obj: CLVMObject) -> bool {
        match obj {
            CLVMObject::Pair(_) => true,
            _ => false
        }
    }
}
