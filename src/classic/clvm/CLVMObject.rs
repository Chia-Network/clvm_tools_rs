use std::fmt::Debug;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{Bytes};

#[derive(Debug)]
pub enum CLVMObject {
    Atom(Bytes),
    Pair(Rc<CLVMObject>, Rc<CLVMObject>)
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
            CLVMObject::Pair(_, _) => true,
            _ => false
        }
    }
}
