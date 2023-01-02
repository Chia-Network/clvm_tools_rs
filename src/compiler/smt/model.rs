use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::sexp::SExp;

use super::smtlib::SMTOutput;

#[derive(Debug, Clone)]
pub struct Fun {
}

#[derive(Debug, Clone)]
pub struct Model {
    vars: HashMap<String, Rc<SExp>>,
    funs: HashMap<String, Fun>
}

#[derive(Debug, Clone)]
pub enum ModelOrMessage {
    SMTModel(Model),
    SMTMessage(String)
}

impl Model {
    fn new(smt: SMTOutput) -> Self {
        todo!()
    }
}
