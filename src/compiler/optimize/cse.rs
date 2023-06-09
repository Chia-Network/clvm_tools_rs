use crate::compiler::optimize::bodyform::BodyformPathArc;
use crate::compiler::BodyForm;
use std::rc::Rc;

// Common subexpression elimintation.
// catalog subexpressions of the given bodyform and

pub struct CSEDetection {
    pub path: Vec<BodyformPathArc>,
    pub subexp: BodyForm,
}

pub fn cse_detect(_fe: Rc<BodyForm>) -> Rc<BodyForm> {
    todo!();
}
