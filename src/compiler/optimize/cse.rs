use std::rc::Rc;
use crate::compiler::BodyForm;
use crate::compiler::optimize::bodyform::BodyformPathArc;

// Common subexpression elimintation.
// catalog subexpressions of the given bodyform and

pub struct CSEDetection {
    path: Vec<BodyformPathArc>,
    subexp: BodyForm
}

pub fn cse_detect(fe: Rc<BodyForm>) -> Rc<BodyForm> {
    todo!();
}
