use std::fmt::Debug;
use std::rc::Rc;
use crate::compiler::comptypes::{BodyForm, CompileForm};
use crate::compiler::smt::verification::VerificationCondition;

pub trait Proposition {
    fn and(&self, other: Rc<dyn Proposition>) -> Rc<dyn DebugProposition>;
}

pub trait DebugProposition: Debug + Proposition { }

// Based heavily on vcgen from esverify.
#[derive(Debug, Clone)]
pub struct VCGenerator {
    program: CompileForm,
    nextvar: usize,
    vcs: Vec<VerificationCondition>,
    testBody: Rc<BodyForm>,
    assertionPolarity: Option<bool>,
    simpleAssertion: bool,
    assumptions: Vec<String>,
    prop: Rc<dyn DebugProposition>
}

impl VCGenerator {
    pub fn new(program: CompileForm, test: Rc<BodyForm>, polarity: Option<bool>, simple: bool, assumptions: Vec<String>, prop: Rc<dyn DebugProposition>) -> Self {
        VCGenerator {
            program,
            nextvar: 1,
            vcs: Vec::new(),
            testBody: test,
            assertionPolarity: polarity,
            simpleAssertion: simple,
            assumptions,
            prop
        }
    }

    pub fn add_have(&mut self, p: Rc<dyn Proposition>) {
        self.prop = self.prop.and(p);
    }

    // check

    pub fn freshVar(&mut self) -> String {
        let next_var_num = self.nextvar;
        self.nextvar += 1;
        format!("_tmp_{}", next_var_num)
    }

    
}
