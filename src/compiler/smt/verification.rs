use crate::compiler::comptypes::CompileErr;
use super::model::Model;
use super::smtlib::SMTSolver;

#[derive(Debug, Clone)]
pub struct VerificationCondition {
    model: Model
}

impl VerificationCondition {
    pub fn verify(&mut self, smtsolver: &mut SMTSolver) -> Result<(), CompileErr> {
        smtsolver.prepare_smt();
        let output = smtsolver.solve();
        todo!();
    }
}
