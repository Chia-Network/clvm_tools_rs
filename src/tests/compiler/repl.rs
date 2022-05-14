use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompileErr;
use crate::compiler::repl::Repl;

fn test_repl_outcome<S>(
    inputs: Vec<S>
) -> Result<Option<String>, CompileErr> where
    S: ToString
{
    let mut allocator = Allocator::new();
    let mut res = Ok(None);
    let opts = Rc::new(DefaultCompilerOpts::new(&"*repl-test*".to_string()));
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut repl = Repl::new(opts, runner);

    for i in inputs.iter() {
        res = res.and_then(|_| {
            repl.process_line(&mut allocator, i.to_string())
        });
    }

    res.map(|r| r.map(|r| r.to_sexp().to_string()))
}

#[test]
fn test_basic_repl_constant() {
    assert_eq!(
        test_repl_outcome(vec![ "(defconstant CREATE_COIN 51)", "51" ]).unwrap().unwrap(),
        "(q . 51)"
    );
}
