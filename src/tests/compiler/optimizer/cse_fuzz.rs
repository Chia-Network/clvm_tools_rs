use num_bigint::ToBigInt;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::compiler::clvm::{convert_from_clvm_rs, run};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts, DefconstData, DefunData, HelperForm};
use crate::compiler::dialect::AcceptedDialect;
use crate::compiler::frontend::compile_helperform;
use crate::compiler::fuzz::{ExprModifier, FuzzGenerator, FuzzTypeParams, Rule};
use crate::compiler::prims::primquote;
use crate::compiler::sexp::{decode_string, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

use crate::tests::compiler::fuzz::{compose_sexp, GenError, perform_compile_of_file};

fn simple_run(opts: Rc<dyn CompilerOpts>, expr: Rc<SExp>, env: Rc<SExp>) -> Result<Rc<SExp>, CompileErr> {
    let mut allocator = Allocator::new();
    let runner: Rc<dyn TRunProgram> = Rc::new(DefaultProgramRunner::new());
    Ok(run(
        &mut allocator,
        runner,
        opts.prim_map(),
        expr,
        env,
        None,
        None
    )?)
}

#[derive(Debug, Clone)]
enum SupportedOperators {
    Plus,
    Minus,
}

impl SupportedOperators {
    fn to_sexp(&self, srcloc: &Srcloc) -> Rc<SExp> {
        match self {
            SupportedOperators::Plus => compose_sexp(srcloc.clone(), "16"),
            SupportedOperators::Minus => compose_sexp(srcloc.clone(), "17")
        }
    }
}

#[derive(Debug, Clone)]
enum ValueSpecification {
    ConstantValue(Rc<SExp>),
    ConstantRef(Vec<u8>),
    ClvmBinop(SupportedOperators, Rc<ValueSpecification>, Rc<ValueSpecification>),
}

impl ValueSpecification {
    fn to_sexp(&self, srcloc: &Srcloc) -> Rc<SExp> {
        match self {
            ValueSpecification::ConstantValue(c) => {
                c.clone()
            }
            ValueSpecification::ConstantRef(c) => {
                Rc::new(SExp::Atom(srcloc.clone(), c.clone()))
            }
            ValueSpecification::ClvmBinop(op, left, right) => {
                Rc::new(SExp::Cons(
                    srcloc.clone(),
                    op.to_sexp(srcloc),
                    Rc::new(SExp::Cons(
                        srcloc.clone(),
                        left.to_sexp(srcloc),
                        Rc::new(SExp::Cons(
                            srcloc.clone(),
                            right.to_sexp(srcloc),
                            Rc::new(SExp::Nil(srcloc.clone()))
                        ))
                    ))
                ))
            }
        }
    }

    fn interpret(&self, opts: Rc<dyn CompilerOpts>, srcloc: &Srcloc, value_map: &BTreeMap<Vec<u8>, Rc<SExp>>, hash_map: &BTreeMap<Vec<u8>, Vec<u8>>) -> Rc<SExp> {
        match self {
            ValueSpecification::ConstantValue(c) => c.clone(),
            ValueSpecification::ConstantRef(c) => {
                if let Some(value) = value_map.get(c) {
                    value.clone()
                } else {
                    todo!();
                }
            }
            ValueSpecification::ClvmBinop(op, left, right) => {
                let operator = op.to_sexp(srcloc);
                let left_val = left.interpret(opts.clone(), srcloc, value_map, hash_map);
                let right_val = right.interpret(opts.clone(), srcloc, value_map, hash_map);
                let nil = Rc::new(SExp::Nil(srcloc.clone()));
                let expr = Rc::new(SExp::Cons(
                    srcloc.clone(),
                    operator,
                    Rc::new(SExp::Cons(
                        srcloc.clone(),
                        Rc::new(primquote(srcloc.clone(), left_val)),
                        Rc::new(SExp::Cons(
                            srcloc.clone(),
                            Rc::new(primquote(srcloc.clone(), right_val)),
                            nil.clone()
                        ))
                    ))
                ));
                simple_run(opts, expr, nil).expect("should succeed")
            }
        }
    }
}

struct ModuleConstantExpectation {
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
}
impl ModuleConstantExpectation {
    fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        ModuleConstantExpectation {
            opts,
            loc: Srcloc::start("*constant-test*"),
        }
    }

    fn loc(&self) -> Srcloc {
        self.loc.clone()
    }
}

struct FuzzT { }
impl FuzzTypeParams for FuzzT {
    type Tag = Vec<u8>;
    type Expr = Rc<SExp>;
    type Error = GenError;
    type State = ModuleConstantExpectation;
}

struct TestModuleConstantFuzzTopRule { defs: usize }
impl TestModuleConstantFuzzTopRule {
    fn new(defs: usize) -> Self {
        TestModuleConstantFuzzTopRule { defs }
    }
}

impl Rule<FuzzT> for TestModuleConstantFuzzTopRule {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        if tag != b"top" {
            return Ok(None);
        }

        let start_program = compose_sexp(state.loc(), &format!("(mod (X) (include *standard-cl-23*) (assign . ${{assign-test-form:{}}}))", idx));
        Ok(Some(start_program.clone()))
    }
}

#[test]
fn test_property_fuzz_cse_binding() {
    let mut rng = ChaCha8Rng::from_seed([
        1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,
        2,2,2,2,2,2,2,2,
        2,2,2,2,2,2,2,2,
    ]);

    let srcloc = Srcloc::start("*value*");
    let one = Rc::new(SExp::Integer(srcloc.clone(), bi_one()));

    let rules: Vec<Rc<dyn Rule<FuzzT>>> = vec![
    //     Rc::new(TestModuleConstantFuzzTopRule::new(false)),
    //     Rc::new(TestModuleConstantFuzzTopRule::new(true)),
    //     Rc::new(TestModuleConstantFuzzConstantBodyRule::new()),
    //     Rc::new(TestModuleConstantNew { }),
    //     Rc::new(TestModuleConstantFuzzMoreConstants { want_more: true }),
    //     Rc::new(TestModuleConstantFuzzMoreConstants { want_more: false }),
    //     Rc::new(TestModuleConstantFuzzExports {}),
    //     Rc::new(TestModuleConstantFuzzApplyOperation { op: SupportedOperators::Plus, other_value: one.clone() }),
    //     Rc::new(TestModuleConstantFuzzApplyOperation { op: SupportedOperators::Minus, other_value: one.clone() }),
    //     Rc::new(TestModuleConstantMoreFunctions {}),
    //     Rc::new(TestModuleConstantFunctionOrConstant { function: false }),
    //     Rc::new(TestModuleConstantFunctionOrConstant { function: true }),
    //     Rc::new(TestModuleConstantTerminateFunctionBody {}),
    //     Rc::new(TestModuleConstantTerminateProgramTail {}),
    //     Rc::new(TestModuleConstantBasedOnFunctionHash {}),
    ];
    let top_node = Rc::new(SExp::Atom(srcloc.clone(), b"${0:top}".to_vec()));

    for _ in 0..30 {
        let mut fuzzgen = FuzzGenerator::new(top_node.clone(), &rules);
        let mut idx = 0;
        let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*test*"));
        let mut mc = ModuleConstantExpectation::new(opts.set_dialect(AcceptedDialect {
            stepping: Some(23),
            strict: true,
        }).set_optimize(true));
        while fuzzgen.expand(&mut mc, idx > 15, &mut rng).expect("should expand") {
            idx += 1;
            assert!(idx < 100);
        }

        let forms =
            if let Some(flist) = fuzzgen.result().proper_list() {
                flist
            } else {
                todo!();
            };

        let program_text = forms.iter().map(|f| f.to_string()).collect::<Vec<String>>().join("\n");
        eprintln!("program_text\n{program_text}");
        let mut allocator = Allocator::new();
        let runner = Rc::new(DefaultProgramRunner::new());
        let compiled = perform_compile_of_file(
            &mut allocator,
            runner.clone(),
            "test.clsp",
            &program_text,
        ).expect("should compile");

        // Collect output values from compiled.
        let nil = Rc::new(SExp::Nil(compiled.compiled.loc()));
        let run_result = simple_run(opts.clone(), compiled.compiled.clone(), nil).expect("should run");
        eprintln!("run_result {run_result}");
        todo!();
    }

    // We've checked all predicted values.
}
