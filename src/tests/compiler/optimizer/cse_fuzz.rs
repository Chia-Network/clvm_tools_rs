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
use crate::compiler::sexp::{AtomValue, decode_string, parse_sexp, NodeSel, SelectNode, SExp, ThisNode};
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
    Times,
}

impl SupportedOperators {
    fn to_sexp(&self, srcloc: &Srcloc) -> Rc<SExp> {
        match self {
            SupportedOperators::Plus => compose_sexp(srcloc.clone(), "16"),
            SupportedOperators::Minus => compose_sexp(srcloc.clone(), "17"),
            SupportedOperators::Times => compose_sexp(srcloc.clone(), "18")
        }
    }
}

#[derive(Debug, Clone)]
enum ValueSpecification {
    ConstantValue(Rc<SExp>),
    VarRef(Vec<u8>),
    ClvmBinop(SupportedOperators, Rc<ValueSpecification>, Rc<ValueSpecification>),
}

impl ValueSpecification {
    fn to_sexp(&self, srcloc: &Srcloc) -> Rc<SExp> {
        match self {
            ValueSpecification::ConstantValue(c) => {
                c.clone()
            }
            ValueSpecification::VarRef(c) => {
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

    fn interpret(&self, opts: Rc<dyn CompilerOpts>, srcloc: &Srcloc, value_map: &BTreeMap<Vec<u8>, Rc<ValueSpecification>>) -> Rc<SExp> {
        match self {
            ValueSpecification::ConstantValue(c) => c.clone(),
            ValueSpecification::VarRef(c) => {
                if let Some(value) = value_map.get(c) {
                    value.interpret(opts, srcloc, value_map)
                } else {
                    todo!();
                }
            }
            ValueSpecification::ClvmBinop(op, left, right) => {
                let operator = op.to_sexp(srcloc);
                let left_val = left.interpret(opts.clone(), srcloc, value_map);
                let right_val = right.interpret(opts.clone(), srcloc, value_map);
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

struct TrickyAssignExpectation {
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
    count: usize,
    actions: usize,
    final_var: Option<Rc<ValueSpecification>>,
    var_defs: BTreeMap<Vec<u8>, Rc<ValueSpecification>>,
}
impl TrickyAssignExpectation {
    fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        TrickyAssignExpectation {
            opts,
            loc: Srcloc::start("*constant-test*"),
            count: 0,
            actions: 0,
            final_var: None,
            var_defs: BTreeMap::default(),
        }
    }

    fn loc(&self) -> Srcloc {
        self.loc.clone()
    }

    fn compute(&self) -> Rc<SExp> {
        let val = self.final_var.as_ref().unwrap();
        val.interpret(
            self.opts.clone(),
            &self.loc,
            &self.var_defs
        )
    }
}

struct FuzzT { }
impl FuzzTypeParams for FuzzT {
    type Tag = Vec<u8>;
    type Expr = Rc<SExp>;
    type Error = GenError;
    type State = TrickyAssignExpectation;
}

struct TestTrickyAssignFuzzTopRule { defs: usize }
impl Rule<FuzzT> for TestTrickyAssignFuzzTopRule {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"top" {
            return Ok(None);
        }

        state.count = self.defs;
        let start_program = compose_sexp(state.loc(), &format!("(mod (X) (include *standard-cl-23*) (defun F (X) (assign . ${{{}:assign-test-form}})) (F X))", idx));
        Ok(Some(start_program.clone()))
    }
}

struct TestTrickyAssignFuzzTestFormRule { }
impl Rule<FuzzT> for TestTrickyAssignFuzzTestFormRule {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"assign-test-form" {
            return Ok(None);
        }

        if state.count > 0 {
            let varname = format!("v{}", state.count);
            state.count -= 1;
            Ok(Some(compose_sexp(state.loc(), &format!("({varname} ${{{idx}:vardef}} . ${{{}:assign-test-form}})", idx + 1))))
        } else {
            Ok(Some(compose_sexp(state.loc(), &format!("${{{idx}:final-expr}}"))))
        }
    }
}

fn find_var_name_in_heritage(heritage: &[Rc<SExp>]) -> Vec<u8> {
    let NodeSel::Cons((varloc, varname), _) = NodeSel::Cons(AtomValue::Here(()), ThisNode).select_nodes(heritage[heritage.len() - 2].clone()).unwrap();
    varname.clone()
}

struct TestTrickyAssignVarDefConstantRule { value: Rc<SExp> }
impl Rule<FuzzT> for TestTrickyAssignVarDefConstantRule {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"vardef" || heritage.len() < 3 {
            return Ok(None);
        }

        state.actions += 13;
        let my_name = find_var_name_in_heritage(heritage);

        let spec = Rc::new(ValueSpecification::ConstantValue(self.value.clone()));
        state.var_defs.insert(my_name.clone(), spec);
        Ok(Some(self.value.clone()))
    }
}

struct TestTrickyAssignVarDefBinopRule { op: SupportedOperators, other: Rc<SExp> }
impl Rule<FuzzT> for TestTrickyAssignVarDefBinopRule {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"vardef" || state.var_defs.is_empty() || heritage.len() < 3 {
            return Ok(None);
        }

        let my_name = find_var_name_in_heritage(heritage);

        // We'll choose one other value and compose with the existing value.
        let to_skip = state.actions % state.var_defs.len();
        let (k, _) = state.var_defs.iter().skip(to_skip).next().unwrap();
        let my_value = Rc::new(ValueSpecification::VarRef(k.to_vec()));

        state.actions += 13;

        let spec = Rc::new(ValueSpecification::ClvmBinop(self.op.clone(), Rc::new(ValueSpecification::ConstantValue(self.other.clone())), my_value));
        state.var_defs.insert(my_name.clone(), spec.clone());
        Ok(Some(spec.to_sexp(&state.loc)))
    }
}

struct TestTrickyAssignFinalExpr { }
impl Rule <FuzzT> for TestTrickyAssignFinalExpr {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"final-expr" || state.var_defs.is_empty() {
            return Ok(None);
        }

        let to_skip = state.actions % state.var_defs.len();
        let (k, _) = state.var_defs.iter().skip(to_skip).next().unwrap();
        state.final_var = Some(Rc::new(ValueSpecification::VarRef(k.to_vec())));
        Ok(Some(Rc::new(SExp::Cons(state.loc.clone(), Rc::new(SExp::Atom(state.loc.clone(), k.to_vec())), Rc::new(SExp::Nil(state.loc.clone()))))))
    }
}

struct TestTrickyAssignFinalBinopRule { op: SupportedOperators, other: Rc<SExp> }
impl Rule <FuzzT> for TestTrickyAssignFinalBinopRule {
    fn check(&self, state: &mut TrickyAssignExpectation, tag: &Vec<u8>, idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Result<Option<Rc<SExp>>,GenError> {
        if tag != b"final-expr" || state.var_defs.is_empty() {
            return Ok(None);
        }

        let to_skip = state.actions % state.var_defs.len();
        let (k, _) = state.var_defs.iter().skip(to_skip).next().unwrap();
        let result_expr = Rc::new(ValueSpecification::ClvmBinop(self.op.clone(), Rc::new(ValueSpecification::ConstantValue(self.other.clone())), Rc::new(ValueSpecification::VarRef(k.to_vec()))));
        state.final_var = Some(result_expr.clone());
        Ok(Some(Rc::new(SExp::Cons(state.loc.clone(), result_expr.to_sexp(&state.loc), Rc::new(SExp::Nil(state.loc.clone()))))))
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
    let two = Rc::new(SExp::Integer(srcloc.clone(), 2_u32.to_bigint().unwrap()));

    let rules: Vec<Rc<dyn Rule<FuzzT>>> = vec![
        Rc::new(TestTrickyAssignFuzzTopRule { defs: 1 }),
        Rc::new(TestTrickyAssignFuzzTopRule { defs: 2 }),
        Rc::new(TestTrickyAssignFuzzTopRule { defs: 3 }),
        Rc::new(TestTrickyAssignFuzzTopRule { defs: 4 }),
        Rc::new(TestTrickyAssignFuzzTopRule { defs: 5 }),
        Rc::new(TestTrickyAssignFuzzTestFormRule { }),
        Rc::new(TestTrickyAssignVarDefConstantRule {
            value: compose_sexp(srcloc.clone(), "1")
        }),
        Rc::new(TestTrickyAssignVarDefBinopRule {
            op: SupportedOperators::Times,
            other: two.clone()
        }),
        Rc::new(TestTrickyAssignFinalExpr { }),
        Rc::new(TestTrickyAssignFinalBinopRule {
            op: SupportedOperators::Times,
            other: two.clone()
        }),
    ];
    let top_node = Rc::new(SExp::Atom(srcloc.clone(), b"${0:top}".to_vec()));

    for _ in 0..500 {
        let mut fuzzgen = FuzzGenerator::new(top_node.clone(), &rules);
        let mut idx = 0;
        let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*test*"));
        let mut mc = TrickyAssignExpectation::new(opts.set_dialect(AcceptedDialect {
            stepping: Some(23),
            strict: true,
        }).set_optimize(true));
        while fuzzgen.expand(&mut mc, idx > 20, &mut rng).expect("should expand") {
            idx += 1;
            assert!(idx < 100);
        }

        let mut allocator = Allocator::new();
        let runner = Rc::new(DefaultProgramRunner::new());
        let program_text = fuzzgen.result().to_string();
        eprintln!("program_text {program_text}");
        let compiled = perform_compile_of_file(
            &mut allocator,
            runner.clone(),
            "test.clsp",
            &program_text,
        ).expect("should compile");

        // Collect output values from compiled.
        let arg = compose_sexp(srcloc.clone(), "(3)");
        let run_result = simple_run(opts.clone(), compiled.compiled.clone(), arg).expect("should run");
        let want_result = mc.compute();
        eprintln!("run_result {run_result} have {want_result}");
        assert_eq!(run_result, want_result);
    }

    // We've checked all predicted values.
}
