use num_bigint::ToBigInt;

use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::borrow::Borrow;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Debug;
use std::rc::Rc;

use clvmr::Allocator;

use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::compiler::clvm::run;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts};
use crate::compiler::fuzz::{ExprModifier, FuzzChoice, FuzzGenerator, FuzzTypeParams, Rule};
use crate::compiler::prims::primquote;
use crate::compiler::sexp::{enlist, extract_atom_replacement, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Debug)]
pub struct GenError {
    pub message: String,
}
impl From<&str> for GenError {
    fn from(m: &str) -> GenError {
        GenError {
            message: m.to_string(),
        }
    }
}

pub fn compose_sexp(loc: Srcloc, s: &str) -> Rc<SExp> {
    parse_sexp(loc, s.bytes()).expect("should parse")[0].clone()
}

pub fn simple_run(
    opts: Rc<dyn CompilerOpts>,
    expr: Rc<SExp>,
    env: Rc<SExp>,
) -> Result<Rc<SExp>, CompileErr> {
    let mut allocator = Allocator::new();
    let runner: Rc<dyn TRunProgram> = Rc::new(DefaultProgramRunner::new());
    Ok(run(
        &mut allocator,
        runner,
        opts.prim_map(),
        expr,
        env,
        None,
        None,
    )?)
}

pub fn simple_seeded_rng(seed: u32) -> ChaCha8Rng {
    let mut seed_data: [u8; 32] = [1; 32];
    for i in 16..28 {
        seed_data[i] = 2;
    }
    seed_data[28] = ((seed >> 24) & 0xff) as u8;
    seed_data[29] = ((seed >> 16) & 0xff) as u8;
    seed_data[30] = ((seed >> 8) & 0xff) as u8;
    seed_data[31] = (seed & 0xff) as u8;
    ChaCha8Rng::from_seed(seed_data)
}

// A generic, simple representation of expressions that allow us to evaluate
// simple expressions.  We can add stuff that increases this capability for
// all consumers.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SupportedOperators {
    Plus,
    Minus,
    Times,
}

impl SupportedOperators {
    pub fn to_int(&self) -> usize {
        match self {
            SupportedOperators::Plus => 16,
            SupportedOperators::Minus => 17,
            SupportedOperators::Times => 18,
        }
    }
    pub fn to_sexp(&self, srcloc: &Srcloc) -> SExp {
        SExp::Integer(srcloc.clone(), self.to_int().to_bigint().unwrap())
    }

    pub fn to_bodyform(&self, srcloc: &Srcloc) -> BodyForm {
        BodyForm::Value(self.to_sexp(srcloc))
    }
}

impl Distribution<SupportedOperators> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> SupportedOperators {
        match rng.gen::<u8>() % 3 {
            0 => SupportedOperators::Plus,
            1 => SupportedOperators::Minus,
            _ => SupportedOperators::Times,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValueSpecification {
    ConstantValue(Rc<SExp>),
    VarRef(Vec<u8>),
    ClvmBinop(
        SupportedOperators,
        Rc<ValueSpecification>,
        Rc<ValueSpecification>,
    ),
}

pub trait HasVariableStore {
    fn get(&self, name: &[u8]) -> Option<Rc<ValueSpecification>>;
}

impl ValueSpecification {
    pub fn to_sexp(&self, srcloc: &Srcloc) -> SExp {
        match self {
            ValueSpecification::ConstantValue(c) => {
                let c_borrowed: &SExp = c.borrow();
                c_borrowed.clone()
            }
            ValueSpecification::VarRef(c) => SExp::Atom(srcloc.clone(), c.clone()),
            ValueSpecification::ClvmBinop(op, left, right) => enlist(
                srcloc.clone(),
                &[
                    Rc::new(op.to_sexp(srcloc)),
                    Rc::new(left.to_sexp(srcloc)),
                    Rc::new(right.to_sexp(srcloc)),
                ],
            ),
        }
    }

    pub fn to_bodyform(&self, srcloc: &Srcloc) -> BodyForm {
        match self {
            ValueSpecification::ClvmBinop(op, left, right) => BodyForm::Call(
                srcloc.clone(),
                vec![
                    Rc::new(op.to_bodyform(srcloc)),
                    Rc::new(left.to_bodyform(srcloc)),
                    Rc::new(right.to_bodyform(srcloc)),
                ],
                None,
            ),
            ValueSpecification::ConstantValue(v) => {
                let borrowed_sexp: &SExp = v.borrow();
                BodyForm::Quoted(borrowed_sexp.clone())
            }
            ValueSpecification::VarRef(v) => {
                BodyForm::Value(SExp::Atom(srcloc.clone(), v.to_vec()))
            }
        }
    }

    pub fn get_free_vars<'a>(&'a self) -> BTreeSet<Vec<u8>> {
        let mut stack = vec![Rc::new(self.clone())];
        let mut result = BTreeSet::default();

        while let Some(v) = stack.pop() {
            match v.borrow() {
                ValueSpecification::VarRef(c) => {
                    result.insert(c.clone());
                }
                ValueSpecification::ClvmBinop(_, l, r) => {
                    stack.push(l.clone());
                    stack.push(r.clone());
                }
                _ => {}
            }
        }

        result
    }

    pub fn interpret<Store: HasVariableStore>(
        &self,
        opts: Rc<dyn CompilerOpts>,
        srcloc: &Srcloc,
        value_map: &Store,
    ) -> Rc<SExp> {
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
                    Rc::new(operator),
                    Rc::new(SExp::Cons(
                        srcloc.clone(),
                        Rc::new(primquote(srcloc.clone(), left_val)),
                        Rc::new(SExp::Cons(
                            srcloc.clone(),
                            Rc::new(primquote(srcloc.clone(), right_val)),
                            nil.clone(),
                        )),
                    )),
                ));
                simple_run(opts, expr, nil).expect("should succeed")
            }
        }
    }
}

//
// Fuzzing support for ValueSpecification alone.
// Provided for testing the fuzzer itself and maybe future use in tests.
//
fn find_in_structure_inner(
    parents: &mut Vec<Rc<ValueSpecification>>,
    structure: Rc<ValueSpecification>,
    target: &Rc<ValueSpecification>,
) -> bool {
    if let ValueSpecification::ClvmBinop(_, l, r) = structure.borrow() {
        parents.push(structure.clone());
        if find_in_structure_inner(parents, l.clone(), target) {
            return true;
        }
        if find_in_structure_inner(parents, r.clone(), target) {
            return true;
        }

        parents.pop();
    }

    structure == *target
}

impl ExprModifier for Rc<ValueSpecification> {
    type Tag = Vec<u8>;
    type Expr = Rc<ValueSpecification>;

    /// Add identified in-progress expansions into waiters.
    /// These are used as expansion candidates during each step of generation.
    /// Each will be tried in a random order with all rules in a random order until
    /// one of the rules returns a replacement.
    fn find_waiters(&self, waiters: &mut Vec<FuzzChoice<Self::Expr, Self::Tag>>) {
        match self.borrow() {
            ValueSpecification::VarRef(v) => {
                if v.starts_with(b"${") && v.ends_with(b"}") {
                    if let Some(r) = extract_atom_replacement(self, v) {
                        waiters.push(r);
                    }
                }
            }
            ValueSpecification::ClvmBinop(_, l, r) => {
                l.find_waiters(waiters);
                r.find_waiters(waiters);
            }
            _ => {}
        }
    }

    /// Replace a value where it appears in the structure with a new value.
    fn replace_node(&self, to_replace: &Self::Expr, new_value: Self::Expr) -> Self::Expr {
        if let ValueSpecification::ClvmBinop(op, l, r) = self.borrow() {
            let new_l = l.replace_node(to_replace, new_value.clone());
            let new_r = r.replace_node(to_replace, new_value.clone());
            if Rc::as_ptr(&new_l) != Rc::as_ptr(l) || Rc::as_ptr(&new_r) != Rc::as_ptr(r) {
                return Rc::new(ValueSpecification::ClvmBinop(op.clone(), new_l, new_r));
            }
        }

        if self == to_replace {
            return new_value;
        }

        self.clone()
    }

    /// Find the expression in the target structure and give the path down to it
    /// expressed as a snapshot of the traversed nodes.
    fn find_in_structure(&self, target: &Self::Expr) -> Option<Vec<Self::Expr>> {
        let mut parents = Vec::new();
        if find_in_structure_inner(&mut parents, self.clone(), target) {
            Some(parents)
        } else {
            None
        }
    }
}

struct SimpleFuzzItselfTestState {
    srcloc: Srcloc,
    used_vars: HashMap<Vec<u8>, Rc<ValueSpecification>>,
}

impl HasVariableStore for SimpleFuzzItselfTestState {
    fn get(&self, name: &[u8]) -> Option<Rc<ValueSpecification>> {
        self.used_vars.get(name).cloned()
    }
}

struct SimpleFuzzItselfTest;
impl FuzzTypeParams for SimpleFuzzItselfTest {
    type Tag = Vec<u8>;
    type Expr = Rc<ValueSpecification>;
    type Error = String;
    type State = SimpleFuzzItselfTestState;
}

struct SimpleRuleVar;
impl Rule<SimpleFuzzItselfTest> for SimpleRuleVar {
    fn check(
        &self,
        state: &mut SimpleFuzzItselfTestState,
        _tag: &Vec<u8>,
        _idx: usize,
        _terminate: bool,
        _parents: &[Rc<ValueSpecification>],
    ) -> Result<Option<Rc<ValueSpecification>>, String> {
        let n = 1 + state.used_vars.len();
        // Set each v<n> = n
        let v1 = format!("v{n}").as_bytes().to_vec();
        state.used_vars.insert(
            v1.clone(),
            Rc::new(ValueSpecification::ConstantValue(Rc::new(SExp::Atom(
                state.srcloc.clone(),
                vec![n as u8],
            )))),
        );
        Ok(Some(Rc::new(ValueSpecification::VarRef(v1))))
    }
}

struct SimpleRuleOp {
    op: SupportedOperators,
}
impl Rule<SimpleFuzzItselfTest> for SimpleRuleOp {
    fn check(
        &self,
        _state: &mut SimpleFuzzItselfTestState,
        _tag: &Vec<u8>,
        idx: usize,
        terminate: bool,
        _parents: &[Rc<ValueSpecification>],
    ) -> Result<Option<Rc<ValueSpecification>>, String> {
        if terminate {
            return Ok(None);
        }

        let l = format!("${{{idx}:expand}}").as_bytes().to_vec();
        let r = format!("${{{}:expand}}", idx + 1).as_bytes().to_vec();

        Ok(Some(Rc::new(ValueSpecification::ClvmBinop(
            self.op.clone(),
            Rc::new(ValueSpecification::VarRef(l)),
            Rc::new(ValueSpecification::VarRef(r)),
        ))))
    }
}

#[test]
fn test_compose_sexp() {
    let loc = Srcloc::start("*vstest*");
    assert_eq!(
        compose_sexp(loc.clone(), "(hi . there)"),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Atom(loc.clone(), b"hi".to_vec())),
            Rc::new(SExp::Atom(loc.clone(), b"there".to_vec()))
        ))
    );
}

#[test]
fn test_random_value_spec() {
    let mut rng = simple_seeded_rng(11);
    let mut state = SimpleFuzzItselfTestState {
        srcloc: Srcloc::start("*vstest*"),
        used_vars: HashMap::default(),
    };
    let topnode = Rc::new(ValueSpecification::VarRef(b"${0:top}".to_vec()));
    let rules: Vec<Rc<dyn Rule<SimpleFuzzItselfTest>>> = vec![
        Rc::new(SimpleRuleVar),
        Rc::new(SimpleRuleOp {
            op: SupportedOperators::Plus,
        }),
        Rc::new(SimpleRuleOp {
            op: SupportedOperators::Times,
        }),
    ];
    let mut fuzzer = FuzzGenerator::new(topnode, &rules);

    let mut idx = 0;
    while let Ok(true) = fuzzer.expand(&mut state, idx > 5, &mut rng) {
        // Repeat
        idx += 1;
    }

    assert_eq!(
        fuzzer.result().to_sexp(&state.srcloc).to_string(),
        "(16 (16 (18 v4 (16 v3 v6)) v5) (18 v7 (18 v1 v2)))"
    );
    // Since each v<n> = n, the expression comes down to
    // (+ (+ (* 4 (+ 3 6)) 5) (* 7 (* 1 2))) = 55
    let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*vstest*"));
    assert_eq!(
        fuzzer
            .result()
            .interpret(opts, &state.srcloc, &state)
            .to_string(),
        "55"
    );
}
