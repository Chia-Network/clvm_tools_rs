use num_bigint::ToBigInt;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Error;
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
use crate::compiler::sexp::{AtomValue, decode_string, enlist, parse_sexp, NodeSel, SelectNode, SExp, ThisNode};
use crate::compiler::srcloc::Srcloc;

use crate::tests::compiler::fuzz::{compose_sexp, GenError, HasVariableStore, perform_compile_of_file, PropertyTest, PropertyTestState, simple_run, simple_seeded_rng, SupportedOperators, ValueSpecification};

fn create_variable_set(srcloc: Srcloc, vars: usize) -> BTreeSet<Vec<u8>> {
    (0..vars).map(|n| format!("v{n}").bytes().collect()).collect()
}

struct AssignExprData {
    bindings: BTreeMap<Vec<u8>, Rc<ComplexAssignExpression>>,
    body: Rc<ComplexAssignExpression>
}

enum ComplexAssignExpression {
    Assign(Rc<AssignExprData>),
    Simple(Rc<ValueSpecification>)
}

struct ExprCreationFuzzT { }
impl FuzzTypeParams for ExprCreationFuzzT {
    type Tag = Vec<u8>;
    type Expr = Rc<SExp>;
    type Error = GenError;
    type State = ExprCreationState;
}

#[derive(Default, Clone)]
struct ExprVariableUsage {
    toplevel: BTreeSet<Vec<u8>>,
    bindings: BTreeMap<Vec<u8>, Vec<Vec<u8>>>
}

impl ExprVariableUsage {
    fn fmtvar(&self, writer: &mut std::fmt::Formatter<'_>, lvl: usize, v: &[u8]) -> Result<(), std::fmt::Error> {
        for i in 0..(2*lvl) {
            write!(writer, " ")?;
        }
        writeln!(writer, "{}:", decode_string(v));
        if let Some(children) = self.bindings.get(v) {
            for c in children.iter() {
                self.fmtvar(writer, lvl + 1, c)?;
            }
        }

        Ok(())
    }

    // Find the parent of this var.
    fn find_parent_of_var<'a>(&'a self, var: &[u8]) -> Option<&'a Vec<u8>> {
        for (parent, bindings) in self.bindings.iter() {
                if bindings.iter().any(|c| c == var) {
                    return Some(parent);
                }
        }

        None
    }

    // Find the path to this var.
    fn find_path_to_var<'a>(&'a self, var: &[u8]) -> Vec<&'a Vec<u8>> {
        let mut result = Vec::new();
        let mut checking = var;
        while let Some(parent) = self.find_parent_of_var(checking) {
            checking = parent;
            result.push(parent);
        }
        result
    }

    // Give the set of variables in scope for the definition of var.
    fn variables_in_scope<'a>(&'a self, var: &[u8]) -> Vec<&'a Vec<u8>> {
        // If this variable itself use an assign form as its definition, then
        // all the innermost bindings are in scope.
        let mut result = self.bindings.get(var).map(|v| {
            v.iter().map(|e| &(*e)).collect()
        }).unwrap_or_else(|| vec![]);

        // Get the parents of var.
        let parents = self.find_path_to_var(var);

        // If there are no parents, then the variables in scope are the toplevel
        // ones that appear before var.
        let mut from_scopes =
            if parents.is_empty() {
                self.toplevel.iter().take_while(|t| *t != var).map(|t| &(*t)).collect()
            } else {
                let mut scopes = Vec::new();
                let mut target = var;
                for p in parents.iter().rev() {
                    let p_borrowed: &[u8] = &p;
                    if let Some(children) = self.bindings.get(p_borrowed) {
                        let mut appear_before_in_parent: Vec<&'a Vec<u8>> = children.iter().take_while(|c| *c != target).map(|t| &(*t)).collect();
                        scopes.append(&mut appear_before_in_parent);
                        target = p;
                    }
                }
                scopes
            };

        // Add the visible toplevel definitions if they won
        result.append(&mut from_scopes);
        result
    }

    // Generate an expression to define one variable.
    fn generate_expression<R: Rng>(&self, srcloc: &Srcloc, wanted_complexity: usize, rng: &mut R, args: &[Vec<u8>], var: &[u8]) -> (Rc<ValueSpecification>, Rc<SExp>) {
        let mut in_scope: Vec<&Vec<u8>> = args.iter().collect();
        let mut assignments_in_scope = self.variables_in_scope(var);
        in_scope.append(&mut assignments_in_scope);

        let generate_constant = |rng: &mut R| {
            // Constant value
            let random_number: i8 = rng.gen();
            let sexp = Rc::new(SExp::Integer(srcloc.clone(), random_number.to_bigint().unwrap()));
            let definition = Rc::new(ValueSpecification::ConstantValue(sexp.clone()));
            (definition, sexp)
        };

        let generate_reference = |rng: &mut R| {
            let variable_choice: usize = rng.gen();
            let variable = in_scope[variable_choice % in_scope.len()].to_vec();
            let var_sexp = Rc::new(SExp::Atom(srcloc.clone(), variable.clone()));
            let reference = Rc::new(ValueSpecification::VarRef(variable.clone()));
            (reference, var_sexp)
        };

        let generate_simple = |rng: &mut R| {
            if in_scope.is_empty() || rng.gen() {
                generate_constant(rng)
            } else {
                generate_reference(rng)
            }
        };

        let (mut value, mut result) = generate_simple(rng);
        let complexity: usize = rng.gen();

        // Generate up to a certain number of operations.
        for i in 0..(complexity % wanted_complexity) {
            // Generate the other branch.
            let (other_value, other_sexp) = generate_simple(rng);

            // Generate a binop.
            let random_op: SupportedOperators = rng.gen();
            let (left_value, right_value, left_sexp, right_sexp) =
                if rng.gen() {
                    (value.clone(), other_value, result.clone(), other_sexp)
                } else {
                    (other_value, value.clone(), other_sexp, result.clone())
                };

            result = Rc::new(enlist(srcloc.clone(), &[
                random_op.to_sexp(&srcloc),
                left_sexp,
                right_sexp,
            ]));

            value = Rc::new(ValueSpecification::ClvmBinop(
                random_op,
                left_value,
                right_value
            ));
        }

        (value, result)
    }
}

#[test]
fn test_expr_variable_usage() {
    let srcloc = Srcloc::start("*test*");
    let mut rng = simple_seeded_rng(0x02020202);
    let vars = create_variable_set(srcloc.clone(), 5);
    let structure_graph = create_structure_from_variables(&mut rng, &vars);

    assert_eq!(
        format!("{structure_graph:?}"),
        indoc!{"
        v0:
          v4:
          v1:
        v2:
        v3:
        "});
    assert_eq!(structure_graph.find_parent_of_var(b"v1"), Some(&b"v0".to_vec()));
    assert_eq!(structure_graph.find_path_to_var(b"v1"), vec![b"v0"]);
    assert_eq!(structure_graph.variables_in_scope(b"v1"), vec![b"v4"]);
    assert_eq!(structure_graph.variables_in_scope(b"v0"), vec![b"v4", b"v1"]);
    assert_eq!(structure_graph.variables_in_scope(b"v3"), vec![b"v0", b"v2"]);
    let (v3, e3) = structure_graph.generate_expression(&srcloc, 5, &mut rng, &[b"a1".to_vec(), b"a2".to_vec()], b"v3");
    assert_eq!(e3.to_string(), "(18 (16 122 (17 a1 43)) -53)");
    assert_eq!(v3, Rc::new(ValueSpecification::ClvmBinop(
        SupportedOperators::Times,
        Rc::new(ValueSpecification::ClvmBinop(
            SupportedOperators::Plus,
            Rc::new(ValueSpecification::ConstantValue(
                Rc::new(SExp::Integer(srcloc.clone(), 122.to_bigint().unwrap()))
            )),
            Rc::new(ValueSpecification::ClvmBinop(
                SupportedOperators::Minus,
                Rc::new(ValueSpecification::VarRef(b"a1".to_vec())),
                Rc::new(ValueSpecification::ConstantValue(
                    Rc::new(SExp::Integer(srcloc.clone(), 43.to_bigint().unwrap()))
                ))
            )),
        )),
        Rc::new(ValueSpecification::ConstantValue(
            Rc::new(SExp::Integer(srcloc.clone(), -53.to_bigint().unwrap()))
        ))
    )));
    let (v1, e1) = structure_graph.generate_expression(&srcloc, 10, &mut rng, &[b"a1".to_vec()], b"v1");
    assert_eq!(e1.to_string(), "(16 v4 (16 (17 (17 (16 v4 v4) 29) 109) a1))");
    assert_eq!(v1, Rc::new(ValueSpecification::ClvmBinop(
        SupportedOperators::Plus,
        Rc::new(ValueSpecification::VarRef(b"v4".to_vec())),
        Rc::new(ValueSpecification::ClvmBinop(
            SupportedOperators::Plus,
            Rc::new(ValueSpecification::ClvmBinop(
                SupportedOperators::Minus,
                Rc::new(ValueSpecification::ClvmBinop(
                    SupportedOperators::Minus,
                    Rc::new(ValueSpecification::ClvmBinop(
                        SupportedOperators::Plus,
                        Rc::new(ValueSpecification::VarRef(b"v4".to_vec())),
                        Rc::new(ValueSpecification::VarRef(b"v4".to_vec()))
                    )),
                    Rc::new(ValueSpecification::ConstantValue(
                        Rc::new(SExp::Integer(srcloc.clone(), 29.to_bigint().unwrap()))
                    ))
                )),
                Rc::new(ValueSpecification::ConstantValue(
                    Rc::new(SExp::Integer(srcloc.clone(), 109.to_bigint().unwrap()))
                ))
            )),
            Rc::new(ValueSpecification::VarRef(b"a1".to_vec()))
        ))
    )));
}

impl Debug for ExprVariableUsage {
    fn fmt(&self, writer: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for t in self.toplevel.iter() {
            self.fmtvar(writer, 0, t)?;
        }
        Ok(())
    }
}

// Precompute dependency graph of inner variables?
//
// Map v -> list<v> where v appears once and never downstream of itself.
struct ExprCreationState {
    rng: ChaCha8Rng,
    structure_graph: ExprVariableUsage,
    start_variables: BTreeSet<Vec<u8>>,
    bindings: BTreeMap<Vec<u8>, Rc<ComplexAssignExpression>>,
}

fn create_structure_from_variables<R: Rng>(rng: &mut R, v: &BTreeSet<Vec<u8>>) -> ExprVariableUsage {
    let mut v_start = v.clone();
    let mut usage = ExprVariableUsage::default();

    while !v_start.is_empty() {
        // Choose a variable.
        let chosen_idx: usize = rng.gen();
        let chosen = v_start.iter().skip(chosen_idx % v_start.len()).next().cloned().unwrap();

        // Decide whether it's toplevel (we always choose one if there are
        // no toplevel choices.
        let coin_flip_toplevel: usize = rng.gen();
        if (usage.toplevel.is_empty() || (coin_flip_toplevel % 3) == 0) && usage.toplevel.len() < 5 {
            // if so, copy it to the toplevel set.
            usage.toplevel.insert(chosen.clone());
        } else {
            // otherwise, choose a key from result, add it there.
            let parent_idx: usize = rng.gen();
            let parent = usage.bindings.keys().skip(parent_idx % usage.bindings.len()).next().cloned().unwrap();
            if let Some(children) = usage.bindings.get_mut(&parent) {
                children.push(chosen.clone());
            }
        }

        // Remove the chosen var from v_start, add an empty entry to result.
        v_start.remove(&chosen);
        usage.bindings.insert(chosen, Vec::new());
    }

    usage
}

impl PropertyTestState<ExprCreationFuzzT> for ExprCreationState {
    fn new_state<R: Rng>(r: &mut R) -> Self {
        let srcloc = Srcloc::start("*cl23-pre-cse-merge-fix");
        let mut rng = simple_seeded_rng(0x02020202);
        let vars = create_variable_set(srcloc, 5);
        let structure_graph = create_structure_from_variables(&mut rng, &vars);

        ExprCreationState {
            rng: rng.clone(),
            start_variables: vars,
            structure_graph,
            bindings: BTreeMap::default(),
        }
    }
    fn examine(&self, result: &Rc<SExp>) {
        eprintln!("state: {}", result);
    }
}

struct ExprCreationGenerator {
    rules: Vec<Rc<dyn Rule<ExprCreationFuzzT>>>
}

struct TopExprBinopRule { op: SupportedOperators }
impl Rule<ExprCreationFuzzT> for TopExprBinopRule {
    fn check(
        &self,
        state: &mut <ExprCreationFuzzT as FuzzTypeParams>::State,
        tag: &<ExprCreationFuzzT as FuzzTypeParams>::Tag,
        idx: usize,
        terminate: bool,
        parents: &[<ExprCreationFuzzT as FuzzTypeParams>::Expr]
    ) -> Result<Option<<ExprCreationFuzzT as FuzzTypeParams>::Expr>, <ExprCreationFuzzT as FuzzTypeParams>::Error> {
        if tag != b"top" {
            return Ok(None);
        }

        todo!();
    }
}

impl ExprCreationGenerator {
    fn new() -> Self {
        // Make rules
        ExprCreationGenerator {
            rules: vec![
                Rc::new(TopExprBinopRule { op: SupportedOperators::Plus }),
            ]
        }
    }

    fn generate<R: Rng>(&self, rng: &mut R) -> (ExprCreationState, Rc<ComplexAssignExpression>) {
        let srcloc = Srcloc::start("*cl23-pre-cse-merge-fix");
        let generated = PropertyTest::generate::<R, ExprCreationState>(rng, compose_sexp(srcloc.clone(), "${0:top}"), &self.rules);
        todo!();
    }
}

#[test]
fn test_cse_merge_regression() {
    let mut rng = simple_seeded_rng(13);
    let eg = ExprCreationGenerator::new();
    let (state, expression) = eg.generate(&mut rng);
    todo!();
}

/*
struct TrickyAssignRegression {
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
    count: usize,
    actions: usize,
    final_var: Option<Rc<ValueSpecification>>,
    var_defs: BTreeMap<Vec<u8>, Rc<ValueSpecification>>,
}

impl HasVariableStore for TrickyAssignExpectation {
    fn get(&self, name: &[u8]) -> Option<Rc<ValueSpecification>> {
        self.var_defs.get(name).cloned()
    }
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
            self,
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

        state.actions += 13;
        let my_name = find_var_name_in_heritage(heritage);

        // We'll choose one other value and compose with the existing value.
        let to_skip = state.actions % state.var_defs.len();
        let (k, _) = state.var_defs.iter().skip(to_skip).next().unwrap();
        let my_value = Rc::new(ValueSpecification::VarRef(k.to_vec()));

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

impl PropertyTestState for TrickyAssignExpectation {
    fn new_state<R: Rng>(r: &mut R) -> Self {
        let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*test*"));
        TrickyAssignExpectation::new(opts.set_dialect(AcceptedDialect {
            stepping: Some(23),
            strict: true,
        }).set_optimize(true))
    }
    fn filename(&self) -> String {
        "*cl23-pre-cse-merge-fix-test.clsp".to_string()
    }
    fn run_args(&self) -> String { "(3)".to_string() }
    fn check(&self, run_result: Rc<SExp>) {
        let want_result = self.compute();
        eprintln!("run_result {run_result} have {want_result}");
        assert_eq!(run_result, want_result);
    }
}

#[test]
fn test_property_fuzz_cse_regression() {
    let srcloc = Srcloc::start("*value*");
    let mut rng = simple_seeded_rng(0x02020202);
    let test = PropertyTest {
        run_times: 500,
        run_cutoff: 100,
        run_expansion: 20,

        top_node: compose_sexp(srcloc.clone(), "${0:top}"),
        rules: vec![
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
                other: compose_sexp(srcloc.clone(), "2")
            }),
            Rc::new(TestTrickyAssignFinalExpr { }),
            Rc::new(TestTrickyAssignFinalBinopRule {
                op: SupportedOperators::Times,
                other: compose_sexp(srcloc, "2")
            }),
        ]
    };

    test.run(&mut rng);
}
*/
