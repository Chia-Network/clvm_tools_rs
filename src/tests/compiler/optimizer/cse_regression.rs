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
use crate::compiler::comptypes::{Binding, BindingPattern, BodyForm, CompileErr, CompileForm, CompilerOpts, DefconstData, DefunData, HelperForm, LetData, LetFormKind};
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

#[derive(Debug, Clone)]
struct GeneratedExpr {
    definition: Rc<ValueSpecification>,
    sexp: Rc<SExp>,
}

impl ExprVariableUsage {
    fn fmtvar(&self, writer: &mut std::fmt::Formatter<'_>, lvl: usize, v: &[u8]) -> Result<(), std::fmt::Error> {
        for i in 0..(2*lvl) {
            write!(writer, " ")?;
        }
        writeln!(writer, "{}:", decode_string(v))?;
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
    fn generate_expression<R: Rng>(&self, srcloc: &Srcloc, wanted_complexity: usize, rng: &mut R, args: &[Vec<u8>], var: &[u8]) -> GeneratedExpr {
        let mut in_scope: Vec<&Vec<u8>> = args.iter().collect();
        let mut assignments_in_scope = self.variables_in_scope(var);
        in_scope.append(&mut assignments_in_scope);

        let generate_constant = |rng: &mut R| {
            // Constant value
            let random_number: i8 = rng.gen();
            let sexp = Rc::new(SExp::Integer(srcloc.clone(), random_number.to_bigint().unwrap()));
            let definition = Rc::new(ValueSpecification::ConstantValue(sexp.clone()));
            GeneratedExpr {
                definition, sexp
            }
        };

        let generate_reference = |rng: &mut R| {
            let variable_choice: usize = rng.gen();
            let variable = in_scope[variable_choice % in_scope.len()].to_vec();
            let var_sexp = Rc::new(SExp::Atom(srcloc.clone(), variable.clone()));
            let reference = Rc::new(ValueSpecification::VarRef(variable.clone()));

            GeneratedExpr {
                definition: reference,
                sexp: var_sexp
            }
        };

        let generate_simple = |rng: &mut R| {
            if in_scope.is_empty() || rng.gen() {
                generate_constant(rng)
            } else {
                generate_reference(rng)
            }
        };

        let mut result = generate_simple(rng);
        let complexity: usize = rng.gen();

        // Generate up to a certain number of operations.
        for i in 0..(complexity % wanted_complexity) {
            // Generate the other branch.
            let other_result = generate_simple(rng);

            // Generate a binop.
            let random_op: SupportedOperators = rng.gen();
            let (left, right) =
                if rng.gen() {
                    (result, other_result)
                } else {
                    (other_result, result)
                };

            result = GeneratedExpr {
                sexp: Rc::new(enlist(srcloc.clone(), &[
                    Rc::new(random_op.to_sexp(&srcloc)),
                    left.sexp,
                    right.sexp,
                ])),
                definition: Rc::new(ValueSpecification::ClvmBinop(
                    random_op,
                    left.definition,
                    right.definition,
                ))
            };
        }

        result
    }

    // Create the assignments for the assign form.
    fn create_assign_form_for_var(&self, srcloc: &Srcloc, expressions: &BTreeMap<Vec<u8>, GeneratedExpr>, var: &[u8]) -> BodyForm {
        let bound_in_var = self.bindings.get(var).cloned().unwrap_or_else(|| vec![]);

        assert!(!bound_in_var.is_empty());

        let bindings: Vec<Rc<Binding>> = bound_in_var.iter().map(|bound_var| {
            let expr = expressions.get(var).unwrap();
            Rc::new(Binding {
                loc: srcloc.clone(),
                nl: srcloc.clone(),
                body: Rc::new(expr.definition.to_bodyform(srcloc)),
                pattern: BindingPattern::Complex(Rc::new(SExp::Atom(srcloc.clone(), bound_var.to_vec())))
            })
        }).collect();

        BodyForm::Let(LetFormKind::Assign, Box::new(LetData {
            kw: None,
            loc: srcloc.clone(),
            bindings,
            body: Rc::new(BodyForm::Value(SExp::Atom(srcloc.clone(), bound_in_var[bound_in_var.len()-1].clone()))),
            inline_hint: None
        }))
    }

    fn create_assign_form(&self, srcloc: &Srcloc, expressions: &BTreeMap<Vec<u8>, GeneratedExpr>) -> BodyForm {
        assert!(!self.toplevel.is_empty());
        let last_top = self.toplevel.iter().skip(self.toplevel.len()-1).next().unwrap();
        let bindings: Vec<Rc<Binding>> = self.toplevel.iter().map(|t| {
            let expr = expressions.get(t).unwrap();
            Rc::new(Binding {
                loc: srcloc.clone(),
                nl: srcloc.clone(),
                body: Rc::new(expr.definition.to_bodyform(srcloc)),
                pattern: BindingPattern::Complex(Rc::new(SExp::Atom(srcloc.clone(), t.clone())))
            })
        }).collect();

        BodyForm::Let(LetFormKind::Assign, Box::new(LetData {
            loc: srcloc.clone(),
            kw: None,
            bindings,
            inline_hint: None,
            body: Rc::new(BodyForm::Value(SExp::Atom(srcloc.clone(), last_top.clone())))
        }))
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
    let g3 = structure_graph.generate_expression(&srcloc, 5, &mut rng, &[b"a1".to_vec(), b"a2".to_vec()], b"v3");
    assert_eq!(g3.sexp.to_string(), "(18 (16 122 (17 a1 43)) -53)");
    assert_eq!(g3.definition, Rc::new(ValueSpecification::ClvmBinop(
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
    let g1 = structure_graph.generate_expression(&srcloc, 10, &mut rng, &[b"a1".to_vec()], b"v1");
    assert_eq!(g1.sexp.to_string(), "(16 v4 (16 (17 (17 (16 v4 v4) 29) 109) a1))");
    assert_eq!(g1.definition, Rc::new(ValueSpecification::ClvmBinop(
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
    let free_vars: Vec<Vec<u8>> = g1.definition.get_free_vars().into_iter().collect();
    assert_eq!(free_vars, vec![b"a1".to_vec(), b"v4".to_vec()]);
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

// Produce a program that provides a valid regression test for the cse merge fix.
fn produce_valid_cse_regression_merge_test<R: Rng>(srcloc: &Srcloc, rng: &mut R) -> Option<CompileForm> {
    // Strategy:
    let vars = create_variable_set(srcloc.clone(), 7);

    // Generate a definition graph including assign forms with fresh variables.
    let structure_graph = create_structure_from_variables(rng, &vars);

    // Generate fresh argument variables.
    let args: Vec<Vec<u8>> = (0..5).map(|n| format!("a{n}").bytes().collect()).collect();

    // Get the generated variable graph.
    let vars: Vec<Vec<u8>> = structure_graph.bindings.keys().cloned().collect();

    // Ensure this graph supports complex definitions, at least 2 vars share 1 in
    // scope).
    let vars_sharing_scopes: BTreeMap<Vec<u8>, Vec<Vec<u8>>> =
        vars.iter().map(|v1| {
            let v1_in_scope: BTreeSet<&Vec<u8>> =
                structure_graph.variables_in_scope(v1).into_iter().collect();
            (v1.clone(), vars.iter().filter(|v2| {
                let v2_in_scope: BTreeSet<&Vec<u8>> = structure_graph.variables_in_scope(v2).into_iter().collect();
                !v2_in_scope.intersection(&v1_in_scope).next().is_some()
            }).cloned().collect::<Vec<Vec<u8>>>())
        }).filter(|(k,v)| !v.is_empty()).collect();

    if vars_sharing_scopes.is_empty() {
        return None;
    }

    // For each variable in the graph, generate some candidate expressions to
    // define it.
    let candidate_definitions: BTreeMap<Vec<u8>, GeneratedExpr> = structure_graph.bindings.keys().map(|k| {
        (k.clone(),
         structure_graph.generate_expression(&srcloc, 10, rng, &[b"a1".to_vec()], k))
    }).collect();

    let body = structure_graph.create_assign_form(srcloc, &candidate_definitions);
    let args = compose_sexp(srcloc.clone(), "(A1)");
    let function = HelperForm::Defun(false, Box::new(DefunData {
        loc: srcloc.clone(),
        nl: srcloc.clone(),
        kw: None,
        name: b"defined-fun".to_vec(),
        orig_args: args.clone(),
        args: args.clone(),
        synthetic: None,
        body: Rc::new(body)
    }));

    Some(CompileForm {
        loc: srcloc.clone(),
        args: args,
        helpers: vec![function],
        include_forms: vec![],
        exp: Rc::new(BodyForm::Call(srcloc.clone(), vec![
            Rc::new(BodyForm::Value(SExp::Atom(srcloc.clone(), b"defined-fun".to_vec()))),
            Rc::new(BodyForm::Value(SExp::Atom(srcloc.clone(), b"A1".to_vec())))
        ], None))
    })
}

#[test]
fn test_cse_merge_regression() {

    let mut rng = simple_seeded_rng(13);
    let srcloc = Srcloc::start("*test*");

    let produce_program = |rng: &mut ChaCha8Rng| {
        loop {
            if let Some(res) = produce_valid_cse_regression_merge_test(&srcloc, rng) {
                return res;
            }
        }
    };
    let test_program = produce_program(&mut rng);

    eprintln!("test_program {}", test_program.to_sexp());
    todo!();
}
