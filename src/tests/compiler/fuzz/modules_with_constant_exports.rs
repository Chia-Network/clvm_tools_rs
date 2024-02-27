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
use crate::compiler::comptypes::{BodyForm, CompilerOpts, DefconstData, HelperForm};
use crate::compiler::dialect::AcceptedDialect;
use crate::compiler::frontend::compile_helperform;
use crate::compiler::fuzz::{FuzzGenerator, Rule};
use crate::compiler::prims::primquote;
use crate::compiler::sexp::{decode_string, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

use crate::tests::compiler::modules::{hex_to_clvm, perform_compile_of_file};

fn compose_sexp(loc: Srcloc, s: &str) -> Rc<SExp> {
    parse_sexp(loc, s.bytes()).expect("should parse")[0].clone()
}

// Property test of sorts:
//
// Make 1-5 constants with any of these expression types:
//   let or assign form
//   lambda (and a corresponding constant applying it either directly or via map
//   or filter)?
//   a few basic operators
// Constants generated one at a time, depending on each other in tiers.
// Constants generated all at once, depending on any arrangement of the others.
//
// Do the above arrangement but adding 1 or 2 functions that depend on the
// constants and each other.
//
// Maybe put some more thought into fuzzing infra?
struct ModuleConstantExpectation {
    constants_and_values: BTreeMap<Vec<u8>, Rc<SExp>>,
    waiting_constants: usize,
    exports: BTreeSet<Vec<u8>>,
    opts: Rc<dyn CompilerOpts>,
    counter: usize,
    loc: Srcloc,
}
impl ModuleConstantExpectation {
    fn new(opts: Rc<dyn CompilerOpts>) -> Self {
        ModuleConstantExpectation {
            exports: BTreeSet::new(),
            waiting_constants: 0,
            constants_and_values: BTreeMap::new(),
            opts,
            counter: 0,
            loc: Srcloc::start("*constant-test*"),
        }
    }

    fn loc(&self) -> Srcloc {
        self.loc.clone()
    }
}

struct TestModuleConstantFuzzTopRule { another_constant: bool }
impl TestModuleConstantFuzzTopRule {
    fn new(c: bool) -> Self {
        TestModuleConstantFuzzTopRule { another_constant: c }
    }
}
impl Rule<ModuleConstantExpectation,Rc<SExp>> for TestModuleConstantFuzzTopRule {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        if tag != b"top" {
            return None;
        }

        eprintln!("T rule check {} {idx} term {terminate} {heritage_list:?}", decode_string(tag));

        if self.another_constant {
            let start_program = compose_sexp(state.loc(), &format!("( (include *standard-cl-23*) ${{{idx}:constant}} . ${{{}:constant-program-tail}})", idx + 1));
            state.waiting_constants += 1;
            eprintln!("waiting_constants: {}", state.waiting_constants);
            Some(start_program.clone())
        } else {
            let start_program = compose_sexp(state.loc(), &format!("( (include *standard-cl-23*) (defconstant A ${{{idx}:constant-body}}) (export A))"));
            state.exports.insert(b"A".to_vec());
            Some(start_program.clone())
        }
    }
}

struct TestModuleConstantFuzzConstantBodyRule { }
impl TestModuleConstantFuzzConstantBodyRule {
    fn new() -> Self { TestModuleConstantFuzzConstantBodyRule { } }
}

fn get_constant_id(heritage: &[Rc<SExp>]) -> Option<Vec<u8>> {
    if heritage.len() < 2 {
        return None;
    }

    if let SExp::Cons(_, c, _) = heritage[heritage.len() - 2].borrow() {
        if let SExp::Atom(_, a) = c.borrow() {
            return Some(a.to_vec());
        }
    }

    None
}

impl Rule<ModuleConstantExpectation,Rc<SExp>> for TestModuleConstantFuzzConstantBodyRule {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        eprintln!("C rule check {} {idx} term {terminate} {heritage_list:?}", decode_string(tag));

        if tag != b"constant-body" {
            return None;
        }

        let body = compose_sexp(state.loc(), "1");
        let constant_id =
            if let Some(constant_id) = get_constant_id(heritage) {
                constant_id
            } else {
                todo!();
            };

        state.constants_and_values.insert(constant_id, body.clone());
        Some(body.clone())
    }
}

struct TestModuleConstantFuzzApplyOperation {
    op: u32,
    other_value: Rc<SExp>
}
impl Rule<ModuleConstantExpectation,Rc<SExp>> for TestModuleConstantFuzzApplyOperation {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {

        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        eprintln!("ApplyOperation {} {heritage_list:?}", decode_string(tag));
        if tag != b"constant-body" {
            return None;
        }

        let my_id =
            if let Some(constant_id) = get_constant_id(heritage) {
                constant_id
            } else {
                return None;
            };

        // Get the existing constants.
        let constants_with_values =
            if let Some(c) = find_all_constants(state.opts.clone(), heritage, false) {
                c
            } else {
                return None;
            };

        // No constants are finished.
        if constants_with_values.is_empty() {
            return None;
        }

        // Choose a constant to base it on.
        let choice = state.counter % constants_with_values.len();
        state.counter += 13;
        let chosen: &DefconstData = &constants_with_values[choice];

        let prev_value =
            if let Some(chosen_value) = state.constants_and_values.get(&chosen.name) {
                // Apply an operation to this value.
                if let Ok(number) = chosen_value.get_number() {
                    number
                } else {
                    return None;
                }
            } else {
                return None;
            };

        let nil = Rc::new(SExp::Nil(state.loc()));
        let quoted_this_val = Rc::new(primquote(state.loc(), Rc::new(SExp::Integer(state.loc(), prev_value))));
        let quoted_other_val = Rc::new(primquote(state.loc(), self.other_value.clone()));
        let make_expr = |loc: Srcloc, this_val: Rc<SExp>, other_val: Rc<SExp>| {
            compose_sexp(loc, &format!("({} {this_val} {other_val})", self.op))
        };
        let mut allocator = Allocator::new();
        let runner: Rc<dyn TRunProgram> = Rc::new(DefaultProgramRunner::new());
        let run_expr = make_expr(state.loc(), quoted_this_val, quoted_other_val);
        eprintln!("run_expr {run_expr}");
        let new_value = run(
            &mut allocator,
            runner,
            state.opts.prim_map(),
            run_expr,
            nil.clone(),
            None,
            None
        ).expect("should execute");
        state.constants_and_values.insert(my_id, new_value);

        // Add one to any constant that already has a body.
        Some(make_expr(state.loc(), Rc::new(SExp::Atom(state.loc(), chosen.name.clone())), self.other_value.clone()))
    }
}

struct TestModuleConstantFuzzMoreConstants {
    want_more: bool,
}
impl Rule<ModuleConstantExpectation,Rc<SExp>> for TestModuleConstantFuzzMoreConstants {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        if tag != b"constant-program-tail" {
            return None;
        }

        if !terminate && self.want_more {
            let body = compose_sexp(state.loc(), &format!("(${{{}:constant}} . ${{{}:constant-program-tail}})", idx, idx + 1));
            state.waiting_constants += 1;
            Some(body.clone())
        } else {
            let body = compose_sexp(state.loc(), &format!("${{{}:exports}}", idx));
            Some(body.clone())
        }
    }
}

fn constant_body_unexpanded(body: Rc<BodyForm>) -> bool {
    if let BodyForm::Value(SExp::Atom(_, name)) = body.borrow() {
        name.starts_with(b"${") && name.ends_with(b"}")
    } else {
        false
    }
}

fn find_all_constants(opts: Rc<dyn CompilerOpts>, heritage: &[Rc<SExp>], abort_on_unexpanded: bool) -> Option<Vec<DefconstData>> {
    // From the toplevel, scan for defconst forms and get their names.
    // Reject any that aren't fully expanded.
    if heritage.is_empty() {
        return None;
    }

    let mut result = Vec::new();

    let mut program = heritage[0].clone();
    while let SExp::Cons(_, p, tail) = program.clone().borrow() {
        program = tail.clone();

        if let Ok(Some(res)) = compile_helperform(opts.clone(), p.clone()) {
            for h in res.new_helpers.iter() {
                if let HelperForm::Defconstant(dc) = h {
                    if constant_body_unexpanded(dc.body.clone()) {
                        if abort_on_unexpanded {
                            return None;
                        } else {
                            continue;
                        }
                    }

                    result.push(dc.clone());
                }
            }
        }
    }

    Some(result)
}

struct TestModuleConstantFuzzExports { }
impl Rule<ModuleConstantExpectation, Rc<SExp>> for TestModuleConstantFuzzExports {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        if tag != b"exports" || state.waiting_constants > 0 {
            return None;
        }

        let have_constants =
            if let Some(c) = find_all_constants(state.opts.clone(), heritage, true) {
                c
            } else {
                return None;
            };

        let nil = Rc::new(SExp::Nil(state.loc()));
        let export_atom = Rc::new(SExp::Atom(state.loc(), b"export".to_vec()));
        let mut result = nil.clone();
        for h in have_constants.iter() {
            result = Rc::new(SExp::Cons(
                state.loc(),
                compose_sexp(
                    state.loc(),
                    &format!("(export {})", decode_string(&h.name))
                ),
                result
            ));

            // Record the export.
            state.exports.insert(h.name.clone());
        }

        Some(result)
    }
}

struct TestModuleConstantNew { }
impl Rule<ModuleConstantExpectation, Rc<SExp>> for TestModuleConstantNew {
    fn check(&self, state: &mut ModuleConstantExpectation, tag: &[u8], idx: usize, terminate: bool, heritage: &[Rc<SExp>]) -> Option<Rc<SExp>> {
        if tag != b"constant" {
            return None;
        }

        let name = format!("C{idx}");
        let body = compose_sexp(state.loc(), &format!("(defconst {name} ${{{}:constant-body}})", idx));
        let heritage_list: Vec<String> = heritage.iter().map(|h| h.to_string()).collect();
        eprintln!("CN waiting_constants: {} {heritage_list:?}", state.waiting_constants);
        state.waiting_constants -= 1;
        Some(body.clone())
    }
}

#[test]
fn test_property_fuzz_stable_constants() {
    let mut rng = ChaCha8Rng::from_seed([
        1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,
        2,2,2,2,2,2,2,2,
        2,2,2,2,2,2,2,2,
    ]);

    let srcloc = Srcloc::start("*value*");
    let one = Rc::new(SExp::Integer(srcloc.clone(), bi_one()));
    let rules: Vec<Rc<dyn Rule<ModuleConstantExpectation, Rc<SExp>>>> = vec![
        Rc::new(TestModuleConstantFuzzTopRule::new(false)),
        Rc::new(TestModuleConstantFuzzTopRule::new(true)),
        Rc::new(TestModuleConstantFuzzConstantBodyRule::new()),
        Rc::new(TestModuleConstantNew { }),
        Rc::new(TestModuleConstantFuzzMoreConstants { want_more: true }),
        Rc::new(TestModuleConstantFuzzMoreConstants { want_more: false }),
        Rc::new(TestModuleConstantFuzzExports {}),
        Rc::new(TestModuleConstantFuzzApplyOperation { op: 16, other_value: one.clone() }),
        Rc::new(TestModuleConstantFuzzApplyOperation { op: 17, other_value: one.clone() })
    ];
    let top_node = Rc::new(SExp::Atom(srcloc.clone(), b"${0:top}".to_vec()));

    for _ in 0..10 {
        let mut fuzzgen = FuzzGenerator::new(top_node.clone(), &rules);
        let mut idx = 0;
        let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new("*test*"));
        let mut mc = ModuleConstantExpectation::new(opts.set_dialect(AcceptedDialect {
            stepping: Some(23),
            strict: true,
        }).set_optimize(true));
        while fuzzgen.expand(&mut mc, idx > 100, &mut rng).expect("should expand") {
            idx += 1;
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
        for cname in mc.exports.iter() {
            if let Some(cval) = mc.constants_and_values.get(cname) {
                eprintln!("checking for {} = {cval}", decode_string(cname));
                let hex_file_name = format!("test_{}.hex", decode_string(cname));
                let hex_data = compiled.source_opts.get_written_file(&hex_file_name).expect("hex file should exist");
                let compiled_node = hex_to_clvm(&mut allocator, &hex_data);
                let converted_node = convert_from_clvm_rs(&mut allocator, cval.loc(), compiled_node).expect("should convert to sexp objects");
                assert_eq!(cval, &converted_node);
            } else {
                todo!();
            }
        }
    }

    // We've checked all predicted values.
}
