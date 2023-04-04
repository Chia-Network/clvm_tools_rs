use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::cmds::{cldb_hierarchy, YamlElement};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::cldb::{hex_to_modern_sexp, CldbNoOverride, CldbRun, CldbRunEnv};
use crate::compiler::clvm::start_step;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::prims;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;

fn json_to_yamlelement(json: &serde_json::Value) -> YamlElement {
    match json {
        serde_json::Value::Object(map) => {
            let mut yaml_map = BTreeMap::new();
            for (k, v) in map.iter() {
                let yamelled_wing = json_to_yamlelement(v);
                yaml_map.insert(k.to_string(), yamelled_wing);
            }
            YamlElement::Subtree(yaml_map)
        }
        serde_json::Value::String(s) => YamlElement::String(s.clone()),
        serde_json::Value::Array(v) => {
            YamlElement::Array(v.iter().map(|v| json_to_yamlelement(v)).collect())
        }
        _ => todo!(),
    }
}

fn yaml_to_yamlelement(yaml: &BTreeMap<String, YamlElement>) -> YamlElement {
    YamlElement::Subtree(yaml.clone())
}

#[test]
fn test_run_clvm_in_cldb() {
    let program_name = "fact.clsp";
    let program_code = "(mod (X) (include *standard-cl-21*) (defun fact (X) (if (> X 1) (* X (fact (- X 1))) 1)) (fact X))";
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(program_name));
    let mut symbols = HashMap::new();
    let args = parse_sexp(Srcloc::start("*args*"), "(5)".bytes()).expect("should parse")[0].clone();

    let program = compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &program_code,
        &mut symbols,
    )
    .expect("should compile");

    let mut prim_map = HashMap::new();
    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }
    let program_lines: Vec<String> = program_code.lines().map(|x| x.to_string()).collect();

    let step = start_step(Rc::new(program), args);
    let cldbenv = CldbRunEnv::new(
        Some(program_name.to_string()),
        Rc::new(program_lines),
        Box::new(CldbNoOverride::new_symbols(symbols)),
    );
    let mut cldbrun = CldbRun::new(runner, Rc::new(prim_map), Box::new(cldbenv), step);
    let mut output: BTreeMap<String, String> = BTreeMap::new();

    loop {
        if cldbrun.is_ended() {
            assert_eq!(output.get("Final"), Some(&"120".to_string()));
            return;
        }

        if let Some(result) = cldbrun.step(&mut allocator) {
            output = result;
        }
    }
}

fn compile_and_run_program_with_tree(
    input_file: &str,
    input_program_text: &str,
    args_text: &str,
    search_paths: &[String],
) -> Vec<BTreeMap<String, YamlElement>> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&input_file))
        .set_optimize(false)
        .set_search_paths(search_paths);

    let mut use_symbol_table = HashMap::new();

    let program = compile_file(
        &mut allocator,
        runner.clone(),
        opts.clone(),
        &input_program_text,
        &mut use_symbol_table,
    )
    .expect("should compile");
    let args = parse_sexp(program.loc(), args_text.as_bytes().iter().copied())
        .expect("should parse args")[0]
        .clone();

    let mut prim_map = HashMap::new();
    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }
    let program_lines: Rc<Vec<String>> =
        Rc::new(input_program_text.lines().map(|x| x.to_string()).collect());

    cldb_hierarchy(
        runner,
        Rc::new(prim_map),
        Some(input_file.to_owned()),
        program_lines,
        Rc::new(use_symbol_table),
        Rc::new(program),
        args,
    )
}

fn run_program_as_tree_from_hex(
    file_name: &str,
    input_program: &str,
    input_args: &str,
    symbol_table: HashMap<String, String>,
) -> Vec<BTreeMap<String, YamlElement>> {
    let mut allocator = Allocator::new();
    let prog_srcloc = Srcloc::start("*program*");
    let args_srcloc = Srcloc::start("*args*");

    let program = hex_to_modern_sexp(
        &mut allocator,
        &symbol_table,
        prog_srcloc.clone(),
        &input_program,
    )
    .expect("should decode from hex");

    let args = hex_to_modern_sexp(
        &mut allocator,
        &symbol_table,
        args_srcloc.clone(),
        &input_args,
    )
    .expect("should decode from hex");

    let mut prim_map = HashMap::new();
    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }
    let program_lines = Rc::new(vec![]);
    let runner = Rc::new(DefaultProgramRunner::new());
    cldb_hierarchy(
        runner,
        Rc::new(prim_map),
        Some(file_name.to_owned()),
        program_lines,
        Rc::new(symbol_table),
        program,
        args,
    )
}

fn compare_run_output(
    result: Vec<BTreeMap<String, YamlElement>>,
    run_entries: Vec<serde_json::Value>,
) {
    assert_eq!(result.len(), run_entries.len());
    for i in 0..result.len() {
        let result_entry = result[i].clone();
        let want_entry = &run_entries[i];
        let want_yaml = json_to_yamlelement(want_entry);
        let have_yaml = yaml_to_yamlelement(&result_entry);
        assert_eq!(want_yaml, have_yaml);
    }
}

#[test]
fn test_cldb_hierarchy_mode() {
    let json_text = fs::read_to_string("resources/tests/cldb_tree/test.json")
        .expect("test resources should exist: test.json");
    let run_entries: Vec<serde_json::Value> =
        serde_json::from_str(&json_text).expect("should contain json");
    let input_program = fs::read_to_string("resources/tests/cldb_tree/test_rec_1.cl")
        .expect("test resources should exist: test_rec_1.cl");
    let input_file = "./test_rec_1.cl";

    let result = compile_and_run_program_with_tree(&input_file, &input_program, "(3 2)", &vec![]);

    compare_run_output(result, run_entries);
}

#[test]
fn test_execute_program_and_capture_arguments() {
    let compiled_symbols_text =
        fs::read_to_string("resources/tests/cldb_tree/pool_member_innerpuz_extra.sym")
            .expect("should exist");
    let compiled_symbols: HashMap<String, String> =
        serde_json::from_str(&compiled_symbols_text).expect("should decode");
    let result = run_program_as_tree_from_hex(
        "./pool_member_innerpuz.hex",
        &fs::read_to_string("resources/tests/cldb_tree/pool_member_innerpuz.hex")
            .expect("should exist"),
        &fs::read_to_string("resources/tests/cldb_tree/pool_member_innerpuz_args.hex")
            .expect("should exist"),
        compiled_symbols,
    );

    let json_text = fs::read_to_string("resources/tests/cldb_tree/pool_member_innerpuz_run.json")
        .expect("test resources should exist");
    let run_entries: Vec<serde_json::Value> =
        serde_json::from_str(&json_text).expect("should contain json");

    compare_run_output(result, run_entries);
}
