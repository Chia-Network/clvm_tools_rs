use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::cmds::{cldb_hierarchy, YamlElement};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::prims;
use crate::compiler::sexp::parse_sexp;

fn json_to_yamlelement(json: &serde_json::Value) -> YamlElement {
    match json {
        serde_json::Value::Object(map) => {
            let mut yaml_map = BTreeMap::new();
            for (k,v) in map.iter() {
                let yamelled_wing = json_to_yamlelement(v);
                yaml_map.insert(k.to_string(), yamelled_wing);
            }
            YamlElement::Subtree(yaml_map)
        },
        serde_json::Value::String(s) => {
            YamlElement::String(s.clone())
        },
        serde_json::Value::Array(v) => {
            YamlElement::Array(v.iter().map(|v| json_to_yamlelement(v)).collect())
        },
        _ => todo!()
    }
}

fn yaml_to_yamlelement(
    yaml: &BTreeMap<String, YamlElement>
) -> YamlElement {
    YamlElement::Subtree(yaml.clone())
}

#[test]
fn test_cldb_hierarchy_mode() {
    let json_text = fs::read_to_string("resources/tests/cldb_tree/test.json").expect("test resources should exist: test.json");
    let run_entries: Vec<serde_json::Value> = serde_json::from_str(&json_text).expect("should contain json");
    let input_program = fs::read_to_string("resources/tests/cldb_tree/test_rec_1.cl").expect("test resources should exist: test_rec_1.cl");
    let input_file = "./test_rec_1.cl";

    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&input_file))
        .set_optimize(false)
        .set_search_paths(&vec![]);

    let mut use_symbol_table = HashMap::new();

    let program = compile_file(
        &mut allocator,
        runner.clone(),
        opts.clone(),
        &input_program,
        &mut use_symbol_table,
    ).expect("should compile");
    let args = parse_sexp(program.loc(), "(3 2)".as_bytes().iter().copied()).expect("should parse args")[0].clone();

    let mut prim_map = HashMap::new();
    for p in prims::prims().iter() {
        prim_map.insert(p.0.clone(), Rc::new(p.1.clone()));
    }
    let program_lines: Rc<Vec<String>> = Rc::new(input_program.lines().map(|x| x.to_string()).collect());

    let result = cldb_hierarchy(
        runner,
        Rc::new(prim_map),
        Some(input_file.to_owned()),
        program_lines,
        Rc::new(use_symbol_table),
        Rc::new(program),
        args
    );

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
fn test_execute_program_and_capture_arguments() {
    let compiled_p2_parent_program_text =
        fs::read_to_string("resources/tests/cldb_tree/pool_member_innerpuz.cl");
    
}
