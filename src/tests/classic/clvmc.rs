use std::collections::HashMap;
use std::fs;

use crate::classic::clvm_tools::clvmc::compile_clvm;
use crate::tests::classic::run::read_json_from_file;

#[test]
fn test_compile_clvm_function_1() {
    let mut symbol_hash_table = HashMap::new();
    let bridge_hex_file = "validation_taproot.clvm2.hex";
    // Try to remove it if it exists.
    fs::remove_file(bridge_hex_file).ok();
    let _ = compile_clvm(
        "resources/tests/bridgeref/validation_taproot.clsp",
        bridge_hex_file,
        &["resources/tests/bridge-includes".to_string()],
        &mut symbol_hash_table,
    )
    .expect("should compile");
    let bridge_hex = fs::read_to_string(bridge_hex_file).expect("should have been created");
    fs::remove_file(bridge_hex_file).expect("should have existed");
    let read_in_hex_data =
        fs::read_to_string("resources/tests/bridgeref/validation_taproot.clvm.hex.reference")
            .expect("should exist");
    let read_in_symbol_data =
        read_json_from_file("resources/tests/bridgeref/validation_taproot.sym.reference");
    assert_eq!(bridge_hex, read_in_hex_data);
    for (key, value) in read_in_symbol_data.iter() {
        if key != "source_file" {
            assert_eq!(symbol_hash_table.get(key), Some(value));
        }
    }
}

#[test]
fn test_compile_clvm_with_previous_data() {
    let bridge_hex_file = "validation_taproot.clvm.hex";
    let bridge_hex =
        fs::read_to_string("resources/tests/bridgeref/validation_taproot.clvm.hex.reference")
            .expect("should have been created");
    let mut symbol_hash_table = HashMap::new();

    fs::write(bridge_hex_file, bridge_hex).expect("should write");
    compile_clvm(
        "resources/tests/bridgeref/validation_taproot.clsp",
        bridge_hex_file,
        &["resources/tests/bridge-includes".to_string()],
        &mut symbol_hash_table,
    )
    .expect("should compile");
    fs::remove_file(bridge_hex_file).expect("should have existed");
}
