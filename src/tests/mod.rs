use std::fs;
use std::path::PathBuf;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::t;
use crate::classic::clvm_tools::cmds::{
    OpdConversion,
    TConversion
};

#[test]
fn basic_opd() {
    let mut allocator = Allocator::new();
    let result = OpdConversion {}.invoke(
        &mut allocator, &"80".to_string()
    ).unwrap();
    assert_eq!(result.rest(), "()");
}

#[test]
fn nil_in_list_opd() {
    let mut allocator = Allocator::new();
    let result = OpdConversion {}.invoke(
        &mut allocator,
        &"ff8080".to_string()
    ).unwrap();
    assert_eq!(result.rest(), "(())");
}

#[test]
fn big_decode_opd() {
    let mut allocator = Allocator::new();
    let mut testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    testpath.push("resources/tests");
    let mut in_path = testpath.clone();
    in_path.push("big_decode_in.txt");
    let mut out_path = testpath.clone();
    out_path.push("big_decode_out.txt");

    let expected =
        fs::read_to_string(in_path).and_then(|input| {
            return fs::read_to_string(out_path).map(|output| {
                t(input, output.trim().to_string())
            });
        }).unwrap();

    let result = OpdConversion {}.invoke(
        &mut allocator,
        &expected.first()
    ).unwrap();
    assert_eq!(expected.rest(), result.rest());
}
