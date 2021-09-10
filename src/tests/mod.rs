use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};

use crate::classic::clvm::__type_compatibility__::t;
use crate::classic::clvm_tools::cmds::{
    OpdConversion,
    TConversion
};

use crate::classic::clvm_tools::binutils::assemble_from_ir;
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
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

fn run_from_source<'a>(allocator: &'a mut Allocator, src: String) -> NodePtr {
    let ir = read_ir(&src).unwrap();
    print!("ir {:?}\n", &ir);
    let assembled = assemble_from_ir(allocator, Rc::new(ir)).unwrap();
    let runner = DefaultProgramRunner::new();
    let null = allocator.null();
    let res = runner.run_program(
        allocator,
        assembled,
        null,
        None
    ).unwrap();
    return res.1;
}

#[test]
fn can_run_from_source_nil() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "()".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 0);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}

#[test]
fn can_echo_quoted_nil() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(1)".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 0);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}

#[test]
fn can_echo_quoted() {
    let mut allocator = Allocator::new();
    let null = allocator.null();
    let res = run_from_source(&mut allocator, "(1 ())".to_string());
    match allocator.sexp(res) {
        SExp::Pair(l,r) => {
            assert_eq!(l, null);
            assert_eq!(r, null);
        },
        _ => { assert_eq!("expected pair", ""); }
    }
}

#[test]
fn can_echo_quoted_atom() {
    let mut allocator = Allocator::new();
    let null = allocator.null();
    let res = run_from_source(&mut allocator, "(1 . 3)".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 3);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}

#[test]
fn can_do_operations() {
    let mut allocator = Allocator::new();
    let null = allocator.null();
    let res = run_from_source(&mut allocator, "(12 (1 . 3) (1 . 5))".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 8);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}
