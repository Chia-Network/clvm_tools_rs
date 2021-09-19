use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::t;
use crate::classic::clvm_tools::cmds::{
    OpcConversion,
    OpdConversion,
    TConversion
};

use crate::classic::clvm_tools::binutils::{
    assemble_from_ir,
    disassemble
};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::NodePath::NodePath;
use crate::classic::clvm_tools::stages;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;

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

fn compile_program<'a>(allocator: &'a mut Allocator, src: String) -> Result<String, EvalErr> {
    let run_script = stages::run(allocator);
    let runner = run_program_for_search_paths(&vec!(".".to_string()));
    let input_ir = read_ir(&src);
    let input_program =
        assemble_from_ir(allocator, Rc::new(input_ir.unwrap())).unwrap();
    let input_sexp = allocator.new_pair(input_program, allocator.null()).unwrap();
    let res = runner.run_program(
        allocator,
        run_script,
        input_sexp,
        None
    );

    return res.map(|x| disassemble(allocator, x.1));
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
    let res = run_from_source(&mut allocator, "(16 (1 . 3) (1 . 5))".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 8);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}

#[test]
fn can_do_operations_kw() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(+ (q . 3) (q . 5))".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 8);
        },
        _ => { assert_eq!("expected atom", ""); }
    }
}

#[test]
fn basic_opc() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}.invoke(
        &mut allocator, &"()".to_string()
    ).unwrap();
    assert_eq!(result.rest(), "80");
}

#[test]
fn basic_opc_lil() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}.invoke(
        &mut allocator, &"(())".to_string()
    ).unwrap();
    assert_eq!(result.rest(), "ff8080");
}

#[test]
fn basic_opc_quoted_1() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}.invoke(
        &mut allocator, &"(q . 1)".to_string()
    ).unwrap();
    assert_eq!(result.rest(), "ff0101");
}

#[test]
fn very_simple_compile() {
    let mut allocator = Allocator::new();
    let result = compile_program(&mut allocator, "(mod () (+ 3 2))".to_string());
    assert_eq!(result, Ok("(q . 5)".to_string()));
}

#[test]
fn node_path_top_left() {
    assert_eq!(*NodePath::new(None).first().as_path().data(), vec!(2 as u8));
}

#[test]
fn node_path_top_right() {
    assert_eq!(*NodePath::new(None).rest().as_path().data(), vec!(3 as u8));
}

#[test]
fn node_path_2nd_of_list() {
    assert_eq!(*NodePath::new(None).first().rest().as_path().data(), vec!(5 as u8));
}

#[test]
fn compile_prog_with_args() {
    let mut allocator = Allocator::new();
    let result = compile_program(&mut allocator, "(mod (A B) (+ A B))".to_string());
    assert_eq!(result, Ok("(+ 2 5)".to_string()));
}

#[test]
fn compile_function_macro() {
    let mut allocator = Allocator::new();
    let result = compile_program(&mut allocator, "(\"defmacro\" \"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))))".to_string());
    assert_eq!(result, Ok("(\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ())))".to_string()));
}
