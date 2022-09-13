use clvmr::allocator::Allocator;
use std::rc::Rc;

use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages::stage_2::compile::{
    do_com_prog, try_expand_macro_for_atom,
};
use crate::classic::clvm_tools::stages::stage_2::helpers::brun;
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;

fn test_expand_macro(
    allocator: &mut Allocator,
    macro_data: String,
    prog_rest: String,
    macros: String,
    symbols: String,
) -> String {
    let macro_ir = read_ir(&macro_data).unwrap();
    let macro_source = assemble_from_ir(allocator, Rc::new(macro_ir)).unwrap();
    let prog_ir = read_ir(&prog_rest).unwrap();
    let prog_source = assemble_from_ir(allocator, Rc::new(prog_ir)).unwrap();
    let macros_ir = read_ir(&macros).unwrap();
    let macros_source = assemble_from_ir(allocator, Rc::new(macros_ir)).unwrap();
    let symbols_ir = read_ir(&symbols).unwrap();
    let symbols_source = assemble_from_ir(allocator, Rc::new(symbols_ir)).unwrap();
    let exp_res = try_expand_macro_for_atom(
        allocator,
        macro_source,
        prog_source,
        macros_source,
        symbols_source,
    )
    .unwrap();
    disassemble(allocator, exp_res.1)
}

fn test_inner_expansion(
    allocator: &mut Allocator,
    macro_code: String,
    prog_rest: String,
) -> String {
    let macro_ir = read_ir(&macro_code).unwrap();
    let macro_source = assemble_from_ir(allocator, Rc::new(macro_ir)).unwrap();
    let prog_ir = read_ir(&prog_rest).unwrap();
    let prog_source = assemble_from_ir(allocator, Rc::new(prog_ir)).unwrap();
    let exp_res = brun(allocator, macro_source, prog_source).unwrap();
    disassemble(allocator, exp_res)
}

fn test_do_com_prog(
    allocator: &mut Allocator,
    program_src: String,
    macro_lookup_src: String,
    symbol_table_src: String,
) -> String {
    let runner = run_program_for_search_paths(&vec![".".to_string()]);
    let prog_ir = read_ir(&program_src).unwrap();
    let program = assemble_from_ir(allocator, Rc::new(prog_ir)).unwrap();
    let macro_ir = read_ir(&macro_lookup_src).unwrap();
    let macro_lookup = assemble_from_ir(allocator, Rc::new(macro_ir)).unwrap();
    let sym_ir = read_ir(&symbol_table_src).unwrap();
    let symbol_table = assemble_from_ir(allocator, Rc::new(sym_ir)).unwrap();
    let result = do_com_prog(allocator, 849, program, macro_lookup, symbol_table, runner).unwrap();
    disassemble(allocator, result.1)
}

#[test]
fn test_macro_expansion() {
    let mut allocator = Allocator::new();
    let res = test_expand_macro(
        &mut allocator,
        "(c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))".to_string(),
        "(\"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))))".to_string(),
        "((\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))))".to_string(),
        "()".to_string()
    );
    assert_eq!(res, "(a (\"com\" (a (q 4 (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))) (q \"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))))) (q (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))))) (q)) 1)".to_string());
}

#[test]
fn test_inner_macro_exp() {
    let mut allocator = Allocator::new();
    let res = test_inner_expansion(
        &mut allocator,
        "(c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))".to_string(),
        "(\"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))))".to_string()
    );
    assert_eq!(res, "(a (q 4 (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))) (q \"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\"))))))))".to_string());
}

#[test]
fn test_compile_during_assert_1() {
    let mut allocator = Allocator::new();
    let res = test_do_com_prog(
        &mut allocator,
        "(\"assert\" 1)".to_string(),
        "((\"assert\" (a (i 3 (q 4 (q . 26982) (c 2 (c (c (q . \"assert\") 3) (q (x))))) (q . 2)) 1)) (26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))))".to_string(),
        "()".to_string()
    );

    assert_eq!(res, "(a (\"com\" (a (q 2 (i 3 (q 4 (q . 26982) (c 2 (c (c (q . \"assert\") 3) (q (x))))) (q . 2)) 1) (q 1)) (q (\"assert\" (a (i 3 (q 4 (q . 26982) (c 2 (c (c (q . \"assert\") 3) (q (x))))) (q . 2)) 1)) (26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))))) (q)) 1)".to_string());
}

#[test]
fn test_compile_check_output_diag_assert() {
    let mut allocator = Allocator::new();
    let res = test_do_com_prog(
        &mut allocator,
        "(\"mod\" () (\"defmacro\" \"assert\" \"items\" (26982 (r \"items\") (\"list\" 26982 (f \"items\") (c \"assert\" (r \"items\")) (q 8)) (f \"items\"))) (\"assert\" 1))".to_string(),
        "((26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))))".to_string(),
        "()".to_string()
    );

    assert_eq!(
        res,
        "(a (q \"opt\" (q 2 (\"opt\" (\"com\" (q \"assert\" 1) (q (\"assert\" (a (i 3 (q 4 (q . 26982) (c 2 (c (c (q . \"assert\") 3) (q (x))))) (q . 2)) 1)) (26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))))) (q))) 1)) 1)".to_string()
    );
}

#[test]
fn test_compile_assert_2() {
    let mut allocator = Allocator::new();
    let res = test_do_com_prog(
        &mut allocator,
        "(\"mod\" () (\"defmacro\" \"assert\" \"items\" (26982 (r \"items\") (\"list\" 26982 (f \"items\") (c \"assert\" (r \"items\")) (q 8)) (f \"items\"))) (\"assert\" 1))".to_string(),
        "((26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q))))))".to_string(),
        "()".to_string()
    );

    assert_eq!(
        res,
        "(a (q \"opt\" (q 2 (\"opt\" (\"com\" (q \"assert\" 1) (q (\"assert\" (a (i 3 (q 4 (q . 26982) (c 2 (c (c (q . \"assert\") 3) (q (x))))) (q . 2)) 1)) (26982 (c (q . 2) (c (c (q . 3) (c 2 (c (c (q . \"function\") (c 5 ())) (c (c (q . \"function\") (c 11 ())) ())))) (q 64)))) (\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ()))) (\"list\" (a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)) (\"defmacro\" (c (q . \"list\") (c (f 1) (c (c (q . \"mod\") (c (f (r 1)) (c (f (r (r 1))) (q)))) (q)))))) (q))) 1)) 1)".to_string()
    );
}
