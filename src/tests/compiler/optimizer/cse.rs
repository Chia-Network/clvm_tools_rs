use std::rc::Rc;

use regex::Regex;

use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::optimize::cse::cse_optimize_bodyform;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;

use crate::tests::classic::run::{do_basic_brun, do_basic_run};

#[test]
fn smoke_test_cse_optimization() {
    let filename = "*test*";
    let source = indoc! {"
    (a (i Q
      (com (G (- Q 1) (* (+ 1 Q) R)))
      (com (* (+ 1 Q) R))
      ) 1)"}
    .to_string();
    let srcloc = Srcloc::start(filename);
    let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(filename));
    let parsed = parse_sexp(srcloc.clone(), source.bytes()).expect("should parse");
    let bodyform = compile_bodyform(opts.clone(), parsed[0].clone()).expect("should compile");
    let cse_transformed =
        cse_optimize_bodyform(&srcloc, b"test", &bodyform).expect("should cse optimize");
    let re_def = r"(let ((cse_[$]_[0-9]+ ([*] ([+] 1 Q) R))) (a (i Q (com (G (- Q 1) cse_[$]_[0-9]+)) (com cse_[$]_[0-9]+)) 1))".replace("(", r"\(").replace(")",r"\)");
    eprintln!("re_def {re_def}");
    let re = Regex::new(&re_def).expect("should become a regex");
    assert!(re.is_match(&cse_transformed.to_sexp().to_string()));
}

#[test]
fn test_cse_tricky() {
    let filename = "resources/tests/strict/cse-complex-1.clsp";
    let program = do_basic_run(&vec!["run".to_string(), filename.to_string()])
        .trim()
        .to_string();

    let run_result_11 = do_basic_brun(&vec![
        "brun".to_string(),
        program.clone(),
        "(11)".to_string(),
    ])
    .trim()
    .to_string();
    assert_eq!(run_result_11, "506");

    let run_result_41 = do_basic_brun(&vec!["brun".to_string(), program, "(41)".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result_41, "15375");
}

#[test]
fn test_cse_tricky_lambda() {
    let filename = "resources/tests/strict/cse-complex-1-lambda.clsp";
    let program = do_basic_run(&vec!["run".to_string(), filename.to_string()])
        .trim()
        .to_string();

    let run_result_11 = do_basic_brun(&vec![
        "brun".to_string(),
        program.clone(),
        "(11)".to_string(),
    ])
    .trim()
    .to_string();
    assert_eq!(run_result_11, "5566");

    let run_result_41 = do_basic_brun(&vec![
        "brun".to_string(),
        program.clone(),
        "(41)".to_string(),
    ])
    .trim()
    .to_string();
    assert_eq!(run_result_41, "0x099e67");

    let run_result_5 = do_basic_brun(&vec!["brun".to_string(), program, "(5)".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result_5, "240");
}

// Ensure that we're sorting CSE rounds to apply by dominance so we do inner
// replacements before outer ones.  Any that aren't dominated don't have an
// order that matters.
#[test]
fn test_cse_dominance_sorting() {
    let filename = "resources/tests/strict/cse-test-no-dom.clsp";
    let program = do_basic_run(&vec!["run".to_string(), filename.to_string()])
        .trim()
        .to_string();
    let run_result = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program,
        "(((3 3) (2 1 13 19) (5 5) (7 7)))".to_string(),
    ])
    .trim()
    .to_string();
    assert_eq!(run_result, "(13 19)");
}

// Test out atomsort from bram's chialisp
#[test]
fn test_atomsort_bad_ref_simplified() {
    let filename = "resources/tests/strict/csecond.clsp";

    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests/strict".to_string(),
        filename.to_string(),
    ])
    .trim()
    .to_string();

    let run_result = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program,
        "((99 101 103))".to_string(),
    ])
    .trim()
    .to_string();

    // Expect test5
    assert_eq!(run_result, "\"test5\"");
}

#[test]
fn test_atomsort_bad_ref() {
    let filename = "resources/tests/strict/test_atomsort.clsp";

    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests/strict".to_string(),
        filename.to_string(),
    ])
    .trim()
    .to_string();

    let run_result_empty = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program.clone(),
        "(())".to_string(),
    ])
    .trim()
    .to_string();

    // Expect a sorted list, descending order.
    assert_eq!(run_result_empty, "()");

    let run_result_one_item = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program.clone(),
        "((0x100001))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(run_result_one_item, "(0x100001)");

    let run_result_two_items = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program.clone(),
        "((0x100001 0x100002))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(run_result_two_items, "(0x100002 0x100001)");

    let run_result_three_items = do_basic_brun(&vec![
        "brun".to_string(),
        "-n".to_string(),
        program,
        "((0x100001 0x100003 0x100002))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(run_result_three_items, "(0x100003 0x100002 0x100001)");
}
