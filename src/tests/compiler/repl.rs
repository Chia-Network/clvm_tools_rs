use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompileErr;
use crate::compiler::repl::Repl;

fn test_repl_outcome_with_stack_limit<S>(
    inputs: Vec<S>,
    limit: Option<usize>,
) -> Result<Option<String>, CompileErr>
where
    S: ToString,
{
    let mut allocator = Allocator::new();
    let mut res = Ok(None);
    let opts = Rc::new(DefaultCompilerOpts::new(&"*repl-test*".to_string()));
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut repl = Repl::new(opts, runner);

    if let Some(limit) = limit {
        repl.set_stack_limit(Some(limit));
    }

    for i in inputs.iter() {
        res = res.and_then(|_| repl.process_line(&mut allocator, i.to_string()));
    }

    res.map(|r| r.map(|r| r.to_sexp().to_string()))
}

fn test_repl_outcome<S>(inputs: Vec<S>) -> Result<Option<String>, CompileErr>
where
    S: ToString,
{
    test_repl_outcome_with_stack_limit(inputs, None)
}

#[test]
fn test_basic_repl_constant() {
    assert_eq!(
        test_repl_outcome(vec!["(defconstant CREATE_COIN 51)", "51"])
            .unwrap()
            .unwrap(),
        "(q . 51)"
    );
}

#[test]
fn test_basic_recursion() {
    assert_eq!(
        test_repl_outcome(vec![
            "(defun fact-base (VALUE) VALUE)",
            "(defun factorial (VALUE) (if (= VALUE 1) (fact-base VALUE) (* VALUE (factorial (- VALUE 1)))))",
            "(factorial 5)"
        ]).unwrap().unwrap(),
        "(q . 120)"
    );
}

#[test]
fn test_pw_coin() {
    let startvec = vec![
        "(defconstant CREATE_COIN 51)",
        "(defun check-password (password)",
        "  (let ((password-hash (sha256 password))",
        "        (real-hash 0x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824))",
        "    (= password-hash real-hash)",
        "    )",
        "  )",
    ];
    let mut yesvec = startvec.clone();
    yesvec.push("(check-password \"hello\")");
    let mut novec = startvec.clone();
    novec.push("(check-password \"hithere\")");

    assert_eq!(test_repl_outcome(yesvec).unwrap().unwrap(), "(q . 1)");
    assert_eq!(test_repl_outcome(novec).unwrap().unwrap(), "(q)");
}

#[test]
fn test_toplevel_macros_1() {
    assert_eq!(
        test_repl_outcome(vec!["(defconstant COND 1)", "(if COND 1 0)"])
            .unwrap()
            .unwrap(),
        "(q . 1)"
    );
}

#[test]
fn test_toplevel_macros_2() {
    assert_eq!(
        test_repl_outcome(vec!["(list 1 2 3)"]).unwrap().unwrap(),
        "(q 1 2 3)"
    );
}

#[test]
fn test_last_of_pwcoin_1() {
    assert_eq!(
        test_repl_outcome(vec![
            "(defconstant CREATE_COIN 51)",
            "(defun check-password (password)",
            "  (let ((password-hash (sha256 password))",
            "        (real-hash 0x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824))",
            "    (= password-hash real-hash)",
            "    )",
            "  )",
            "(defun doit (password new_puzhash amount)",
            "  (if (check-password password)",
            "    (list (list CREATE_COIN new_puzhash amount))",
            "    (x)",
            "    )",
            "  )",
            "(doit \"hello\" 0xdeadbeef 1)"
        ]).unwrap().unwrap(),
        "(q (51 0xdeadbeef 1))"
    );
}

#[test]
fn test_defconstant_2() {
    assert_eq!(
        test_repl_outcome(vec!["(defconstant A 1)", "(defconstant B 2)", "B"])
            .unwrap()
            .unwrap(),
        "(q . 2)"
    );
}

#[test]
fn test_last_of_pwcoin_2() {
    assert_eq!(
        test_repl_outcome(vec![
            "(defconstant CREATE_COIN 51)",
            "(defun check-password (password)",
            "  (let ((password-hash (sha256 password))",
            "        (real-hash 0x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824))",
            "    (= password-hash real-hash)",
            "    )",
            "  )",
            "(defconstant password \"hello\")",
            "(defconstant new_puzhash 0xdeadbeef)",
            "(defconstant amount 1)",
            "(if (check-password password)",
            "  (list (list CREATE_COIN new_puzhash amount))",
            "  (x)",
            "  )"
        ]).unwrap().unwrap(),
        "(q (51 0xdeadbeef 1))"
    );
}

#[test]
fn test_repl_supports_at_capture() {
    assert_eq!(
        test_repl_outcome(vec![
            "(defun F (A (@ Z (B C)) D) (c (+ A B C D) Z))",
            "(F 1 (q 2 3) 4)",
        ])
        .unwrap()
        .unwrap(),
        "(q 10 2 3)"
    );
}

#[test]
fn test_collatz() {
    assert_eq!(
        test_repl_outcome(vec![
            "(defun-inline odd (X) (logand X 1))",
            "(defun collatz (N X)",
            "  (if (= X 1)",
            "    N",
            "    (let ((incN (+ N 1)))",
            "      (if (odd X)",
            "        (collatz incN (+ 1 (* 3 X)))",
            "        (collatz incN (/ X 2))",
            "        )",
            "      )",
            "    )",
            "  )",
            "(collatz 0 3)"
        ])
        .unwrap()
        .unwrap(),
        "(q . 7)"
    );
}

#[test]
fn test_mod_in_repl() {
    assert_eq!(
        test_repl_outcome(vec!["(a (mod (X) (+ 1 (* 3 X))) (list 3))"])
            .unwrap()
            .unwrap(),
        "(q . 10)"
    );
}

#[test]
fn test_eval_forever_primitive() {
    assert!(test_repl_outcome(vec!["(defconstant RUNME (2 1 1))", "(a RUNME RUNME)"]).is_err());
}

#[test]
fn test_eval_forever_recursive() {
    assert!(test_repl_outcome(vec!["(defun more (N) (more N))", "(more 3)"]).is_err());
}

#[test]
fn test_eval_a_bit_more_than_forever_recursive() {
    assert!(test_repl_outcome_with_stack_limit(
        vec![
        "(defun tricky (N) (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ N 1)))))))))))))))))",
        "(tricky 3)"
    ],
        Some(10)
    )
    .is_err());
}

#[test]
fn test_eval_less_than_forever_recursive() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(
            vec![
                "(defun tricky (N) (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ N 1)))))))))))))))))",
                "(tricky 3)"
            ],
            Some(50)
        )
            .unwrap()
            .unwrap(),
        "(q . 4)"
    );
}

// This shows partial evaluation.  Use of certain constant names such as 'a' and
// 'c' disrupts this process, which I intend to fix in a separate pr.
#[test]
fn test_eval_list_with_constants_z() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(vec!["(defconstant z 3)", "(list x y z)"], Some(50))
            .unwrap()
            .unwrap(),
        "(c x (c y (q 3)))"
    );
}

#[test]
fn test_eval_list_with_constants_yz() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(
            vec!["(defconstant y 2)", "(defconstant z 3)", "(list x y z)"],
            Some(50)
        )
        .unwrap()
        .unwrap(),
        "(c x (q 2 3))"
    );
}

#[test]
fn test_eval_list_with_constants_xyz() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(
            vec![
                "(defconstant x 1)",
                "(defconstant y 2)",
                "(defconstant z 3)",
                "(list x y z)"
            ],
            Some(50)
        )
        .unwrap()
        .unwrap(),
        "(q 1 2 3)"
    );
}

#[test]
fn test_eval_list_partially_evaluated_abc() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(vec!["(list a b c)"], Some(50))
            .unwrap()
            .unwrap(),
        "(c a (c b (c c (q))))"
    );
}

#[test]
fn test_eval_list_partially_evaluated_xyz() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(vec!["(list x y z)"], Some(50))
            .unwrap()
            .unwrap(),
        "(c x (c y (c z (q))))"
    );
}

#[test]
fn test_lambda_eval_5() {
    assert_eq!(
        test_repl_outcome_with_stack_limit(
            vec![
                "(defun GetFun (L) (lambda ((& L) X) (+ X L)))",
                "(a (GetFun 10) (list 3))"
            ],
            None
        )
        .unwrap()
        .unwrap(),
        "(q . 13)"
    );
}
