use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::clvm::run;
use crate::compiler::compiler::{compile_file, DefaultCompilerOpts};
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

fn compile_string(content: &String) -> Result<String, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let opts = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));

    compile_file(&mut allocator, runner, opts, &content, &mut HashMap::new()).map(|x| x.to_string())
}

fn run_string_maybe_opt(
    content: &String,
    args: &String,
    fe_opt: bool,
) -> Result<Rc<SExp>, CompileErr> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(&"*test*".to_string()));
    let srcloc = Srcloc::start(&"*test*".to_string());
    opts = opts
        .set_frontend_opt(fe_opt)
        .set_search_paths(&vec!["resources/tests".to_string()]);
    let sexp_args = parse_sexp(srcloc.clone(), &args).map_err(|e| CompileErr(e.0, e.1))?[0].clone();

    compile_file(
        &mut allocator,
        runner.clone(),
        opts,
        &content,
        &mut HashMap::new(),
    )
    .and_then(|x| {
        run(
            &mut allocator,
            runner,
            Rc::new(HashMap::new()),
            Rc::new(x),
            sexp_args,
        )
        .map_err(|e| match e {
            RunFailure::RunErr(l, s) => CompileErr(l, s),
            RunFailure::RunExn(l, s) => CompileErr(l, s.to_string()),
        })
    })
}

fn run_string(content: &String, args: &String) -> Result<Rc<SExp>, CompileErr> {
    run_string_maybe_opt(content, args, false)
}

fn run_string_opt(content: &String, args: &String) -> Result<Rc<SExp>, CompileErr> {
    run_string_maybe_opt(content, args, true)
}

#[test]
fn compile_test_1() {
    let result = compile_string(
        &"(mod () (defmacro testmacro (A) (qq (+ 1 (unquote A)))) (testmacro 3))".to_string(),
    )
    .unwrap();
    assert_eq!(result, "(2 (1 16 (1 . 1) (1 . 3)) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_2() {
    let result =
        compile_string(
            &"(mod () (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @))) (if () (+ 1 3) (+ 5 8)))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 2 (3 (1) (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 5) (1 . 8)) 1)) 1) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_3() {
    let result = compile_string(&"(mod (A) (include *standard-cl-21*) A)".to_string()).unwrap();
    assert_eq!(result, "(2 (1 . 5) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_4() {
    let result =
        compile_string(
            &"(mod () (defmacro if (A B C) (qq (a (i (unquote A) (com (unquote B)) (com (unquote C))) @))) (if () (+ 1 3) (+ 5 8)))".to_string()
        ).unwrap();
    assert_eq!(result, "(2 (1 2 (3 (1) (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 5) (1 . 8)) 1)) 1) (4 (1) 1))".to_string());
}

#[test]
fn compile_test_5() {
    let result =
        compile_string(
            &"(mod (X) (include *standard-cl-21*) (defmacro testmacro (x) (qq (+ 1 (unquote x)))) (if X (testmacro 3) (testmacro 4)))".to_string()
        ).unwrap();
    assert_eq!(
        result,
        "(2 (1 2 (3 5 (1 2 (1 16 (1 . 1) (1 . 3)) 1) (1 2 (1 16 (1 . 1) (1 . 4)) 1)) 1) (4 (1) 1))"
            .to_string()
    );
}

#[test]
fn compile_test_6() {
    let result = compile_string(&"(mod () (list 1 2 3))".to_string()).unwrap();
    assert_eq!(
        result,
        "(2 (1 4 (1 . 1) (4 (1 . 2) (4 (1 . 3) (1)))) (4 (1) 1))".to_string()
    );
}

fn run_test_1_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &"(mod () (defun f (a b) (+ (* a a) b)) (f 3 1))".to_string(),
        &"()".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "10".to_string());
}

#[test]
fn compile_test_7() {
    let result =
        compile_string(&"(mod (X) (include *standard-cl-21*) (/ X 10))".to_string()).unwrap();
    assert_eq!(result, "(2 (1 5 (20 5 (1 . 10))) (4 (1) 1))".to_string());
}

#[test]
fn run_test_1() {
    run_test_1_maybe_opt(false);
}

#[test]
fn run_test_1_opt() {
    run_test_1_maybe_opt(true);
}

fn run_test_2_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &"(mod (c) (defun f (a b) (+ (* a a) b)) (f 3 c))".to_string(),
        &"(4)".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "13".to_string());
}

#[test]
fn run_test_2() {
    run_test_2_maybe_opt(false);
}

#[test]
fn run_test_2_opt() {
    run_test_2_maybe_opt(true);
}

fn run_test_3_maybe_opt(opt: bool) {
    let result =
        run_string_maybe_opt(
            &"(mod (arg_one) (defun factorial (input) (if (= input 1) 1 (* (factorial (- input 1)) input))) (factorial arg_one))".to_string(),
            &"(5)".to_string(),
            opt
        ).unwrap();
    assert_eq!(result.to_string(), "120".to_string());
}

#[test]
fn run_test_3() {
    run_test_3_maybe_opt(false);
}

#[test]
fn run_test_3_opt() {
    run_test_3_maybe_opt(true);
}

fn run_test_4_maybe_opt(opt: bool) {
    let result =
        run_string_maybe_opt(
            &"(mod () (defun makelist (a) (if a (c (q . 4) (c (f a) (c (makelist (r a)) (q . ())))) (q . ()))) (makelist (q . (1 2 3))))".to_string(),
            &"()".to_string(),
            opt
        ).unwrap();
    assert_eq!(result.to_string(), "(4 1 (4 2 (4 3 ())))".to_string());
}

#[test]
fn run_test_4() {
    run_test_4_maybe_opt(false);
}

#[test]
fn run_test_4_opt() {
    run_test_4_maybe_opt(true);
}

fn run_test_5_maybe_opt(opt: bool) {
    let result =
        run_string_maybe_opt(&"(mod (a) (list 1 2))".to_string(), &"()".to_string(), opt).unwrap();
    assert_eq!(result.to_string(), "(1 2)".to_string());
}

#[test]
fn run_test_5() {
    run_test_5_maybe_opt(false);
}

#[test]
fn run_test_5_opt() {
    run_test_5_maybe_opt(true);
}

fn run_test_6_maybe_opt(opt: bool) {
    let result =
        run_string_maybe_opt(
            &"(mod args (defmacro square (input) (qq (* (unquote input) (unquote input)))) (defun sqre_list (my_list) (if my_list (c (square (f my_list)) (sqre_list (r my_list))) my_list)) (sqre_list args))".to_string(),
            &"(10 9 8 7)".to_string(),
            opt
        ).unwrap();
    assert_eq!(result.to_string(), "(100 81 64 49)".to_string());
}

#[test]
fn run_test_6() {
    run_test_6_maybe_opt(false);
}

#[test]
fn run_test_6_opt() {
    run_test_6_maybe_opt(true);
}

fn run_test_7_maybe_opt(opt: bool) {
    let result =
        run_string_maybe_opt(
            &"(mod (PASSWORD_HASH password new_puzhash amount) (defconstant CREATE_COIN 51) (defun check_password (PASSWORD_HASH password new_puzhash amount) (if (= (sha256 password) PASSWORD_HASH) (list (list CREATE_COIN new_puzhash amount)) (x))) (check_password PASSWORD_HASH password new_puzhash amount))".to_string(),
            &"(0x2ac6aecf15ac3042db34af4863da46111da7e1bf238fc13da1094f7edc8972a1 \"sha256ftw\" 0x12345678 1000000000)".to_string(),
            opt
        ).unwrap();
    assert_eq!(
        result.to_string(),
        "((51 0x12345678 1000000000))".to_string()
    );
}

#[test]
fn run_test_7() {
    run_test_7_maybe_opt(false);
}

#[test]
fn run_test_7_opt() {
    run_test_7_maybe_opt(true);
}

fn run_test_8_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &"(mod (a b) (let ((x (+ a 1)) (y (+ b 1))) (+ x y)))".to_string(),
        &"(5 8)".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "15".to_string());
}

#[test]
fn run_test_8() {
    run_test_8_maybe_opt(false);
}

#[test]
fn run_test_8_opt() {
    run_test_8_maybe_opt(true);
}

#[test]
fn run_inlines() {
    let result = run_string(
        &"(mod (a) (defun-inline F (x) (+ x 1)) (defun-inline G (x) (* x 2)) (G (F a)))"
            .to_string(),
        &"(13)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "28".to_string());
}

#[test]
fn run_inlines_2() {
    let result = run_string(
        &"(mod (a b) (defun-inline F (x y) (+ x y)) (defun-inline G (x y) (- y x)) (defun-inline H (x y) (* x y)) (H (F a b) (G a b)))"
            .to_string(),
        &"(103 107)".to_string(),
    )
        .unwrap();
    // H (103 + 107) (108 - 104)
    // 210 * 4
    // 840
    assert_eq!(result.to_string(), "840".to_string());
}

#[test]
fn run_test_at_form() {
    let result = run_string(
        &"(mod (a b) (- (@ 11) (@ 5)))".to_string(),
        &"(51 107)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "56".to_string());
}

#[test]
fn run_test_intermediate_let_1() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun-inline letbinding_$_264 args args)
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}
        .to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "((100) 101)".to_string());
}

#[test]
fn run_test_intermediate_let_1_1() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun-inline letbinding_$_265 args args)
                (defun letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}
        .to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "(((100) 101) 102)".to_string());
}

#[test]
fn run_test_intermediate_let_1_2() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun letbinding_$_265 args args)
                (defun letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}
        .to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "(((100) 101) 102)".to_string());
}

#[test]
fn run_test_intermediate_let_1_3() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun-inline letbinding_$_265 args args)
                (defun letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}
        .to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "(((100) 101) 102)".to_string());
}

#[test]
fn run_test_intermediate_let_1_4() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun letbinding_$_265 args args)
                (defun-inline letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}.to_string(),
        &"(100)".to_string(),
    ).unwrap();
    assert_eq!(result.to_string(), "(((100) 101) 102)".to_string());
}

#[test]
fn run_test_intermediate_let_2() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun-inline letbinding_$_265 args args)
                (defun-inline letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}.to_string(),
        &"(100)".to_string(),
    ).unwrap();
    assert_eq!(result.to_string(), "(((100) 101) 102)".to_string());
}

#[test]
fn run_test_intermediate_let_final() {
    let result = run_string(
        &indoc! {"
            (mod (a)
                (defun-inline letbinding_$_265 (((a) x_$_263) y) (+ x_$_263 y))
                (defun-inline letbinding_$_264 ((a) x) (letbinding_$_265 (c (c a ()) (c x ())) (+ x 1)))
                (letbinding_$_264 (r @) (+ a 1))
                )
        "}.to_string(),
        &"(100)".to_string(),
    ).unwrap();
    assert_eq!(result.to_string(), "203".to_string());
}

#[test]
fn run_test_let_star_2_deep() {
    let result = run_string(
        &"(mod (a) (let* ((x (+ a 1)) (y (+ x 1))) (+ x y)))".to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "203".to_string());
}

#[test]
fn run_test_let_star_3_deep() {
    let result = run_string(
        &"(mod (a) (let* ((x (+ a 1)) (y (+ x 1)) (z (* a y))) (+ x y z)))".to_string(),
        &"(100)".to_string(),
    )
    .unwrap();
    assert_eq!(result.to_string(), "10403".to_string());
}

#[test]
fn run_test_normal_with_macro_call() {
    let result = run_string(
        &"(mod (a) (defun test-value (a n) (if (- a n) 9999 1111)) (c (test-value a 3) (test-value a 2)))".to_string(),
        &"(3)".to_string()
    ).unwrap();
    assert_eq!(result.to_string(), "(1111 . 9999)".to_string());
}

#[test]
fn run_test_inline_with_macro_call() {
    let result = run_string(
        &"(mod (X) (defun-inline test-value (a n) (if (- a n) 9999 1111)) (c (test-value X 3) (test-value X 2)))".to_string(),
        &"(3)".to_string()
    ).unwrap();
    assert_eq!(result.to_string(), "(1111 . 9999)".to_string());
}

/*
 * - TODO: Ensure that a compileform name inlined and shadowed in a macro doesn't
 *   disrupt macro execution.
 *   ... i'll have to think about how to handle this.
 * /
#[test]
fn run_test_inline_with_macro_call_tricky_naming() {
    let result = run_string(
        &"(mod (a) (defun-inline test-value (a n) (if (- a n) 9999 1111)) (c (test-value a 3) (test-value a 2)))".to_string(),
        &"(3)".to_string()
    ).unwrap();
    assert_eq!(result.to_string(), "(1111 . 9999)".to_string());
}
 */

fn run_test_9_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &"(mod (a) (defun f (i) (let ((x (not i)) (y (* i 2))) (+ x y))) (f a))".to_string(),
        &"(0)".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "1".to_string());
}

#[test]
fn run_test_9() {
    run_test_9_maybe_opt(false);
}

#[test]
fn run_test_9_opt() {
    run_test_9_maybe_opt(true);
}

fn run_test_10_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &"(mod (a) (defun f (i) (let ((x (not i)) (y (* i 2))) (+ x y))) (f a))".to_string(),
        &"(3)".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "6".to_string());
}

#[test]
fn run_test_10() {
    run_test_10_maybe_opt(false);
}

#[test]
fn run_test_10_opt() {
    run_test_10_maybe_opt(true);
}

#[test]
fn test_defconstant() {
    let result =
        run_string(&indoc!{"
            (mod (password new_puzhash amount)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              (defconstant CREATE_COIN 51)
              (defun check-password (password)
                (let ((password-hash (sha256 password))
                      (real-hash 0x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824))
                  (= password-hash real-hash)
                  )
                )

              (if (check-password password)
                (list (list CREATE_COIN new_puzhash amount))
                (x)
                )
              )
        "}.to_string(),
                   &"(hello 0x5f5767744f91c1c326d927a63d9b34fa7035c10e3eb838c44e3afe127c1b7675 2)".to_string(),
        ).unwrap();

    assert_eq!(
        result.to_string(),
        "((51 0x5f5767744f91c1c326d927a63d9b34fa7035c10e3eb838c44e3afe127c1b7675 2))".to_string()
    );
}

#[test]
fn inline_compile_test() {
    let result = compile_string(
        &indoc! {"
        (mod (A)
          (include *standard-cl-21*)

          (defun-inline f (x) (+ x 1))
          (f A)
          )
        "}
        .to_string(),
    )
    .unwrap();
    assert_eq!(result, "(2 (1 16 5 (1 . 1)) (4 (1) 1))".to_string());
}

#[test]
fn cant_redefine_defconstant() {
    let result = compile_string(
        &"(mod (X) (include *standard-cl-21*) (defconstant A 3) (defconstant A 4) A)".to_string(),
    );
    assert!(result.is_err());
}

#[test]
fn cant_redefine_defun_with_defun() {
    let inline_if_not_zero = |i, c| {
        if i & c == 0 {
            ""
        } else {
            "-inline"
        }
    };
    for i in 0..4 {
        let result = compile_string(&format!(
            indoc! {"
            (mod (A)
              (include *standard-cl-21*)

              (defun{} f (x) (+ x 1))
              (defun{} f (y) (- y 1))

              (f A)
              )
            "},
            inline_if_not_zero(i, 2),
            inline_if_not_zero(i, 1)
        ));
        assert!(result.is_err());
    }
}

#[test]
fn test_at_destructure_1() {
    let result = run_string(
        &indoc! {"
            (mod (A (@ Z (B C)) D)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              A
              )
        "}
        .to_string(),
        &"(1 (2 3) 4)".to_string(),
    )
    .unwrap();

    assert_eq!(result.to_string(), "1".to_string());
}

#[test]
fn test_at_destructure_2() {
    let result = run_string(
        &indoc! {"
            (mod (A (@ Z (B C)) D)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              Z
              )
        "}
        .to_string(),
        &"(1 (2 3) 4)".to_string(),
    )
    .unwrap();

    assert_eq!(result.to_string(), "(2 3)".to_string());
}

#[test]
fn test_at_destructure_3() {
    let result = run_string(
        &indoc! {"
            (mod (A (@ Z (B C)) D)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              B
              )
        "}
        .to_string(),
        &"(1 (2 3) 4)".to_string(),
    )
    .unwrap();

    assert_eq!(result.to_string(), "2".to_string());
}

#[test]
fn test_at_destructure_4() {
    let result = run_string(
        &indoc! {"
            (mod (A (@ Z (B C)) D)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              C
              )
        "}
        .to_string(),
        &"(1 (2 3) 4)".to_string(),
    )
    .unwrap();

    assert_eq!(result.to_string(), "3".to_string());
}

#[test]
fn test_at_destructure_5() {
    let result = run_string(
        &indoc! {"
            (mod (A (@ Z (B C)) D)
              (include *standard-cl-21*) ;; Specify chialisp-21 compilation.
              D
              )
        "}
        .to_string(),
        &"(1 (2 3) 4)".to_string(),
    )
    .unwrap();

    assert_eq!(result.to_string(), "4".to_string());
}

fn test_collatz_maybe_opt(opt: bool) {
    let result = run_string_maybe_opt(
        &indoc! {"
            (mod (A)
             (include *standard-cl-22*)
             (defun-inline odd (X) (logand X 1))
             (defun collatz (N X)
              (if (= X 1)
               N
               (let ((incN (+ N 1)))
                (if (odd X)
                 (collatz incN (+ 1 (* 3 X)))
                 (collatz incN (/ X 2))
                )
               )
              )
             )
             (collatz 0 A)
            )
        "}
        .to_string(),
        &"(4)".to_string(),
        opt,
    )
    .unwrap();
    assert_eq!(result.to_string(), "2");
}

#[test]
fn test_collatz() {
    test_collatz_maybe_opt(false);
}

#[test]
fn fancy_nested_let_bindings_should_work() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod X
     (include *standard-cl-21*)
     (defun do-something (solutions se)
        (if solutions
             (let (
                    (R (f solutions))
                    (S (- se 99))
                  )
                (if (= (f solutions) 99)
                    S
                    (let ((something-else (+ se R)))
                        (do-something (r solutions) something-else)
                    )
                )
             )
             100
        )
    )

    (do-something X 1)
    )
        "}
        .to_string(),
        &"(1 2 3 100 99)".to_string(),
        false,
    )
    .unwrap();
    assert_eq!(result.to_string(), "8");
}

#[test]
fn let_as_argument() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod (X)
     (include *standard-cl-21*)
     (defun twice (x) (* x 2))
     (defun plus (x y) (+ x y))
     (plus (let ((t (twice X))) t) 3))
        "}
        .to_string(),
        &"(5)".to_string(),
        false,
    )
    .unwrap();
    assert_eq!(result.to_string(), "13");
}

#[test]
fn recursive_let_complicated_arguments() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod (X Y)
     (include *standard-cl-21*)
     (defun G (A (@ pt (X Y))) (+ A X Y))
     (defun F (@ pt (X Y)) (let ((X1 (+ X 1)) (Y1 (+ Y 3))) (G X1 (let ((p (list X1 Y1))) p))))
     (F X Y)
     )
        "}
        .to_string(),
        &"(7 13)".to_string(),
        false,
    )
    .unwrap();
    assert_eq!(result.to_string(), "32");
}

#[test]
fn test_let_structure_access_1() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod (X Y)
      (include *standard-cl-21*)
      (let ((a 1)
            (b 2))
        (let ((A (+ a 1))
               (XX (+ X 1))
               (C (+ b b)))
         (if Y
            (let ((D (+ C 1))
                  (E (+ XX Y)))
              (c D E)
              )
            (let ((D XX)
                  (E (+ XX Y)))
              (c D E)
              )
          )
         )
       )
      )
        "}
        .to_string(),
        &"(7 13)".to_string(),
        false,
    )
    .unwrap();
    // a = 1
    // b = 2
    // A = 2
    // XX = X + 1
    // C = 2 + 2
    // if Y
    //   D = 5
    //   E = X + Y + 1
    // else
    //   D = X + 1
    //   E = X + Y + 1
    assert_eq!(result.to_string(), "(5 . 21)");
}

#[test]
fn test_let_structure_access_2() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod (X Y)
      (include *standard-cl-21*)
      (let ((a 1)
            (b 2))
        (let* ((A (+ a 1))
               (XX (+ X 1))
               (C (+ A b)))
         (if Y
            (let ((D (+ C 1))
                  (E (+ XX Y)))
              (c D E)
              )
            (let ((D XX)
                  (E (+ XX Y)))
              (c D E)
              )
          )
         )
       )
      )
        "}
        .to_string(),
        &"(7 13)".to_string(),
        false,
    )
    .unwrap();
    // a = 1
    // b = 2
    // A = 2
    // XX = X + 1
    // C = 2 + 2
    // if Y
    //   D = 5
    //   E = X + Y + 1
    // else
    //   D = X + 1
    //   E = X + Y + 1
    assert_eq!(result.to_string(), "(5 . 21)");
}

#[test]
fn test_let_inline_1() {
    let result = run_string_maybe_opt(
        &indoc! {"
    (mod (G)
      (include *standard-cl-21*)
      (defun-inline F (X) (let ((Y (* X 2))) (+ Y 1)))
      (F G)
      )
        "}
        .to_string(),
        &"(5)".to_string(),
        false,
    )
    .unwrap();
    assert_eq!(result.to_string(), "11");
}

#[test]
fn read_of_hex_constant_in_modern_chialisp() {
    let result = run_string(
        &indoc! {"(mod () (include *standard-cl-21*) (sha256 (q . 1) (q . 0xf22ada22a0ed015000ea157013ee62dc6ce337a649ec01054fc62ed6caac7eaf)))"}
        .to_string(),
        &"()".to_string(),
    )
        .unwrap();

    assert_eq!(
        result.to_string(),
        "36364122602940516403027890844760998025315693007634105146514094828976803085567".to_string()
    );
}

#[test]
fn hash_handling_test_2() {
    let result = run_string(
        &indoc! {"(mod () (include *standard-cl-21*) (sha256 (q . 1) (q . 1)))"}.to_string(),
        &"()".to_string(),
    )
    .unwrap();

    assert_eq!(
        result.to_string(),
        "-44412188149083219915772186748035909266791016930429887947443501395007119841358"
    );
}

#[test]
fn hash_handling_test_3() {
    let result = run_string(
        &indoc! {"(mod () (include *standard-cl-21*) (sha256 1 0))"}.to_string(),
        &"()".to_string(),
    )
    .unwrap();

    assert_eq!(
        result.to_string(),
        "34356466678672179216206944866734405838331831190171667647615530531663699592602"
    );
}

#[test]
fn sebastian_hash_test_1() {
    let result = run_string(
        &indoc! {"
(mod (MOD_HASH TOKEN_A_AMOUNT TOKEN_B_AMOUNT K token_a_delta token_b_delta)
    (include \"condition_codes.clvm\")
    (include \"curry-and-treehash.clinc\")
    (include *standard-cl-21*)

    (defun sha256tree1 (TREE)
        (if (l TREE)
            (sha256 2 (sha256tree1 (f TREE)) (sha256tree1 (r TREE)))
            (sha256 1 TREE)
        )
    )
    (defun return-new-coin (mod_hash new_token_a_amount new_token_b_amount K)
        (list (list mod_hash (sha256tree1 mod_hash))
            (list
                CREATE_COIN
               (puzzle-hash-of-curried-function
                    mod_hash (sha256tree1 mod_hash)
                )
                1
            )
        )
    )

    (let (
         (new_token_a_amount (+ TOKEN_A_AMOUNT token_a_delta))
         (new_token_b_amount (+ TOKEN_B_AMOUNT token_b_delta))
        )
        (if (all (= K (* new_token_a_amount new_token_b_amount)) (> new_token_a_amount 0) (> new_token_b_amount 0) )
            (return-new-coin MOD_HASH new_token_a_amount new_token_b_amount K)
            (x new_token_a_amount new_token_b_amount)
        )
    ))"}
        .to_string(),
        &"(0xf22ada22a0ed015000ea157013ee62dc6ce337a649ec01054fc62ed6caac7eaf 10000 200 2000000 -2000 50)".to_string()
    )
        .unwrap();

    assert_eq!(result.to_string(), "((0xf22ada22a0ed015000ea157013ee62dc6ce337a649ec01054fc62ed6caac7eaf 36364122602940516403027890844760998025315693007634105146514094828976803085567) (51 -54330418644829767769717664495663952010367061369724157609947295940464695774007 1))");
}

#[test]
fn sebastian_hash_test_2() {
    let result = run_string(
        &indoc! {"
(mod (MOD_HASH TOKEN_A_AMOUNT TOKEN_B_AMOUNT K token_a_delta token_b_delta)
    (include \"condition_codes.clvm\")
    (include \"curry-and-treehash.clinc\")

    (defun sha256tree1 (TREE)
        (if (l TREE)
            (sha256 2 (sha256tree1 (f TREE)) (sha256tree1 (r TREE)))
            (sha256 1 TREE)
        )
    )
    (defun return-new-coin (mod_hash new_token_a_amount new_token_b_amount K)
        (list (list mod_hash (sha256tree1 mod_hash))
            (list
                CREATE_COIN
               (puzzle-hash-of-curried-function
                    mod_hash (sha256tree1 mod_hash)
                )
                1
            )
        )
    )

        (if (all (= K (* (+ TOKEN_A_AMOUNT token_a_delta) (+ TOKEN_B_AMOUNT token_b_delta))) (> (+ TOKEN_A_AMOUNT token_a_delta) 0) (> (+ TOKEN_B_AMOUNT token_b_delta) 0) )
            (return-new-coin MOD_HASH (+ TOKEN_A_AMOUNT token_a_delta) (+ TOKEN_B_AMOUNT token_b_delta) K)
            (x (+ TOKEN_A_AMOUNT token_a_delta) (+ TOKEN_B_AMOUNT token_b_delta))
        )
    )"}
        .to_string(),
        &"(0xf22ada22a0ed015000ea157013ee62dc6ce337a649ec01054fc62ed6caac7eaf 10000 200 2000000 -2000 50)".to_string()
    )
        .unwrap();

    assert_eq!(result.to_string(), "((0xf22ada22a0ed015000ea157013ee62dc6ce337a649ec01054fc62ed6caac7eaf 36364122602940516403027890844760998025315693007634105146514094828976803085567) (51 -54330418644829767769717664495663952010367061369724157609947295940464695774007 1))");
}

#[test]
fn test_modern_inline_at_capture() {
    let result = run_string(
        &indoc! {"
(mod (Z)
  (include *standard-cl-21*)
  (defun-inline check_lineage_proof
    (
      THIS_MOD_HASH
      TYPES
      (@ lineage_proof (foo bar))
      conditions
    )
    (if TYPES
        (x lineage_proof)
        conditions
    )
  )

  (check_lineage_proof 1 2 Z 4)
  )"}
        .to_string(),
        &"(99)".to_string(),
    )
    .unwrap_err();

    assert_eq!(result.1, "clvm raise in (8 5) (() 99)");
}
