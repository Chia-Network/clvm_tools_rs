use crate::tests::compiler::compiler::run_string;

#[test]
fn test_defmac_basic_0() {
    let prog = indoc! {"
    (mod (X)
      (defmac double-arg (A) (list (string->symbol (string-append (symbol->string A) \"1\")) (string->symbol (string-append (symbol->string A) \"2\"))))
      (defun strange (double-arg X) (+ X1 X2))
      (strange X (* 2 X))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "9");
}

#[test]
fn test_defmac_basic_shared_constant() {
    let prog = indoc! {"
    (mod (X)
      (defconstant twostring \"2\")
      (defmac double-arg (A) (list (string->symbol (string-append (symbol->string A) \"1\")) (string->symbol (string-append (symbol->string A) twostring))))
      (defun strange (double-arg X) (+ X1 X2))
      (c twostring (strange X (* 2 X)))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(\"2\" . 9)");
}

#[test]
fn test_defmac_basic_shared_constant_not_string_with_string_operator() {
    let prog = indoc! {"
    (mod (X)
      (defconstant twostring 2)
      (defmac double-arg (A) (list (string->symbol (string-append (symbol->string A) \"1\")) (string->symbol (string-append (symbol->string A) twostring))))
      (defun strange (double-arg X) (+ X1 X2))
      (c twostring (strange X (* 2 X)))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string());
    assert!(res.is_err());
}

#[test]
fn test_defmac_basic_shared_constant_not_string_with_string_operator_fun() {
    let prog = indoc! {"
    (mod (X)
      (defconstant twostring \"2\")
      (defun make-arg-list (A) (list (string->symbol (string-append (symbol->string A) \"1\")) (string->symbol (string-append (symbol->string A) twostring))))
      (defmac double-arg (A) (make-arg-list A))
      (defun strange (double-arg X) (+ X1 X2))
      (c twostring (strange X (* 2 X)))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(\"2\" . 9)");
}

#[test]
fn test_defmac_basic_test_is_string_pos() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (string? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify \"test\"))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 1 . \"test\")");
}

#[test]
fn test_defmac_basic_test_is_string_neg() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (string? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify test))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 2 . test)");
}

#[test]
fn test_defmac_basic_test_is_symbol_pos() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (symbol? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify test))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 1 . test)");
}

#[test]
fn test_defmac_basic_test_is_symbol_neg() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (symbol? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify \"test\"))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 2 . \"test\")");
}

#[test]
fn test_defmac_basic_test_is_number_pos() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (number? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify 7))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 1 . 7)");
}

#[test]
fn test_defmac_basic_test_is_number_neg() {
    let prog = indoc! {"
    (mod (X)
      (defmac classify (S)
        (if (number? S)
          (qq (c 1 (unquote S)))
          (qq (c 2 (unquote S)))
          )
        )
      (c X (classify \"test\"))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 2 . \"test\")");
}

#[test]
fn test_defmac_create_cond_form() {
    let prog = indoc! {"
    ;; Make a simple list match ala ocaml/elm/haskell.
    ;;
    ;; The real version will be more elaborate.  This is a test case and a demo.
    (mod (X)
        (defun list-nth (L N)
          (if N
            (list-nth (r L) (- N 1))
            (f L)
            )
          )

        (defun list-len (L N)
          (if L
            (list-len (r L) (+ N 1))
            N
            )
          )

        ;; From a list of bindings or constants, build a matcher for the elements.
        (defun gather-bindings-list (expr tomatch)
          (if (not expr)
            ()
            ()
            )
          )

        (defun gather-bindings (condition expr rest)
          (qq
            (if (= (list-len (unquote expr)) (unquote (list-len condition)))
              (unquote
                (let*
                  (
                    (bindings-and-checks (gather-bindings-and-checks condition expr))
                    (bindings (f bindings-and-checks))
                    (checks (r bindings-and-checks))
                  )
                  (qq (if checks (let bindings rest)))
                  )
                )
              ()
              )
            )
          )

        ;; For each pair, emit an expression that checks for the requested pattern
        ;; and returns either the requested result or allows the following matchers
        ;; to run.
        (defun handle-matches (expr matches)
          (if (not matches)
            (qq (x (unquote expr)))
            (let
              (
                (condition (f (f expr)))
                (code (f (r (f expr))))
                )
              (qq (if (unquote (make-match-expr condition expr)) (unquote code) (unquote (handle-matches (r matches)))))
              )
            )
          )

        ;; match as below.
        (defmac match (expr . matches) (handle-matches expr matches))

        (match X
          ((16 x y) (c 1 (+ x y)))
          ((3 () b c) c)
          ((3 (q . 1) b c) b)
          (x x)
          )
        )
    "}
    .to_string();
    let res = run_string(&prog, &"(3 () 1001 1002)".to_string()).unwrap();
    assert_eq!(res.to_string(), "1002");
}
