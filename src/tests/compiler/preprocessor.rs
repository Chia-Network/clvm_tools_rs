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
fn test_defmac_extension_from_function() {
    let prog = indoc! {"
    (mod (X)
      (defun FX (X) (symbol->string X))
      (defmac F (X) (FX X))
      (c 3 (F X))
      )
    "}
    .to_string();
    let res = run_string(&prog, &"(3)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(3 . \"X\")");
}

#[test]
fn test_defmac_if_extension() {
    let prog = indoc! {"
    (mod (X)
      (defun FX (X) (if X (number->string 1) 2))
      (defmac F (X) (c 1 (FX X)))
      (F X)
      )
    "}.to_string();
    let res = run_string(&prog, &"(9)".to_string()).unwrap();
    assert_eq!(res.to_string(), "\"1\"");
}

#[test]
fn test_defmac_create_match_form() {
    let prog = indoc! {"
    ;; Make a simple list match ala ocaml/elm/haskell.
    ;;
    ;; The real version will be more elaborate.  This is a test case and a demo.
    (mod X
        (include *standard-cl-21*)
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

        (defun funcall (name args) (c (string->symbol name) args))
        (defun quoted (X) (c 1 X))
        (defun equals (A B) (funcall \"=\" (list A B)))
        (defun emit-list-nth (L N) (funcall \"list-nth\" (list L N)))
        (defun emit-list-len (L N) (funcall \"list-len\" (list L N)))
        (defun emit-if (C T E) (funcall \"if\" (list C T E)))
        (defun emit-let (bindings body) (funcall \"let\" (list bindings body)))

        ;; Determine the size of each list as well as the constants and bindings
        ;; Return either a list of (number-of-elts matches bindings) or symbol.
        (defun build-matches-and-bindings (n pattern matches bindings)
            (if (not pattern)
                (list n matches bindings)
                (if (l pattern)
                    (if (symbol? (f pattern))
                        (build-matches-and-bindings (+ n 1) (r pattern) matches (c (c n (f pattern)) bindings))
                        (build-matches-and-bindings (+ n 1) (r pattern) (c (c n (f pattern)) matches) bindings)
                        )
                    pattern
                    )
                )
            )

        ;; Emit code that matches each match list for length and constants.
        (defun write-match-code (expr matches)
            (if (not matches)
                (quoted 1)
                (if (l (f matches))
                    (let*
                        (
                         (offset (f (f matches)))
                         (desire (r (f matches)))
                         (this-match (equals (quoted desire) (emit-list-nth expr (quoted offset))))
                         )
                      (if (not (r matches))
                          (list this-match)
                          (c this-match (write-match-code expr (r matches)))
                          )
                      )
                    (quoted 1)
                    )
                )
            )

        ;; Generate let bindings for the bindings indicated in the match.
        (defun let-bindings (expr bindings)
            (if (not bindings)
                ()
                (let
                    ((n (f (f bindings)))
                     (binding (r (f bindings)))
                     )
                  (c (list binding (emit-list-nth expr n)) (let-bindings expr (r bindings)))
                  )
                )
            )

        ;; Generate if expressions that match the indicates matches and return
        ;; the indicated code with bindings installed.
        (defun match-if (expr clauses)
            (if (not clauses)
                (list 8)
                (let
                    ((extracted-clause-data (build-matches-and-bindings 0 (f (f clauses)) () ()))
                     (code (f (r (f clauses))))
                     )
                  (if (l extracted-clause-data)
                      (let
                          (
                           (number-of-elts (f extracted-clause-data))
                           (matches (list-nth extracted-clause-data 1))
                           (bindings (list-nth extracted-clause-data 2))
                           )
                        (emit-if
                          (emit-if
                            (equals (emit-list-len expr 0) (quoted number-of-elts))
                            ;; then
                            (c (string->symbol \"logand\") (write-match-code expr matches))
                            ;; else
                            ()
                            )
                          ;; then
                          (emit-let (let-bindings expr bindings) code)
                          ;; else
                          (match-if expr (r clauses))
                          )
                        )
                      (emit-let (list (list extracted-clause-data expr)) code)
                      )
                     )
                )
            )

        ;; match as below.
        (defmac match (expr . matches) (match-if expr matches))

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

#[test]
fn test_defmac_stringq() {
    let prog = indoc! {"
      (mod ()
         (defmac is-string (X) (string? X))
         (list (is-string X) (is-string \"X\") (is-string 3))
         )
    "}.to_string();
    let res = run_string(&prog, &"()".to_string()).unwrap();
    assert_eq!(res.to_string(), "(() 1 ())");
}

#[test]
fn test_defmac_numberq() {
    let prog = indoc! {"
      (mod ()
         (defmac is-number (X) (number? X))
         (list (is-number X) (is-number \"X\") (is-number 3))
         )
    "}.to_string();
    let res = run_string(&prog, &"()".to_string()).unwrap();
    assert_eq!(res.to_string(), "(() () 1)");
}

#[test]
fn test_defmac_symbolq() {
    let prog = indoc! {"
      (mod ()
         (defmac is-symbol (X) (symbol? X))
         (list (is-symbol X) (is-symbol \"X\") (is-symbol 3))
         )
    "}.to_string();
    let res = run_string(&prog, &"()".to_string()).unwrap();
    assert_eq!(res.to_string(), "(1 () ())");
}

#[test]
fn test_defmac_string_to_symbol() {
    let prog = indoc! {"
      (mod ()
         (defmac is-symbol (X) (symbol? X))
         (list (is-symbol X) (is-symbol \"X\") (is-symbol 3))
         )
    "}.to_string();
    let res = run_string(&prog, &"()".to_string()).unwrap();
    assert_eq!(res.to_string(), "(1 () ())");
}

#[test]
fn test_defmac_string_to_symbol_converts() {
    let prog = indoc! {"
      (mod (X)
        (defmac let_pi (code) (qq (let (((unquote (string->symbol \"pi\")) 31415)) (unquote code))))
        (let_pi (+ pi X))
        )
    "}.to_string();
    let res = run_string(&prog, &"(5)".to_string()).unwrap();
    assert_eq!(res.to_string(), "31420");
}

#[test]
fn test_defmac_string_needs_conversion() {
    let prog = indoc! {"
      (mod (X)
        (defmac let_pi (code) (qq (let ((\"pi\" 31415)) (unquote code))))
        (let_pi (+ pi X))
        )
    "}.to_string();
    let res = run_string(&prog, &"(5)".to_string());
    assert!(res.is_err());
}

#[test]
fn test_defmac_string_substr_0() {
    let prog = indoc! {"
      (mod (X)
        (defmac first-letter-of (Q)
          (let ((first-character (substring (symbol->string Q) 0 1)))
            (qq (c (unquote first-character) (unquote (string->symbol first-character))))
            )
          )
        (first-letter-of Xanadu)
        )
    "}.to_string();
    let res = run_string(&prog, &"(5999)".to_string()).unwrap();
    assert_eq!(res.to_string(), "(\"X\" . 5999)");
}
