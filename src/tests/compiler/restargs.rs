use crate::tests::compiler::compiler::run_string;

// All tests needed for rest calls:
//
// Call from non-inline to inline
// 01 - Too many arguments, no tail position argument to absorb.
// 02 - Too many arguments, tail position argument to absorb, &rest.
// 03 - Too many arguments, tail position argument to absorb, no &rest.
// 04 - Exact number of arguments, no tail position argument.
// 05 - Exact number of arguments, tail position argument, &rest.
// 06 - Exact number of arguments, tail position argument, no &rest.
// 07 - Too few arguments, &rest, tail.
// 08 - Too few arguments, &rest, no tail.
// 09 - Too few arguments, no &rest, tail. (error)
// 10 - Too few arguments, &rest, no tail.
// 11 - Too few arguments, &rest, tail.
// Call from inline to inline
// 12 - Too many arguments, no tail position argument to absorb.
// 13 - Too many arguments, tail position argument to absorb, &rest.
// 14 - Too many arguments, tail position argument to absorb, no &rest.
// 15 - Exact number of arguments, no tail position argument.
// 16 - Exact number of arguments, tail position argument, &rest.
// 17 - Exact number of arguments, tail position argument, no &rest.
// 18 - Too few arguments, &rest, tail.
// 19 - Too few arguments, &rest, no tail.
// 20 - Too few arguments, no &rest, tail. (error)
// 21 - Too few arguments, &rest, no tail.
// 22 - Too few arguments, &rest, tail.
// Call from non-inline to non-inline
// 23 - Too many arguments, no tail position argument to absorb.
// 24 - Too many arguments, tail position argument to absorb, &rest.
// 25 - Too many arguments, tail position argument to absorb, no &rest.
// 26 - Exact number of arguments, no tail position argument.
// 27 - Exact number of arguments, tail position argument, &rest.
// 28 - Exact number of arguments, tail position argument, no &rest.
// 29 - Too few arguments, &rest, tail.
// 30 - Too few arguments, &rest, no tail.
// 31 - Too few arguments, no &rest, tail. (not error)
// 32 - Too few arguments, &rest, no tail.
// 33 - Too few arguments, &rest, tail.
// Call from inline to non-inline
// 34 - Too many arguments, no tail position argument to absorb.
// 35 - Too many arguments, tail position argument to absorb, &rest.
// 36 - Too many arguments, tail position argument to absorb, no &rest.
// 37 - Exact number of arguments, no tail position argument.
// 38 - Exact number of arguments, tail position argument, &rest.
// 39 - Exact number of arguments, tail position argument, no &rest.
// 40 - Too few arguments, &rest, tail.
// 41 - Too few arguments, &rest, no tail.
// 42 - Too few arguments, no &rest, tail. (not error)
// 43 - Too few arguments, &rest, no tail.
// 44 - Too few arguments, &rest, tail.
//
#[test]
fn test_simple_inline_toomany_args_01() {
    let prog = indoc! {"
(mod (X Y Z)
  (include *standard-cl-23*)

  (defun-inline F (A B) (+ A B))

  (F X Y Z)
  )"}.to_string();
    let res = run_string(&prog, &"(5 7 9)".to_string()).expect("should compile and run");
    assert_eq!(res.to_string(), "12");
}

#[test]
fn test_simple_inline_toomany_args_improper_tail_02() {
    let prog = indoc! {"
(mod (X Y Z)
  (include *standard-cl-23*)

  (defun sum (Xs)
    (if Xs
      (+ (f Xs) (sum (r Xs)))
      ()
      )
    )

  (defun-inline F (A B . C) (* A B (sum C)))

  (F X Y 99 101 &rest Z)
  )"}.to_string();
    let res = run_string(&prog, &"(5 7 (301 313))".to_string()).expect("should compile and run");
    assert_eq!(res.to_string(), "28490");
}

#[test]
fn test_simple_inline_toomany_args_improper_no_tail_03() {
    let prog = indoc! {"
(mod (X Y)
  (include *standard-cl-23*)

  (defun sum (Xs)
    (if Xs
      (+ (f Xs) (sum (r Xs)))
      ()
      )
    )

  (defun-inline F (A B . C) (* A B (sum C)))

  (F X Y 99 101)
  )"}.to_string();
    let res = run_string(&prog, &"(5 7)".to_string()).expect("should compile and run");
    assert_eq!(res.to_string(), "7000");
}

#[test]
fn test_simple_rest_call_27() {
    let prog = indoc! {"
(mod X
  (include *standard-cl-23*)

  (defun F Xs
    (if Xs
      (+ (f Xs) (F &rest (r Xs)))
      ()
      )
    )

  (F &rest X)
  )"}
    .to_string();
    let res = run_string(&prog, &"(13 99 144)".to_string()).expect("should compile and run");
    assert_eq!(res.to_string(), "256");
}

#[test]
fn test_simple_rest_call_inline_38() {
    let prog = indoc! {"
(mod X
  (include *standard-cl-23*)

  (defun sum (Xs)
    (if Xs
      (+ (f Xs) (sum (r Xs)))
      ()
      )
    )

  (defun-inline F (A1 . A2) (* A1 (sum A2)))

  (F 3 &rest X)
  )"}
    .to_string();
    let res = run_string(&prog, &"(13 99 144)".to_string()).expect("should compile and run");
    assert_eq!(res.to_string(), "768");
}

