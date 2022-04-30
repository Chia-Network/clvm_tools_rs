use rand::random;
use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm_tools::sha256tree;
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::clvm::{
    convert_to_clvm_rs, extract_program_and_env, parse_and_run, path_to_function, sha256tree,
};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

fn test_compiler_clvm(to_run: &String, args: &String) -> Result<Rc<SExp>, RunFailure> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    parse_and_run(
        &mut allocator,
        runner,
        &"*test*".to_string(),
        &to_run,
        &args,
    )
}

#[test]
fn test_sexp_parse_1() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"()".to_string()).map(|x| x[0].to_string());
    assert_eq!(res, Ok("()".to_string()));
}

#[test]
fn test_sexp_parse_2() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"55".to_string()).and_then(|x| x[0].get_number());
    assert_eq!(res, Ok(55_i32.to_bigint().unwrap()));
}

#[test]
fn test_sexp_parse_3() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"hello".to_string()).and_then(|x| x[0].get_number());
    assert_eq!(res, Ok(448378203247_i64.to_bigint().unwrap()));
}

#[test]
fn test_sexp_parse_4() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"\"hello\"".to_string()).and_then(|x| x[0].get_number());
    assert_eq!(res, Ok(448378203247_i64.to_bigint().unwrap()));
}

#[test]
fn test_sexp_parse_5() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"(3 . 4)".to_string()).map(|x| x[0].to_string());
    assert_eq!(res, Ok("(3 . 4)".to_string()));
}

#[test]
fn test_sexp_parse_6() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"(\" \" . 3)".to_string()).map(|x| x[0].to_string());
    assert_eq!(res, Ok("(\" \" . 3)".to_string()));
}

#[test]
fn test_sexp_parse_7() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(loc, &"(3 . \" \")".to_string()).map(|x| x[0].to_string());
    assert_eq!(res, Ok("(3 . \" \")".to_string()));
}

#[test]
fn test_sexp_parse_8() {
    let loc = Srcloc::start(&"*test*".to_string());
    let res = parse_sexp(
        loc,
        &"(a (q 2 4 (c 2 (c 6 ()))) (c (q 13 26729 \"there\" \"fool\") 1))".to_string(),
    )
    .map(|x| x[0].to_string());
    assert_eq!(
        res,
        Ok("(a (q 2 4 (c 2 (c 6 ()))) (c (q 13 26729 \"there\" \"fool\") 1))".to_string())
    );
}

#[test]
fn test_clvm_1() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = test_compiler_clvm(
        &"(a (q 2 4 (c 2 (c 6 ()))) (c (q 13 26729 \"there\" \"fool\") 1))".to_string(),
        &"()".to_string(),
    )
    .unwrap();
    let want = parse_sexp(loc, &"(\"there\" \"fool\")".to_string()).unwrap();

    assert!(result.equal_to(want[0].borrow()));
}

#[test]
fn test_clvm_2() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result =
        test_compiler_clvm(
            &"(a (q 2 (q 2 2 (c 2 (c 3 (q)))) (c (q 2 (i 5 (q 4 (q . 4) (c 9 (c (a 2 (c 2 (c 13 (q)))) (q)))) (q 1)) 1) 1)) 1)".to_string(),
            &"(1 2)".to_string(),
        ).unwrap();
    let want = parse_sexp(loc, &"(4 1 (4 2 ()))".to_string()).unwrap();

    assert!(result.equal_to(want[0].borrow()));
}

#[test]
fn test_clvm_3() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = test_compiler_clvm(
        &"(2 (3 (1) (1 16 (1 . 1) (1 . 3)) (1 16 (1 . 5) (1 . 8))) 1)".to_string(),
        &"()".to_string(),
    )
    .unwrap();
    let want = parse_sexp(loc, &"13".to_string()).unwrap();

    assert!(result.equal_to(want[0].borrow()));
}

#[test]
fn test_clvm_4() {
    let loc = Srcloc::start(&"*test*".to_string());
    let result = test_compiler_clvm(
        &"(divmod (1 . 300000003392) (1 . 10000000))".to_string(),
        &"()".to_string(),
    )
    .unwrap();
    let want = parse_sexp(loc, &"(30000 . 3392)".to_string()).unwrap();

    assert!(result.equal_to(want[0].borrow()));
}

#[test]
fn modern_sha256tree_1() {
    let mut allocator = Allocator::new();
    let srcloc = Srcloc::start(&"*".to_string());
    let modern_sha256 = sha256tree(Rc::new(SExp::Nil(srcloc)));
    let null = allocator.null();
    let old_sha256 = sha256tree::sha256tree(&mut allocator, null);
    assert_eq!(&modern_sha256, old_sha256.data());
}

#[test]
fn modern_sha256tree_2() {
    let mut allocator = Allocator::new();
    let srcloc = Srcloc::start(&"*".to_string());
    let modern_sexp = Rc::new(SExp::Cons(
        srcloc.clone(),
        Rc::new(SExp::Atom(srcloc.clone(), vec![9])),
        Rc::new(SExp::Cons(
            srcloc.clone(),
            Rc::new(SExp::Integer(srcloc.clone(), 11_u32.to_bigint().unwrap())),
            Rc::new(SExp::Nil(srcloc.clone())),
        )),
    ));
    let modern_sha256 = sha256tree(modern_sexp.clone());
    let old_sexp = convert_to_clvm_rs(&mut allocator, modern_sexp.clone()).unwrap();
    let old_sha256 = sha256tree::sha256tree(&mut allocator, old_sexp);
    assert_eq!(&modern_sha256, old_sha256.data());
}

#[test]
fn test_hash_path() {
    let loc = Srcloc::start(&"*".to_string());

    for _ in 0..100 {
        let mut wanted_expr: SExp = random();
        let mut used_exprs = HashSet::new();
        while wanted_expr.to_string() == "()" {
            wanted_expr = random();
        }
        used_exprs.insert(wanted_expr.to_string());
        let wanted_hash = sha256tree(Rc::new(wanted_expr.clone()));
        let mut wanted_path = bi_one();
        let wanted_steps: usize = random();
        let mut full_expr = wanted_expr.clone();

        for _ in 0..wanted_steps % 5 {
            let right_side = random();
            wanted_path *= 2;
            let mut new_expr: SExp = random();
            while used_exprs.contains(&new_expr.to_string()) || path_to_function(Rc::new(new_expr.clone()), &wanted_hash) != None {
                new_expr = random();
            }
            used_exprs.insert(new_expr.to_string());
            let new_expr = if right_side {
                wanted_path += 1;
                SExp::Cons(loc.clone(), Rc::new(new_expr), Rc::new(full_expr.clone()))
            } else {
                SExp::Cons(loc.clone(), Rc::new(full_expr.clone()), Rc::new(new_expr))
            };
            if !used_exprs.contains(&new_expr.to_string()) {
                full_expr = new_expr;
            }
        }

        let detected_path = path_to_function(Rc::new(full_expr.clone()), &wanted_hash).unwrap();
        println!(
            "find {} in {}: want path {} got path {}",
            wanted_expr.to_string(),
            full_expr.to_string(),
            wanted_path,
            detected_path
        );
        assert_eq!(detected_path, wanted_path);
    }
}

#[test]
fn test_extract_program_and_env() {
    let loc = Srcloc::start(&"*".to_string());
    let program = Rc::new(enlist(
        loc.clone(),
        vec![
            Rc::new(SExp::Integer(loc.clone(), 2_u32.to_bigint().unwrap())),
            Rc::new(SExp::Integer(loc.clone(), 99_u32.to_bigint().unwrap())),
            Rc::new(enlist(
                loc.clone(),
                vec![
                    Rc::new(SExp::Integer(loc.clone(), 4_u32.to_bigint().unwrap())),
                    Rc::new(SExp::Integer(loc.clone(), 101_u32.to_bigint().unwrap())),
                    Rc::new(SExp::Integer(loc.clone(), 1_u32.to_bigint().unwrap())),
                ],
            )),
        ],
    ));

    let ep = extract_program_and_env(program).unwrap();
    assert_eq!(ep.0.to_string(), "99");
    assert_eq!(ep.1.to_string(), "101");
}
