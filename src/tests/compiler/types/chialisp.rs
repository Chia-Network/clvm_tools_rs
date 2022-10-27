use num_bigint::ToBigInt;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompileErr;
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::{HasLoc, Srcloc};
use crate::compiler::typechia::{context_from_args_and_type, standard_type_context};
use crate::compiler::types::ast::{Polytype, Type, TypeVar};
use crate::compiler::types::theory::TypeTheory;
use crate::tests::compiler::types::types::{
    check_expression_against_type_with_context, flatten_exists,
};

#[test]
fn test_chialisp_context_from_args_and_type_empty() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::Nil(loc.clone())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "()", "Unit", false);
}

#[test]
fn test_chialisp_context_from_args_and_type_single_atom_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "X", "Any", false);
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone())),
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "X", "Any", false);
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_any_pair() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone())),
        )),
        &Type::TAny(loc.clone()),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "X", "Any", false);
}

#[test]
fn test_chialisp_context_from_args_and_type_arg_with_list_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
        &Type::TApp(
            Rc::new(Type::TVar(TypeVar("List".to_string(), loc.clone()))),
            Rc::new(Type::TAtom(loc.clone(), None)),
        ),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "X", "(List Atom)", false);
}

#[test]
fn test_chialisp_context_from_args_and_type_single_arg_with_pair_type() {
    let loc = Srcloc::start(&"*test*".to_string());
    let context = context_from_args_and_type(
        &HashSet::new(),
        &standard_type_context(),
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(SExp::atom_from_string(loc.clone(), &"X".to_string())),
            Rc::new(SExp::Nil(loc.clone())),
        )),
        &Type::TPair(
            Rc::new(Type::TAtom(loc.clone(), None)),
            Rc::new(Type::TUnit(loc.clone())),
        ),
        bi_zero(),
        bi_one(),
    )
    .expect("should synthesize a context");
    check_expression_against_type_with_context(&context, "X", "Atom", false);
}

fn test_chialisp_program_typecheck(s: &str, flatten: bool) -> Result<Polytype, CompileErr> {
    let testname = "*test*".to_string();
    let loc = Srcloc::start(&testname);
    let context = standard_type_context();
    let opts = DefaultCompilerOpts::new(&testname);
    let pre_forms = parse_sexp(loc.clone(), s.bytes()).map_err(|e| CompileErr(e.0, e.1))?;
    let compileform = frontend(Rc::new(opts), pre_forms)?;
    let mut fcount: usize = 0;
    let mut held = HashMap::new();
    let target_type = context.typecheck_chialisp_program(&compileform)?;
    if flatten {
        Ok(flatten_exists(
            &context.reify(&target_type, None),
            &mut held,
            &mut fcount,
        ))
    } else {
        Ok(context.reify(&target_type, None))
    }
}

#[test]
fn test_chialisp_program_returning_unit_no_anno() {
    let ty = test_chialisp_program_typecheck("(mod () ())", false).expect("should type check");
    assert_eq!(ty, Type::TAny(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_unit_annotation() {
    let ty = test_chialisp_program_typecheck("(mod () : (Unit -> Unit) ())", false)
        .expect("should type check");
    assert_eq!(ty, Type::TUnit(ty.loc()));
}

#[test]
fn test_chialisp_program_returning_one_atom_annotation() {
    let ty = test_chialisp_program_typecheck("(mod (X) : ((Pair Atom Unit) -> Atom) X)", false)
        .expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_chialisp_program_doing_cons() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X) : (forall t0 ((Pair t0 Unit) -> (Pair t0 Unit))) (c X ()))",
        true,
    )
    .expect("should type check");
    assert_eq!(
        ty,
        Type::TPair(
            Rc::new(Type::TVar(TypeVar("t0".to_string(), ty.loc()))),
            Rc::new(Type::TUnit(ty.loc()))
        )
    );
}

#[test]
fn test_chialisp_program_doing_plus() {
    let ty = test_chialisp_program_typecheck(
        "(mod (X Y) : ((Pair Atom (Pair Atom Unit)) -> Atom) (+ X Y))",
        true,
    )
    .expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_chialisp_defun_sha256() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) : ((Pair Atom Unit) -> Atom32)
  (defun F (X) : ((Pair Atom Unit) -> Atom32)
    (sha256 1 X)
    )

  (F X)
  )"
        },
        true,
    )
    .expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap())));
}

#[test]
fn test_chialisp_defun_sha256_bad() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) : ((Pair Atom Unit) -> Atom32)
  (defun F (X) : ((Pair Atom32 Unit) -> Atom32)
    (sha256 1 X)
    )

  (F X)
  )"
        },
        false,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_defun_sha256_good() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) : ((Pair Atom32 Unit) -> Atom32)
  (defun F (X) : ((Pair Atom32 Unit) -> Atom32)
    (sha256 1 X)
    )

  (F X)
  )"
        },
        false,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_chialisp_with_arg_type_smoke_test() {
    let ty = test_chialisp_program_typecheck("(mod ((X : Atom)) -> Atom (+ X 1))", false)
        .expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_chialisp_with_arg_type_first_should_not_check() {
    let ty = test_chialisp_program_typecheck("(mod ((X : Atom)) -> Atom (f X))", false);
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_with_arg_type_first_should_check() {
    let ty = test_chialisp_program_typecheck("(mod ((X : (Pair Atom Unit))) -> Atom (f X))", false);
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_chialisp_with_arg_type_doesnt_check_not_atom32() {
    let ty =
        test_chialisp_program_typecheck("(mod ((X : (Pair Atom Unit))) -> Atom32 (+ 1 X))", false);
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_with_arg_type_doesnt_checks_atom32() {
    let ty = test_chialisp_program_typecheck(
        "(mod ((X : (Pair Atom Unit))) -> Atom32 (sha256 1 X))",
        false,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_function_returning_any_is_ok_as_atom32() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"(mod () -> Atom32
           (defun F () (sha256 1 1 1 1 1 1 1 1))
           (F)
           )"},
        false,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_chialisp_function_returning_atom_isnt_ok_as_atom32() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"(mod () -> Atom32
           (defun F () -> Atom (sha256 1 1 1 1 1 1 1 1))
           (F)
           )"},
        false,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_function_checks_result_type() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"(mod () -> Atom32
           (defun F () -> Atom (+ 1 1 1 1 1 1 1 1))
           (F)
           )"},
        false,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_chialisp_function_returning_atom_is_ok_as_atom32() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Atom32
  (defun F () -> Atom32 (sha256 1 1 1 1 1 1 1 1))
  (F)
  )"},
        false,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_if_smoke() {
    let ty = test_chialisp_program_typecheck("(mod (X) -> Atom (if X 2 3))", true)
        .expect("should check");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_if_not_right_type() {
    let ty = test_chialisp_program_typecheck("(mod (X) -> Atom32 (if X 2 3))", true);
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_conflicting_types() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Atom
  (defun G () -> (Pair Atom Unit) (c 1 ()))
  (G)
  )
        "},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_if_conflicting_types() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Atom
  (defun F () -> Atom 1)
  (defun G () -> (Pair Atom Unit) (c 1 ()))
  (if 1 (F) (G))
  )
        "},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_if_not_conflicting_types() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Any
  (defun F () -> (Nullable (Pair Atom Unit)) ())
  (defun G () -> (Nullable (Pair Atom Unit)) (c 1 ()))
  (if 1 (F) (G))
  )
        "},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn test_basic_abstract_type_decl() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : Mystery)) -> Mystery
   (deftype Mystery)
   X
   )
        "},
        true,
    )
    .expect("should typecheck");
    assert_eq!(ty, Type::TVar(TypeVar("Mystery".to_string(), ty.loc())));
}

#[test]
fn test_abstract_type_decl_synthesizes() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : Mystery)) -> Atom
   (deftype Mystery)
   X
   )
        "},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_struct_decl_easy() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : Struct)) -> Atom32
   (deftype Struct ((A . (B : Atom32)) C))
   (get_Struct_B X)
   )
        "},
        true,
    )
    .expect("should type check");
    assert_eq!(ty, Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap())));
}

#[test]
fn test_struct_decl_easy_fail() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : Struct)) -> Atom32
   (deftype Struct (((A : Atom) . (B : Atom32)) C))
   (get_Struct_A X)
   )
        "},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_struct_construction() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((A : Atom) (B : Atom32)) -> Struct
   (deftype Struct (((A : Atom) . (B : Atom32)) C))
   (new_Struct A B ())
   )
        "},
        true,
    )
    .expect("should typecheck");
    assert_eq!(ty, Type::TVar(TypeVar("Struct".to_string(), ty.loc())));
}

#[test] // Struct2 isn't compatible with Struct1
fn test_wrong_struct_construction() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((A : Atom) (B : Atom32)) -> Struct1
   (deftype Struct1 (((A : Atom) . (B : Atom32)) C))
   (deftype Struct2 (((A : Atom) . (B : Atom)) C))
   (new_Struct2 A B ())
   )
        "},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_struct_construction_with_var() {
    let ty = test_chialisp_program_typecheck(
        "(mod () -> (S Atom) (deftype S a ((A : a))) (new_S 1))",
        true,
    )
    .expect("should typecheck");
    assert_eq!(
        ty,
        Type::TApp(
            Rc::new(Type::TVar(TypeVar("S".to_string(), ty.loc()))),
            Rc::new(Type::TAtom(ty.loc(), None))
        )
    );
}

#[test]
fn test_struct_construction_with_var_member() {
    let ty = test_chialisp_program_typecheck(
        "(mod () -> Atom32 (deftype S a ((A : a))) (defun hash_S (S) (sha256 (get_S_A S))) (hash_S (new_S 1)))",
        true
    ).expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap())));
}

#[test]
fn test_coerce() {
    let ty = test_chialisp_program_typecheck(
        "(mod () -> Atom32 (deftype S a ((A : a))) (defun hash_S (S) (+ (get_S_A S))) (coerce (hash_S (new_S 1))))",
        true
    ).expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap())));
}

#[test]
fn test_bless() {
    let ty = test_chialisp_program_typecheck(
        "(mod () -> (Exec Atom32) (deftype S a ((A : a))) (defun hash_S (S) (sha256 (get_S_A S))) (bless (hash_S (new_S 1))))",
        true
    ).expect("should typecheck");
    assert_eq!(
        ty,
        Type::TExec(Rc::new(Type::TAtom(
            ty.loc(),
            Some(32_u32.to_bigint().unwrap())
        )))
    );
}

#[test]
fn test_simple_type() {
    let ty = test_chialisp_program_typecheck(
        "(mod () -> Hash (deftype Hash ((A : Atom32))) (new_Hash (sha256 1)))",
        true,
    )
    .expect("should typecheck");
    assert_eq!(ty, Type::TVar(TypeVar("Hash".to_string(), ty.loc())));
}

#[test]
fn test_let_type_1() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Hash
  (include *standard-cl-21*)
  (deftype Hash ((A : Atom32)))
  (let ((h (sha256 1)))
    (new_Hash h)
    )
  )"},
        true,
    )
    .expect("should typecheck");
    assert_eq!(ty, Type::TVar(TypeVar("Hash".to_string(), ty.loc())));
}

#[test]
fn test_head_of_list() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : (List Atom))) -> Atom32
  (defun F ((P : Atom32) (X : (List Atom))) -> Atom32 (if X (F (sha256 P (f X)) (r X)) P))
  (F (sha256 1) X)
  )"},
        true,
    )
    .expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap())));
}

#[test]
fn test_fixedlist() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X Y Z) : ((FixedList Atom Atom32 Atom) -> (FixedList Atom32 Atom))
  (list Y Z)
  )"},
        true,
    )
    .expect("should typecheck");
    assert_eq!(
        ty,
        Type::TPair(
            Rc::new(Type::TAtom(ty.loc(), Some(32_u32.to_bigint().unwrap()))),
            Rc::new(Type::TPair(
                Rc::new(Type::TAtom(ty.loc(), None)),
                Rc::new(Type::TUnit(ty.loc()))
            ))
        )
    );
}

#[test]
fn test_curry1() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((code : (Exec ((FixedList Atom Atom) -> Atom)))) -> Atom
  (defun curry-1 (code arg) : (forall a (forall b (forall c ((FixedList (Exec ((Pair a b) -> c)) a) -> (Exec (b -> c))))))
    (coerce (list 2 (c 1 code) (list 4 (c 1 arg) 1)))
    )
  (a (curry-1 code 2) (list 3))
  )"},
        true,
    )
        .expect("should typecheck");
    assert_eq!(ty, Type::TAtom(ty.loc(), None));
}

#[test]
fn test_struct_is_not_random_pair() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> (FixedList Atom (FixedList Atom32))
  (deftype A ((thing : Atom)))
  (deftype B ((hash : Atom32)))
  (deftype Counter x ((count : Atom) (obj : x)))
  (new_Counter V (new_B (sha256 3)))
  )
"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn test_struct_is_own_type() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> (Counter B)
     (deftype A ((thing : Atom)))
     (deftype B ((hash : Atom32)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (new_Counter V (new_B (sha256 3)))
    )
"},
        true,
    )
    .expect("should typecheck");
    assert_eq!(
        ty,
        Type::TApp(
            Rc::new(Type::TVar(TypeVar("Counter".to_string(), ty.loc()))),
            Rc::new(Type::TVar(TypeVar("B".to_string(), ty.loc())))
        )
    );
}

#[test]
fn test_struct_is_not_other_struct_type() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> (Counter B)
     (deftype A ((thing : Atom)))
     (deftype B ((hash : Atom32)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (new_Counter V (new_A 3))
    )
"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_1() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X)
      (defun F (P X) (if X (F (sha256 P (f X)) (r X)) P))
      (F (sha256 1) X)
      )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_2() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
      (defun F (P X) (if X (F (sha256 P (f X)) (r X)) P))
      (F (sha256 1) X)
      )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_3() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F (P X) : (Any -> Any) (if X (F (sha256 P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_4() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F (P X) : (Any -> Atom) (if X (F (sha256 P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_5() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F (P X) : (Any -> Atom32) (if X (F (sha256 P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_6() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F ((P : Atom) X) -> Atom32 (if X (F (sha256 P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_7() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F ((P : Atom32) X) -> Atom32 (if X (F (* P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_8() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod (X) -> Atom32
     (defun F ((P : Atom32) X) -> Atom32 (if X (F (sha256 P (f X)) (r X)) P))
     (F 1 X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_9() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((X : (List Atom))) -> Atom32
     (defun F ((P : Atom32) (X : (List Atom))) -> Atom32 (if X (F (sha256 P (f X)) (r X)) P))
     (F (sha256 1) X)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_10() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> Counter
     (deftype Counter ((count : Atom)))
     (list V)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_11() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> Counter
     (deftype Counter ((count : Atom)))
     (new_Counter V)
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_12() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> Atom
     (deftype A ((thing : Atom)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (get_A_thing (get_Counter_obj (new_Counter V (new_A 3))))
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_13() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((V : Atom)) -> (FixedList Atom Atom32)
 (deftype A ((thing : Atom)))
 (deftype B ((hash : Atom32)))
 (deftype Counter x ((count : Atom) (obj : x)))
 (list
  (get_A_thing (get_Counter_obj (new_Counter V (new_A 3))))
  (get_B_hash (get_Counter_obj (new_Counter V (new_B (sha256 4)))))
 )
)"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_14() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Unit
 (defmacro simply (S) (qq (com (unquote S))))
 (simply (list 1 2 3))
)"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_15() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod () -> Unit
 (defmacro simply (S) (qq (com (unquote S))))
 (a (simply (list 1 2 3)) ())
)"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn tut_example_16() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((code : (Exec ((FixedList Atom Atom) -> Atom)))) -> Atom
 (+ 1 (a code (list 2 3)))
)"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn tut_example_17() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
(mod ((code : (Exec ((FixedList Atom Atom) -> Atom)))) -> Atom
 (defun curry-1 (code arg) : (forall a (forall b (forall c ((FixedList (Exec ((Pair a b) -> c)) a) -> (Exec (b -> c))))))
  (coerce (list 2 (c 1 code) (list 4 (c 1 arg) 1)))
 )
 (a (curry-1 code 2) (list 3))
)"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn difficult_judgement_about_nested_type() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
    (mod ((V : Atom)) -> B
     (deftype A ((thing : Atom)))
     (deftype B ((hash : Atom32)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (get_Counter_obj (new_Counter V (new_A 3)))
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}

#[test]
fn basic_nested_judgement_correct() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
    (mod ((V : Atom)) -> (Counter B)
     (deftype A ((thing : Atom)))
     (deftype B ((hash : Atom32)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (new_Counter V (new_B (sha256 3)))
    )"},
        true,
    );
    assert_eq!(ty.is_err(), false);
}

#[test]
fn basic_nested_judgement_wrong() {
    let ty = test_chialisp_program_typecheck(
        indoc! {"
    (mod ((V : Atom)) -> (Counter B)
     (deftype A ((thing : Atom)))
     (deftype B ((hash : Atom32)))
     (deftype Counter x ((count : Atom) (obj : x)))
     (new_Counter V (new_A (+ V 3)))
    )"},
        true,
    );
    assert_eq!(ty.is_err(), true);
}
