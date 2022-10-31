use num_bigint::ToBigInt;

#[cfg(test)]
use rand::distributions::Standard;
#[cfg(test)]
use rand::prelude::*;
#[cfg(test)]
use rand::Rng;
#[cfg(test)]
use rand_chacha::ChaChaRng;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero, Stream};
use crate::classic::clvm_tools::binutils::disassemble;
use crate::classic::clvm_tools::cmds::launch_tool;
use crate::classic::clvm_tools::node_path::NodePath;
use crate::compiler::clvm::convert_to_clvm_rs;
use crate::compiler::sexp;
use crate::util::{number_from_u8, Number};

const NUM_GEN_ATOMS: usize = 16;

fn do_basic_brun(args: &Vec<String>) -> String {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"run".to_string(), 0);
    return s.get_value().decode();
}

fn do_basic_run(args: &Vec<String>) -> String {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"run".to_string(), 2);
    return s.get_value().decode();
}

#[test]
fn basic_run_test() {
    assert_eq!(
        do_basic_run(&vec!("run".to_string(), "(mod (A B) (+ A B))".to_string())).trim(),
        "(+ 2 5)".to_string()
    );
}

#[test]
fn add_1_test() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(opt (com (q . (+ 6 55))))".to_string()
        ))
        .trim(),
        "(q . 61)".to_string()
    );
}

#[test]
fn div_test() {
    assert_eq!(
        do_basic_run(&vec!("run".to_string(), "(mod (X) (/ X 10))".to_string())).trim(),
        "(f (divmod 2 (q . 10)))".to_string()
    );
}

#[test]
fn brun_y_1_test() {
    let testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut sym_path = testpath.clone();
    sym_path.push("resources/tests/stage_2/brun-y-1.sym");
    assert_eq!(
        do_basic_brun(
            &vec!(
                "brun".to_string(),
                "-y".to_string(),
                sym_path.into_os_string().into_string().unwrap(),
                "(a (q . (a 2 (c 2 (c 5 (q . ()))))) (c (q . (a (i (= 5 (q . 1)) (q . (q . 1)) (q . (* 5 (a 2 (c 2 (c (- 5 (q . 1)) (q . ()))))))) 1)) 1))".to_string(),
                "(10)".to_string()
            )
        ).trim(),
        indoc! {"0x375f00
            
            (\"fact\" 10) => 0x375f00
            
            (\"fact\" 9) => 0x058980
            
            (\"fact\" 8) => 0x009d80
            
            (\"fact\" 7) => 5040
            
            (\"fact\" 6) => 720
            
            (\"fact\" 5) => 120
            
            (\"fact\" 4) => 24
            
            (\"fact\" 3) => 6
            
            (\"fact\" 2) => 2
            
            (\"fact\" 1) => 1"}
    );
}

#[test]
fn brun_v_test() {
    assert_eq!(
        do_basic_brun(&vec!(
            "brun".to_string(),
            "-v".to_string(),
            "(a (q + (q . 3) (q . 5)) 1)".to_string()
        ))
        .trim(),
        indoc! {"8
            
            (a 2 3) [((a (q 16 (q . 3) (q . 5)) 1))] => 8
            
            3 [((a (q 16 (q . 3) (q . 5)) 1))] => ()
            
            2 [((a (q 16 (q . 3) (q . 5)) 1))] => (a (q 16 (q . 3) (q . 5)) 1)
            
            (a (q 16 (q . 3) (q . 5)) 1) [()] => 8
            
            1 [()] => ()
            
            (q 16 (q . 3) (q . 5)) [()] => (+ (q . 3) (q . 5))
            
            (+ (q . 3) (q . 5)) [()] => 8
            
            (q . 5) [()] => 5
            
            (q . 3) [()] => 3"}
    );
}

#[test]
fn brun_constant_test() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defconstant X 3) X)".to_string()
        ))
        .trim(),
        "(q . 3)".to_string()
    );
}

#[test]
fn at_capture_destructure_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) A)".to_string()
        ))
        .trim(),
        "2"
    );
}

#[test]
fn at_capture_destructure_2() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) Z)".to_string()
        ))
        .trim(),
        "5"
    );
}

#[test]
fn at_capture_destructure_3() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) B)".to_string()
        ))
        .trim(),
        "9"
    );
}

#[test]
fn at_capture_destructure_4() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) C)".to_string()
        ))
        .trim(),
        "21"
    );
}

#[test]
fn at_capture_destructure_5() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) D)".to_string()
        ))
        .trim(),
        "11"
    );
}

#[test]
fn at_capture_inline_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) X) (F 97 98))".to_string()
        ))
        .trim(),
        "(q . 97)"
    );
}

#[test]
fn at_capture_inline_2() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) Y) (F 97 98))".to_string()
        ))
        .trim(),
        "(q . 98)"
    );
}

#[test]
fn at_capture_inline_3() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) pt) (F (+ 117 1) (+ 98 1)))".to_string()
        ))
        .trim(),
        "(q 118 99)"
    );
}

#[test]
fn at_capture_inline_4() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (A (@ pt (X Y))) (list (list A X Y) pt)) (F 115 (list 99 77)))".to_string()
        ))
            .trim(),
        "(q (115 99 77) (99 77))"
    );
}

#[test]
fn inline_destructure_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F ((A . B)) (+ A B)) (F (c 3 7)))".to_string()
        ))
        .trim(),
        "(q . 10)"
    );
}

#[test]
fn test_forms_of_destructuring_allowed_by_classic_1() {
    assert_eq!(
        do_basic_run(&vec![
            "run".to_string(),
            "(mod (A) (defun-inline foo (X Y . Z) (i X Y . Z)) (foo A 2 3))".to_string()
        ])
        .trim(),
        "(i 2 (q . 2) (q . 3))"
    );
}

#[test]
fn test_num_encoding_just_less_than_5_bytes() {
    let res = do_basic_run(&vec!["run".to_string(), "4281419728".to_string()])
        .trim()
        .to_string();
    assert_eq!(res, "0x00ff3147d0");
}

#[test]
fn test_divmod() {
    let res = do_basic_run(&vec![
        "run".to_string(),
        "(/ 78962960182680 4281419728)".to_string(),
    ])
    .trim()
    .to_string();
    assert_eq!(res, "18443");
}

#[cfg(test)]
pub struct RandomClvmNumber {
    pub intended_value: Number,
}

#[cfg(test)]
pub fn random_clvm_number<R: Rng + ?Sized>(rng: &mut R) -> RandomClvmNumber {
    // Make a number by creating some random atom bytes.
    // Set high bit randomly.
    let natoms = rng.gen_range(0..=NUM_GEN_ATOMS);
    let mut result_bytes = Vec::new();
    for _ in 0..=natoms {
        let mut new_bytes = sexp::random_atom_name(rng, 3)
            .iter()
            .map(|x| {
                if rng.gen() {
                    // The possibility of negative values.
                    x | 0x80
                } else {
                    *x
                }
            })
            .collect();
        result_bytes.append(&mut new_bytes);
    }
    let num = number_from_u8(&result_bytes);

    RandomClvmNumber {
        intended_value: num,
    }
}

#[cfg(test)]
impl Distribution<RandomClvmNumber> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> RandomClvmNumber {
        random_clvm_number(rng)
    }
}

// Finally add property based testing in here.
#[test]
fn test_encoding_properties() {
    let mut rng = ChaChaRng::from_entropy();
    for _ in 1..=200 {
        let number_spec: RandomClvmNumber = rng.gen();

        // We'll have it compile a constant value.
        // The representation of the number will come out most likely
        // as a hex constant.
        let serialized_through_run = do_basic_run(&vec![
            "run".to_string(),
            format!("(q . {})", number_spec.intended_value),
        ])
        .trim()
        .to_string();

        // If we can subtract the original value from the encoded value and
        // get zero, then we did the right thing.
        let cancelled_through_run = do_basic_run(&vec![
            "run".to_string(),
            format!(
                "(- {} {})",
                serialized_through_run, number_spec.intended_value
            ),
        ])
        .trim()
        .to_string();
        assert_eq!(cancelled_through_run, "()");
    }
}

const SEXP_RNG_HORIZON: usize = 13;
const SEXP_DEPTH: usize = 2;

#[cfg(test)]
fn gather_paths(
    path_map: &mut HashMap<Vec<u8>, Number>,
    p: Number,
    mask: Number,
    sexp: &sexp::SExp,
) {
    let this_path = p.clone() | mask.clone();
    match sexp {
        sexp::SExp::Atom(_, x) => {
            path_map.insert(x.clone(), this_path);
        }
        sexp::SExp::Cons(_, a, b) => {
            let next_mask = mask * 2_u32.to_bigint().unwrap();
            gather_paths(path_map, p.clone(), next_mask.clone(), a.borrow());
            gather_paths(path_map, this_path, next_mask.clone(), b.borrow());
        }
        _ => {}
    }
}

// Ensure our atoms are not taken up as operators during the reading process.
#[cfg(test)]
fn stringize(sexp: &sexp::SExp) -> sexp::SExp {
    match sexp {
        sexp::SExp::Cons(l, a, b) => sexp::SExp::Cons(
            l.clone(),
            Rc::new(stringize(a.borrow())),
            Rc::new(stringize(b.borrow())),
        ),
        sexp::SExp::Atom(l, n) => sexp::SExp::QuotedString(l.clone(), b'"', n.clone()),
        _ => sexp.clone(),
    }
}

#[test]
fn test_check_tricky_arg_path_random() {
    let mut rng = ChaChaRng::from_entropy();
    // Make a very deep random sexp and make a path table in it.
    let random_tree = Rc::new(stringize(&sexp::random_sexp(&mut rng, SEXP_RNG_HORIZON)));
    let mut deep_tree = random_tree.clone();

    let mut path_map = HashMap::new();
    gather_paths(&mut path_map, bi_zero(), bi_one(), &random_tree);
    let mut deep_path = bi_one();
    for _ in 1..=SEXP_DEPTH {
        deep_path *= 2_u32.to_bigint().unwrap();
        if rng.gen() {
            deep_path |= bi_one();
            deep_tree = Rc::new(sexp::SExp::Cons(
                random_tree.loc(),
                Rc::new(sexp::SExp::Nil(random_tree.loc())),
                deep_tree,
            ));
        } else {
            deep_tree = Rc::new(sexp::SExp::Cons(
                random_tree.loc(),
                deep_tree.clone(),
                Rc::new(sexp::SExp::Nil(random_tree.loc())),
            ));
        }
    }
    // Now we have a very deep tree and a path to our sexp.
    // We'll test whether node path serializes to the right thing by
    // checking that we can reach all the atoms in our tree.
    for (k, v) in path_map {
        let np = NodePath::new(Some(deep_path.clone()));
        let up = NodePath::new(Some(v.clone()));
        let path_bytes = np.add(up).as_path();
        let program = sexp::SExp::Cons(
            random_tree.loc(),
            Rc::new(sexp::SExp::Atom(random_tree.loc(), vec![b'a'])),
            Rc::new(sexp::SExp::Cons(
                random_tree.loc(),
                Rc::new(sexp::SExp::QuotedString(
                    random_tree.loc(),
                    b'"',
                    path_bytes.raw().clone(),
                )),
                Rc::new(sexp::SExp::Cons(
                    random_tree.loc(),
                    Rc::new(sexp::SExp::Cons(
                        random_tree.loc(),
                        Rc::new(sexp::SExp::Atom(random_tree.loc(), vec![b'q'])),
                        deep_tree.clone(),
                    )),
                    Rc::new(sexp::SExp::Nil(random_tree.loc())),
                )),
            )),
        );

        let res = do_basic_run(&vec![
            "run".to_string(),
            program.to_string(),
            "()".to_string(),
        ])
        .trim()
        .to_string();
        let mut allocator = Allocator::new();
        let converted = convert_to_clvm_rs(
            &mut allocator,
            Rc::new(sexp::SExp::Atom(random_tree.loc(), k.clone())),
        )
        .unwrap();
        let disassembled = disassemble(&mut allocator, converted);
        eprintln!("run {} want {} have {}", program, disassembled, res);
        assert_eq!(disassembled, res);
    }
}
