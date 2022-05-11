use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{t, Stream};
use crate::classic::clvm_tools::cmds::{launch_tool, OpcConversion, OpdConversion, TConversion};

use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::stages;
use crate::classic::clvm_tools::stages::stage_0::{DefaultProgramRunner, TRunProgram};
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;
use crate::classic::clvm_tools::NodePath::NodePath;

#[test]
fn basic_opd() {
    let mut allocator = Allocator::new();
    let result = OpdConversion {}
        .invoke(&mut allocator, &"80".to_string())
        .unwrap();
    assert_eq!(result.rest(), "()");
}

#[test]
fn nil_in_list_opd() {
    let mut allocator = Allocator::new();
    let result = OpdConversion {}
        .invoke(&mut allocator, &"ff8080".to_string())
        .unwrap();
    assert_eq!(result.rest(), "(())");
}

#[test]
fn big_decode_opd() {
    let mut allocator = Allocator::new();
    let mut testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    testpath.push("resources/tests");
    let mut in_path = testpath.clone();
    in_path.push("big_decode_in.txt");
    let mut out_path = testpath.clone();
    out_path.push("big_decode_out.txt");

    let expected = fs::read_to_string(in_path)
        .and_then(|input| {
            return fs::read_to_string(out_path).map(|output| t(input, output.trim().to_string()));
        })
        .unwrap();

    let result = OpdConversion {}
        .invoke(&mut allocator, &expected.first())
        .unwrap();
    assert_eq!(expected.rest(), result.rest());
}

fn run_from_source<'a>(allocator: &'a mut Allocator, src: String) -> NodePtr {
    let ir = read_ir(&src).unwrap();
    let assembled = assemble_from_ir(allocator, Rc::new(ir)).unwrap();
    let runner = DefaultProgramRunner::new();
    let null = allocator.null();
    let res = runner
        .run_program(allocator, assembled, null, None)
        .unwrap();
    return res.1;
}

fn compile_program<'a>(
    allocator: &'a mut Allocator,
    include_path: String,
    src: String,
) -> Result<String, EvalErr> {
    let run_script = stages::run(allocator);
    let runner = run_program_for_search_paths(&vec![include_path]);
    let input_ir = read_ir(&src);
    let input_program = assemble_from_ir(allocator, Rc::new(input_ir.unwrap())).unwrap();
    let input_sexp = allocator.new_pair(input_program, allocator.null()).unwrap();
    let res = runner.run_program(allocator, run_script, input_sexp, None);

    return res.map(|x| disassemble(allocator, x.1));
}

#[test]
fn quoted_negative() {
    let mut s = Stream::new(None);
    launch_tool(
        &mut s,
        &vec!["run".to_string(), "-d".to_string(), "(q . -3)".to_string()],
        &"run".to_string(),
        2,
    );
    let result = s.get_value().decode().trim().to_string();
    assert_eq!(result, "81fd".to_string());
}

#[test]
fn can_run_from_source_nil() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "()".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 0);
        }
        _ => {
            assert_eq!("expected atom", "");
        }
    }
}

#[test]
fn can_echo_quoted_nil() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(1)".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 0);
        }
        _ => {
            assert_eq!("expected atom", "");
        }
    }
}

#[test]
fn can_echo_quoted() {
    let mut allocator = Allocator::new();
    let null = allocator.null();
    let res = run_from_source(&mut allocator, "(1 ())".to_string());
    match allocator.sexp(res) {
        SExp::Pair(l, r) => {
            assert_eq!(l, null);
            assert_eq!(r, null);
        }
        _ => {
            assert_eq!("expected pair", "");
        }
    }
}

#[test]
fn can_echo_quoted_atom() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(1 . 3)".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 3);
        }
        _ => {
            assert_eq!("expected atom", "");
        }
    }
}

#[test]
fn can_do_operations() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(16 (1 . 3) (1 . 5))".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 8);
        }
        _ => {
            assert_eq!("expected atom", "");
        }
    }
}

#[test]
fn can_do_operations_kw() {
    let mut allocator = Allocator::new();
    let res = run_from_source(&mut allocator, "(+ (q . 3) (q . 5))".to_string());
    match allocator.sexp(res) {
        SExp::Atom(b) => {
            let res_bytes = allocator.buf(&b).to_vec();
            assert_eq!(res_bytes.len(), 1);
            assert_eq!(res_bytes[0], 8);
        }
        _ => {
            assert_eq!("expected atom", "");
        }
    }
}

#[test]
fn basic_opc() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}
        .invoke(&mut allocator, &"()".to_string())
        .unwrap();
    assert_eq!(result.rest(), "80");
}

#[test]
fn opc_ten_million() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}
        .invoke(&mut allocator, &"10000000".to_string())
        .unwrap();
    assert_eq!(result.rest(), "8400989680");
}

#[test]
fn basic_opc_lil() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}
        .invoke(&mut allocator, &"(())".to_string())
        .unwrap();
    assert_eq!(result.rest(), "ff8080");
}

#[test]
fn basic_opc_quoted_1() {
    let mut allocator = Allocator::new();
    let result = OpcConversion {}
        .invoke(&mut allocator, &"(q . 1)".to_string())
        .unwrap();
    assert_eq!(result.rest(), "ff0101");
}

#[test]
fn very_simple_compile() {
    let mut allocator = Allocator::new();
    let result = compile_program(
        &mut allocator,
        ".".to_string(),
        "(mod () (+ 3 2))".to_string(),
    );
    assert_eq!(result, Ok("(q . 5)".to_string()));
}

#[test]
fn node_path_top_left() {
    assert_eq!(*NodePath::new(None).first().as_path().data(), vec!(2 as u8));
}

#[test]
fn node_path_top_right() {
    assert_eq!(*NodePath::new(None).rest().as_path().data(), vec!(3 as u8));
}

#[test]
fn node_path_2nd_of_list() {
    assert_eq!(
        *NodePath::new(None).first().rest().as_path().data(),
        vec!(5 as u8)
    );
}

#[test]
fn compile_prog_with_args() {
    let mut allocator = Allocator::new();
    let result = compile_program(
        &mut allocator,
        ".".to_string(),
        "(mod (A B) (+ A B))".to_string(),
    );
    assert_eq!(result, Ok("(+ 2 5)".to_string()));
}

#[test]
fn compile_function_macro() {
    let mut allocator = Allocator::new();
    let result = compile_program(
        &mut allocator,
        ".".to_string(),
        "(\"defmacro\" \"function\" (\"BODY\") (29041 (\"opt\" (\"com\" (q \"unquote\" \"BODY\") (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))))".to_string());
    assert_eq!(result, Ok("(\"function\" (c (q . \"opt\") (c (c (q . \"com\") (c (c (q . 1) 2) (q (29041 (\"unquote\" (\"macros\"))) (29041 (\"unquote\" (\"symbols\")))))) ())))".to_string()));
}

#[test]
fn basic_if_expansion() {
    let mut allocator = Allocator::new();
    let result = compile_program(
        &mut allocator,
        ".".to_string(),
        "(mod (A B) (if A (* 2 A) (+ 1 A)))".to_string(),
    );
    assert_eq!(
        result,
        Ok("(a (i 2 (q 18 (q . 2) 2) (q 16 (q . 1) 2)) 1)".to_string())
    );
}

#[test]
fn basic_assert_macro() {
    let mut allocator = Allocator::new();
    let program = "(mod () (defmacro assert items (if (r items) (list if (f items) (c assert (r items)) (q . (x))) (f items))) (assert 1))";
    let result = compile_program(&mut allocator, ".".to_string(), program.to_string());
    assert_eq!(result, Ok("(q . 1)".to_string()));
}

#[test]
fn macro_mod_1() {
    let mut allocator = Allocator::new();
    let program = indoc! {"
    (opt (com (quote (mod (ARGS) \
    (defmacro if1 (A B C) \
     (qq (a \
          (i (unquote A) \
           (function (unquote B)) \
           (function (unquote C))) \
          @)) \
    ) \
    (defmacro and1 ARGS \
     (if1 ARGS \
      (qq (if1 (unquote (f ARGS)) \
           (unquote (c and1 (r ARGS))) \
           () \
      )) \
      1) \
    ) \
    (and1 (f @) 30) \
    ))))"};
    let result = compile_program(&mut allocator, ".".to_string(), program.to_string());
    assert_eq!(result, Ok("(q 2 (i 2 (q 1 . 1) ()) 1)".to_string()));
}

#[test]
fn map_6() {
    let mut allocator = Allocator::new();
    let program = "(a (mod (ARGS) (defun double (VAL) (* 2 VAL)) (defun square (VAL) (* VAL VAL)) (defun map (func items) (if items (c (func (f items)) (map func (r items))) ())) (map square (map double ARGS))) (quote ((4 3 2 1))))".to_string();
    let result = compile_program(&mut allocator, ".".to_string(), program.to_string());
    assert_eq!(result, Ok("(64 36 16 4)".to_string()));
}

#[test]
fn pool_member_innerpuz() {
    let mut testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    testpath.push("resources/tests/stage_2");
    let program = indoc! {"
        (mod (POOL_PUZZLE_HASH
              P2_SINGLETON_PUZZLE_HASH
              OWNER_PUBKEY
              POOL_REWARD_PREFIX
              WAITINGROOM_PUZHASH
              Truths
              p1
              pool_reward_height
              )
        
        
          ; POOL_PUZZLE_HASH is commitment to the pool's puzzle hash
          ; P2_SINGLETON_PUZZLE_HASH is the puzzle hash for your pay to singleton puzzle
          ; OWNER_PUBKEY is the farmer pubkey which authorises a travel
          ; POOL_REWARD_PREFIX is network-specific data (mainnet vs testnet) that helps determine if a coin is a pool reward
          ; WAITINGROOM_PUZHASH is the puzzle_hash you'll go to when you iniate the leaving process
        
          ; Absorbing money if pool_reward_height is an atom
          ; Escaping if pool_reward_height is ()
        
          ; p1 is pool_reward_amount if absorbing money
          ; p1 is extra_data key_value_list if escaping
        
          ; pool_reward_amount is the value of the coin reward - this is passed in so that this puzzle will still work after halvenings
          ; pool_reward_height is the block height that the reward was generated at. This is used to calculate the coin ID.
          ; key_value_list is signed extra data that the wallet may want to publicly announce for syncing purposes
        
          (include condition_codes.clvm)
          (include singleton_truths.clib)
        
          ; takes a lisp tree and returns the hash of it
          (defun sha256tree (TREE)
              (if (l TREE)
                  (sha256 2 (sha256tree (f TREE)) (sha256tree (r TREE)))
                  (sha256 1 TREE)
              )
          )
        
          (defun-inline calculate_pool_reward (pool_reward_height P2_SINGLETON_PUZZLE_HASH POOL_REWARD_PREFIX pool_reward_amount)
            (sha256 (logior POOL_REWARD_PREFIX (logand (- (lsh (q . 1) (q . 128)) (q . 1)) pool_reward_height)) P2_SINGLETON_PUZZLE_HASH pool_reward_amount)
          )
        
          (defun absorb_pool_reward (POOL_PUZZLE_HASH my_inner_puzzle_hash my_amount pool_reward_amount pool_reward_id)
            (list
                (list CREATE_COIN my_inner_puzzle_hash my_amount)
                (list CREATE_COIN POOL_PUZZLE_HASH pool_reward_amount)
                (list CREATE_PUZZLE_ANNOUNCEMENT pool_reward_id)
                (list ASSERT_COIN_ANNOUNCEMENT (sha256 pool_reward_id '$'))
            )
          )
        
          (defun-inline travel_to_waitingroom (OWNER_PUBKEY WAITINGROOM_PUZHASH my_amount extra_data)
            (list (list AGG_SIG_ME OWNER_PUBKEY (sha256tree extra_data))
                  (list CREATE_COIN WAITINGROOM_PUZHASH my_amount)
            )
          )
        
          ; main
        
          (if pool_reward_height
            (absorb_pool_reward POOL_PUZZLE_HASH
                                (my_inner_puzzle_hash_truth Truths)
                                (my_amount_truth Truths)
                                p1
                                (calculate_pool_reward pool_reward_height P2_SINGLETON_PUZZLE_HASH POOL_REWARD_PREFIX p1)
            )
            (travel_to_waitingroom OWNER_PUBKEY WAITINGROOM_PUZHASH (my_amount_truth Truths) p1)
            )
          )
        )
    "};
    let desired = "(a (q 2 (i 767 (q 2 22 (c 2 (c 5 (c 1215 (c 1727 (c 383 (c (sha256 (logior 47 (logand (q . 0x00ffffffffffffffffffffffffffffffff) 767)) 11 383) ()))))))) (q 4 (c 8 (c 23 (c (a 30 (c 2 (c 383 ()))) ()))) (c (c 28 (c 95 (c 1727 ()))) ()))) 1) (c (q (50 61 . 51) 62 (c (c 28 (c 11 (c 23 ()))) (c (c 28 (c 5 (c 47 ()))) (c (c 10 (c 95 ())) (c (c 20 (c (sha256 95 (q . 36)) ())) ())))) 2 (i (l 5) (q 11 (q . 2) (a 30 (c 2 (c 9 ()))) (a 30 (c 2 (c 13 ())))) (q 11 (q . 1) 5)) 1) 1))".to_string();
    let mut s = Stream::new(None);
    launch_tool(
        &mut s,
        &vec![
            "run".to_string(),
            "-i".to_string(),
            testpath.into_os_string().into_string().unwrap(),
            program.to_string(),
        ],
        &"run".to_string(),
        2,
    );
    let result = s.get_value().decode().trim().to_string();
    assert_eq!(result, desired);
}
