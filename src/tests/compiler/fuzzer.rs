use crate::compiler::comptypes::CompileForm;
use crate::compiler::fuzzer::CollectProgramStructure;
use crate::fuzzing::fuzzrng::FuzzPseudoRng;
use rand::prelude::*;

fn produce_fuzz_program(b: &[u8]) -> CompileForm {
    let mut rng = FuzzPseudoRng::new(b);
    let mut cps: CollectProgramStructure = rng.gen();
    cps.to_program()
}

#[test]
fn test_simple_fuzzer_output_1() {
    let input: &[u8] = &[
        0x00, 0x00, 0x00, 0xaf, 0xe8, 0x20, 0xb7, 0x82, 0x07, 0x29, 0xae, 0x0f, 0x22, 0xb3, 0xf5,
        0x5b,
    ];
    let cf = produce_fuzz_program(input);
    assert_eq!(
        cf.to_sexp().to_string(),
        "(E (defmacro helper_0 C (18 (q) (q))) (q))"
    );
}

#[test]
fn test_simple_fuzzer_output_2() {
    let input: &[u8] = &[
        0x00, 0x00, 0x00, 0xaf, 0xe8, 0x20, 0xb7, 0x82, 0x07, 0x3f, 0x79, 0xaa, 0x72, 0xb3, 0xf5,
        0x5b,
    ];
    let cf = produce_fuzz_program(input);
    assert_eq!(
        cf.to_sexp().to_string(),
        "(E (defmacro helper_0 C (let ((A (18 (q) (q)))) (18 (q) (q)))) (q))"
    );
}

#[test]
fn test_simple_fuzzer_output_3() {
    let input: &[u8] = &[
        0x00, 0x00, 0x00, 0x8c, 0x66, 0x36, 0xfd, 0xb3, 0x5a, 0x80, 0x9d, 0x45, 0x9c, 0x0e, 0x91,
        0x79,
    ];
    let cf = produce_fuzz_program(input);
    assert_eq!(cf.to_sexp().to_string(), "(A (18 (let ((B A) (D A)) A) A))");
}
