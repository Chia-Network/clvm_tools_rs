use crate::tests::classic::run::{do_basic_brun, do_basic_run};

const EMBED_BIN_FILE: &str = "a-binary-file-called-hello.dat";
const EMBED_HEX_FILE: &str = "hex-embed-01.hex";
const EMBED_SEXP_FILE: &str = "embed.sexp";
const EMBED_NOT_EXIST: &str = "not-exist.txt";

const BIN_HASH: &str = "0xcceeb7a985ecc3dabcb4c8f666cd637f16f008e3c963db6aa6f83a7b288c54ef"; // sha256(b'\x01hello')
const HEX_HASH: &str = "0xd59489bcba845c9a04cde90e94ae0cb1efaa81befcd3a9b6603a5fa6f8327bef"; // (mod () (include sha256tree.clib) (sha256tree (q 65 66 67)))
const SEXP_HASH: &str = "0x392f4227bfc31a238b4738b0b0c7f10afb1a55c674286bc99cf89b4b22610aba"; // '(mod () (include sha256tree.clib) (sha256tree (q 23 24 25)))'

const BIN_TYPE: &str = "bin";
const HEX_TYPE: &str = "hex";
const SEXP_TYPE: &str = "sexp";

#[test]
fn test_embed_file_as_variable_name() {
    let program = indoc! {"
(mod (X) (defun embed-file (embed-file) (+ 1 embed-file)) (embed-file X))
    "}
    .to_string();
    let compiled = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        program,
    ]);

    let result = do_basic_brun(&vec!["brun".to_string(), compiled, "(103)".to_string()])
        .trim()
        .to_string();

    assert_eq!(result, "104");
}

// Embed test matrix (suggested)
// Exists, NotExists vs Bin, Hex, Sexp vs Modern, Classic
// - Exists
//   - Bin Modern
//   - Bin Classic
//   - Hex Modern
//   - Hex Classic
//   - Sexp Modern
//   - Sexp Classic
// - NotExists
//   - Bin Modern
//   - Bin Classic
//   - Hex Modern
//   - Hex Classic
//   - Sexp Modern
//   - Sexp Classic
#[test]
fn test_embed_exhaustive() {
    let include_list = &[
        (BIN_TYPE, EMBED_BIN_FILE, BIN_HASH),
        (HEX_TYPE, EMBED_HEX_FILE, HEX_HASH),
        (SEXP_TYPE, EMBED_SEXP_FILE, SEXP_HASH),
    ];

    for order in 0..=1 {
        for exists in 0..=1 {
            for (include_kind, include_file, want_hash) in include_list.iter() {
                for modern in 0..=2 {
                    let modern_sigil = if modern == 1 {
                        "(include *standard-cl-21*)"
                    } else if modern == 2 {
                        "(include *strict-cl-21*)"
                    } else {
                        ""
                    };
                    let filename = if exists > 0 {
                        include_file
                    } else {
                        EMBED_NOT_EXIST
                    };

                    let embed_pt: Vec<String> = (0..=1)
                        .map(|i| {
                            if i == order {
                                format!("(embed-file embedded-data {include_kind} {filename})")
                            } else {
                                "".to_string()
                            }
                        })
                        .collect();

                    let program = format!("(mod () {modern_sigil} {} (include sha256tree.clib) {} (sha256tree embedded-data))", embed_pt[0], embed_pt[1]);
                    eprintln!("program {program}");

                    let compiled = do_basic_run(&vec![
                        "run".to_string(),
                        "-i".to_string(),
                        "resources/tests".to_string(),
                        program,
                    ]);

                    if exists > 0 {
                        let output =
                            do_basic_brun(&vec!["brun".to_string(), compiled, "()".to_string()])
                                .trim()
                                .to_string();
                        assert_eq!(want_hash, &output);
                    } else {
                        if modern > 0 {
                            assert!(compiled.contains("could not find not-exist.txt"));
                        } else {
                            assert!(compiled.starts_with("FAIL:"));
                        }
                    }
                }
            }
        }
    }
}
