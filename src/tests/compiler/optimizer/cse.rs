use regex::Regex;
use std::rc::Rc;

use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::optimize::cse::cse_optimize_bodyform;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;

#[test]
fn smoke_test_cse_optimization() {
    let filename = "*test*";
    let source = indoc! {"
    (a (i Q
      (com (G (- Q 1) (* (+ 1 Q) R)))
      (com (* (+ 1 Q) R))
      ) 1)"}
    .to_string();
    let srcloc = Srcloc::start(filename);
    let opts: Rc<dyn CompilerOpts> = Rc::new(DefaultCompilerOpts::new(filename));
    let parsed = parse_sexp(srcloc.clone(), source.bytes()).expect("should parse");
    let bodyform = compile_bodyform(opts.clone(), parsed[0].clone()).expect("should compile");
    let cse_transformed =
        cse_optimize_bodyform(&srcloc, b"test", &bodyform).expect("should cse optimize");
    let re_def = r"(let ((cse_[$]_[0-9]+ ([*] ([+] 1 Q) R))) (a (i Q (com (G (- Q 1) cse_[$]_[0-9]+)) (com cse_[$]_[0-9]+)) 1))".replace("(", r"\(").replace(")",r"\)");
    eprintln!("re_def {re_def}");
    let re = Regex::new(&re_def).expect("should become a regex");
    assert!(re.is_match(&cse_transformed.to_sexp().to_string()));
}
