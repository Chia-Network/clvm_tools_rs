use num_bigint::ToBigInt;

use std::borrow::Borrow;
use std::env;
use std::fs;
use std::rc::Rc;

use clvm_tools_rs::classic::clvm::__type_compatibility__::bi_zero;
use clvm_tools_rs::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;

use clvm_tools_rs::compiler::comptypes::{BodyForm, CompilerOpts, CompileForm, DefunData, HelperForm, LetFormKind};
use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
use clvm_tools_rs::compiler::evaluate::make_operator2;
use clvm_tools_rs::compiler::frontend::frontend;
use clvm_tools_rs::compiler::sexp::{decode_string, parse_sexp, SExp};
use clvm_tools_rs::compiler::srcloc::Srcloc;
use clvm_tools_rs::compiler::smt::model::Model;

use clvm_tools_rs::util::Number;

fn to_es_sexp(sexp: &SExp, quoted_atom: bool) -> String {
    match sexp {
        SExp::Nil(_) => "null".to_string(),
        SExp::Atom(_,a) => {
            if quoted_atom {
                format!("\"{}\"", decode_string(&a))
            } else {
                format!("{}", decode_string(&a))
            }
        }
        SExp::Integer(_,i) => format!("{}n", i),
        SExp::QuotedString(_,_,s) => format!("\"{}\"", decode_string(&s)),
        SExp::Cons(_,a,b) => format!("[{},{}]", to_es_sexp(a, quoted_atom), to_es_sexp(b, quoted_atom))
    }
}

fn is_if(args: &[Rc<BodyForm>]) -> bool {
    if args.len() != 4 {
        return false;
    }

    if let BodyForm::Value(SExp::Atom(_,name)) = args[0].borrow() {
        return name == b"if";
    }

    false
}

fn map_atom_name(name: &[u8]) -> Vec<u8> {
    if name == b"-" {
        return b"chia_minus".to_vec();
    } else if name == b"+" {
        return b"chia_plus".to_vec();
    } else if name == b"*" {
        return b"chia_times".to_vec();
    } else if name == b"c" {
        return b"chia_cons".to_vec();
    } else if name == b"f" {
        return b"chia_first".to_vec();
    } else if name == b"r" {
        return b"chia_rest".to_vec();
    } else if name == b"a" {
        return b"chia_apply".to_vec();
    } else if name == b"/" {
        return b"chia_div".to_vec();
    } else if name == b"=" {
        return b"chia_eq".to_vec();
    }

    name.to_vec()
}

fn to_es_body(bf: &BodyForm) -> String {
    match bf {
        BodyForm::Quoted(sexp) => {
            format!("{{f:1,r:{}}}", to_es_sexp(&sexp, true))
        }
        BodyForm::Value(sexp) => {
            to_es_sexp(&sexp, false)
        }
        BodyForm::Call(l, args) => {
            if args.is_empty() {
                return "null".to_string();
            } else if is_if(&args) {
                return format!(
                    "(() => {{ if (clvm_truthy({})) {{ return {}; }} else {{ return {}; }} }})()",
                    to_es_body(&args[1]),
                    to_es_body(&args[2]),
                    to_es_body(&args[3])
                );
            } else {
                let mut argdata = "null".to_string();
                let call_name =
                    if let BodyForm::Value(SExp::Atom(_,n)) = args[0].borrow() {
                        decode_string(&map_atom_name(&n))
                    } else {
                        to_es_body(&args[0])
                    };
                for a in args.iter().skip(1).rev() {
                    argdata = format!("{{f:{},r:{}}}", to_es_body(&a), argdata);
                }
                format!("{}({})", call_name, argdata)
            }
        }
        BodyForm::Let(_, letdata) => {
            let mut arglist = "".to_string();
            let mut argdata = "".to_string();
            let mut comma = "".to_string();
            for b in letdata.bindings.iter() {
                arglist = format!("{}{}{}", arglist, comma, decode_string(&b.name));
                argdata = format!("{}{}{}", argdata, comma, to_es_body(&b.body));
                comma = ",".to_string();
            }
            format!("(({}) => {{ return {}; }})({})", arglist, to_es_body(&letdata.body), argdata)
        }
        BodyForm::Mod(_, program) => {
            to_es_compileform(&program)
        }
    }
}

fn compute_decoded_args(mask: Number, path: Number, args: Rc<SExp>) -> String {
    if let SExp::Cons(_,f,r) = args.borrow() {
        let next_mask = mask.clone() * 2_u32.to_bigint().unwrap();
        format!("{} {}", compute_decoded_args(next_mask.clone(), path.clone(), f.clone()), compute_decoded_args(next_mask, path + mask, r.clone()))
    } else if let SExp::Atom(_,n) = args.borrow() {
        format!("let {} = choose_path({}n, arg);", decode_string(&n), mask + path)
    } else {
        "".to_string()
    }
}

fn to_es_helper(cf: &CompileForm, hf: &HelperForm) -> String {
    match hf {
        HelperForm::Defconstant(cdata) => {
            format!("let {} = {};", decode_string(&cdata.name), to_es_body(&cdata.body))
        }
        HelperForm::Defmacro(mac) => { format!("/* macro {} */", decode_string(&mac.name)) }
        HelperForm::Defun(_,data) => {
            let decoded_args = compute_decoded_args(2_u32.to_bigint().unwrap(), bi_zero(), data.args.clone());
            format!("function {}(arg) {{ {}; return {}; }}", decode_string(&data.name), decoded_args, to_es_body(&data.body))
        }
    }
}

fn to_es_compileform(compiled: &CompileForm) -> String {
    let mut helpers = "".to_string();
    for h in compiled.helpers.iter() {
        if h.name() == b"/" {
            continue;
        }
        helpers = format!("{}{}", helpers, to_es_helper(&compiled, &h));
    }

    let main_function = HelperForm::Defun(false, DefunData {
        loc: compiled.loc(),
        name: b"__main".to_vec(),
        kw: None,
        nl: compiled.loc(),
        args: compiled.args.clone(),
        body: compiled.exp.clone()
    });

    format!("(args) => {{ {}{}; return __main(args); }}", helpers, to_es_helper(&compiled, &main_function))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let loc = Srcloc::start("*command*");
    let bare_paths = Vec::new();

    for a in args.iter().skip(1) {
        let runner =
            run_program_for_search_paths(
                &a, &bare_paths, true
            );
        let opts = DefaultCompilerOpts::new(&a).set_frontend_check_live(false);
        let read_file = fs::read_to_string(&a).
            expect(&format!("file should exist: {}", a));
        let parsed = parse_sexp(Srcloc::start(&a), read_file.bytes()).expect("should parse");
        let compiled = frontend(opts.clone(), &parsed).expect("should compile");

        println!("{}", to_es_compileform(&compiled));
    }
}
