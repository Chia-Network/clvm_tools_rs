use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};
use crate::classic::clvm::serialize::sexp_to_stream;
use crate::classic::clvm::sexp::{enlist, mapM, proper_list, rest};

use crate::classic::clvm_tools::sha256tree::sha256tree;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::frontend::frontend;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::srcloc::Srcloc;
use crate::compiler::usecheck::check_parameters_used_compileform;

// export const PRELUDE = `<html>
// <head>
//   <link rel="stylesheet"
//       href="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/css/bootstrap.min.css"
//       integrity="sha384-ggOyR0iXCbMQv3Xipma34MD+dH/1fQ784/j6cY/iJTQUOhcWr7x9JvoRxT2MZw1T"
//       crossorigin="anonymous">
//   <script
//       src="https://code.jquery.com/jquery-3.3.1.slim.min.js"
//       integrity="sha384-q8i/X+965DzO0rT7abK41JStQIAqVgRVzpbzo5smXKp4YfRvH+8abtTE1Pi6jizo"
//       crossorigin="anonymous"></script>
//   <script
//       src="https://cdnjs.cloudflare.com/ajax/libs/popper.js/1.14.7/umd/popper.min.js"
//       integrity="sha384-UO2eT0CpHqdSJQ6hJty5KVphtPhzWj9WO1clHTMGa3JDZwrnQq4sF86dIHNDz0W1"
//       crossorigin="anonymous"></script>
//   <script
//       src="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/js/bootstrap.min.js"
//       integrity="sha384-JjSmVgyd0p3pXB1rRibZUAYoIIy6OrQ6VrjIEaFf/nJGzIxFDsf4x0xIM+B07jRM"
//       crossorigin="anonymous"></script>
// </head>
// <body>
// <div class="container">
// `;

// export const TRAILER = "</div></body></html>";

// export function dump_sexp(s: SExp, disassemble_f: typeof disassemble = disassemble){
//   return `<span id="${s.__repr__()}">${disassemble_f(s)}</span>`;
// }

// // The function below is broken as of 2021/06/22.
// /*
// export function dump_invocation(
//   form: SExp,
//   rewrit_form: SExp,
//   env: SExp[],
//   result: SExp,
//   disassemble_f: typeof disassemble = disassemble,
// ){
//   print(`<hr><div class="invocation" id="${form}">`);
//   print(`<span class="form"><a name="id_${form}">${dump_sexp(form, disassemble)}</a></span>`);
//   print("<ul>")
//   if (form != rewrit_form){
//     print(
//       `<li>Rewritten as:<span class="form">`,
//       `<a name="id_${rewrit_form}">${dump_sexp(rewrit_form, disassemble)}</a></span></li>`,
//     );
//   }
//   env.forEach((e, i) => {
//     print(`<li>x${i}: <a href="#id_${e}">${dump_sexp(e, disassemble_f)}</a>`);
//   });
//   print("</ul>");
//   print(`<span class="form">${dump_sexp(result, disassemble_f)}</span>`);
//   if(form.listp() && form.list_len() > 1){
//     print(`<ul>`);
//     // @todo Implement here if original python code is fixed.
//   }
//   print(`</ul>`)
//   print("</div>")
// }
// export function trace_to_html(){
//     // @todo Implement here if original python code is fixed.
// }
// */
pub fn build_symbol_dump(
    allocator: &mut Allocator,
    constants_lookup: HashMap<Vec<u8>, NodePtr>,
    run_program: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    let compiled_unrolled: Vec<(Vec<u8>, NodePtr)> = constants_lookup.into_iter().collect();

    m! {
        map_result <- mapM(
            allocator,
            &mut compiled_unrolled.iter(),
            &|allocator, kv| m! {
                run_result <- run_program.run_program(
                    allocator,
                    kv.1,
                    allocator.null(),
                    None
                );

                let sha256 = sha256tree(allocator, run_result.1).hex();
                sha_atom <- allocator.new_atom(&sha256.as_bytes().to_vec());
                name_atom <- allocator.new_atom(&kv.0.clone());
                allocator.new_pair(sha_atom, name_atom)
            }
        );

        enlist(allocator, &map_result)
    }
}

fn text_trace(
    allocator: &mut Allocator,
    output: &mut Stream,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    form: NodePtr,
    symbol: Option<String>,
    env_: NodePtr,
    result: &String,
) {
    let symbol_val;
    let mut env = env_;
    match symbol {
        Some(sym) => {
            env = rest(allocator, env).unwrap_or_else(|_| allocator.null());
            let symbol_atom = allocator.new_atom(&sym.as_bytes().to_vec()).unwrap();
            let symbol_list = allocator.new_pair(symbol_atom, env).unwrap();
            symbol_val = disassemble_f(allocator, symbol_list);
        }
        _ => {
            symbol_val = format!(
                "{} [{}]",
                disassemble_f(allocator, form),
                disassemble_f(allocator, env)
            );
        }
    }

    output.write_string(format!("{} => {}\n\n", symbol_val, result));
}

fn table_trace(
    allocator: &mut Allocator,
    stdout: &mut Stream,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    form: NodePtr,
    _symbol: Option<String>,
    env: NodePtr,
    result: &String,
) {
    let (sexp, args) = match allocator.sexp(form) {
        SExp::Pair(sexp, args) => (sexp, args),
        SExp::Atom(_) => (form, allocator.null()),
    };

    stdout.write_string(format!("exp: {}\n", disassemble_f(allocator, sexp)));
    stdout.write_string(format!("arg: {}\n", disassemble_f(allocator, args)));
    stdout.write_string(format!("env: {}\n", disassemble_f(allocator, env)));
    stdout.write_string(format!("val: {}\n", result));
    let mut sexp_stream = Stream::new(None);
    sexp_to_stream(allocator, sexp, &mut sexp_stream);
    let mut args_stream = Stream::new(None);
    sexp_to_stream(allocator, args, &mut args_stream);
    let mut benv_stream = Stream::new(None);
    sexp_to_stream(allocator, env, &mut benv_stream);
    stdout.write_string(format!("bexp: {}\n", sexp_stream.get_value().hex()));
    stdout.write_string(format!("barg: {}\n", args_stream.get_value().hex()));
    stdout.write_string(format!("benv: {}\n", benv_stream.get_value().hex()));
    stdout.write_string(format!("--\n"));
}

fn display_trace(
    allocator: &mut Allocator,
    stdout: &mut Stream,
    trace: &Vec<NodePtr>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    symbol_table: Option<HashMap<String, String>>,
    display_fun: &dyn Fn(
        &mut Allocator,
        &mut Stream,
        &dyn Fn(&mut Allocator, NodePtr) -> String,
        NodePtr,
        Option<String>,
        NodePtr,
        &String,
    ),
) {
    for item in trace {
        let item_vec = proper_list(allocator, *item, true).unwrap();
        let form = item_vec[0];
        let env = item_vec[1];
        let rv = if item_vec.len() > 2 {
            disassemble_f(allocator, item_vec[2])
        } else {
            "(didn't finish)".to_string()
        };

        let h = sha256tree(allocator, form).hex();
        let symbol = symbol_table
            .as_ref()
            .and_then(|st| st.get(&h).map(|x| x.to_string()));
        display_fun(allocator, stdout, disassemble_f, form, symbol, env, &rv);
    }
}

pub fn trace_to_text(
    allocator: &mut Allocator,
    stdout: &mut Stream,
    trace: &Vec<NodePtr>,
    symbol_table: Option<HashMap<String, String>>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
) {
    display_trace(
        allocator,
        stdout,
        trace,
        disassemble_f,
        symbol_table,
        &text_trace,
    );
}

pub fn trace_to_table(
    allocator: &mut Allocator,
    stdout: &mut Stream,
    trace: &Vec<NodePtr>,
    symbol_table: Option<HashMap<String, String>>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
) {
    display_trace(
        allocator,
        stdout,
        trace,
        disassemble_f,
        symbol_table,
        &table_trace,
    );
}

pub fn trace_pre_eval(
    allocator: &mut Allocator,
    append_log: &dyn Fn(&mut Allocator, NodePtr),
    symbol_table: Option<HashMap<String, String>>,
    sexp: NodePtr,
    args: NodePtr,
) -> Result<Option<NodePtr>, EvalErr> {
    let h = sha256tree(allocator, sexp);
    let recognized = symbol_table
        .as_ref()
        .and_then(|symbol_table| symbol_table.get(&h.hex()).map(|x| x.to_string()));

    if recognized.is_none() && !symbol_table.is_none() {
        Ok(None)
    } else {
        m! {
            log_entry <- enlist(allocator, &vec!(sexp, args));
            let _ = append_log(allocator, log_entry);
            Ok(Some(log_entry))
        }
    }
}

pub fn check_unused(
    opts: Rc<dyn CompilerOpts>,
    input_program: &String,
) -> Result<(bool, String), CompileErr> {
    let mut output: Stream = Stream::new(None);
    let pre_forms = parse_sexp(Srcloc::start(&opts.filename()), input_program)
        .map_err(|e| CompileErr(e.0, e.1))?;
    let g = frontend(opts.clone(), pre_forms)?;
    let unused = check_parameters_used_compileform(opts, Rc::new(g))?;

    if !unused.is_empty() {
        output.write_string(format!("unused arguments detected at the mod level (lower case arguments are considered uncurried by convention)\n"));
        for s in unused.iter() {
            output.write_string(format!(
                " - {}\n",
                Bytes::new(Some(BytesFromType::Raw(s.clone()))).decode()
            ));
        }
        Ok((false, output.get_value().decode()))
    } else {
        Ok((true, output.get_value().decode()))
    }
}
