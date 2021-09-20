use std::collections::HashMap;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};
use crate::classic::clvm::serialize::{
    SimpleCreateCLVMObject,
    sexp_to_stream
};
use crate::classic::clvm::sexp::{
    enlist,
    rest,
    proper_list
};

use crate::classic::clvm_tools::sha256tree::sha256tree;

pub enum TracePostAction {
    PostActionReplaceMostRecentLogEntry
}

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

// export function build_symbol_dump(constants_lookup: Record<str, SExp>, run_program: TRunProgram, path: str){
//   const compiled_lookup: Record<str, str> = {};
//   const entries = Object.entries(constants_lookup);
//   for(const [k, v] of entries){
//     const [, v1] = run_program(v, SExp.null());
//     compiled_lookup[sha256tree(v1).hex()] = h(k).decode();
//   }
//   const output = JSON.stringify(compiled_lookup);
//   fs_write(path, output);
// }

fn text_trace(
    allocator: &mut Allocator,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    form: NodePtr,
    symbol: Option<String>,
    env_: NodePtr,
    result: &String
) {
    let mut symbol_val = "".to_string();
    let mut env = env_;
    match symbol {
        Some(sym) => {
            env = rest(allocator, env).unwrap();
            let symbol_atom =
                allocator.new_atom(&sym.as_bytes().to_vec()).unwrap();
            let symbol_list = allocator.new_pair(symbol_atom, env).unwrap();
            symbol_val = disassemble_f(allocator, symbol_list);
        },
        _ => {
            symbol_val = format!("{} [{}]", disassemble_f(allocator, form), disassemble_f(allocator, env));
        }
    }

    print!("{} => {}\n\n", symbol_val, result);
}

fn table_trace(
    allocator: &mut Allocator,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    form: NodePtr, symbol: Option<String>, env: NodePtr, result: &String
) {
    let (sexp, args) =
        match allocator.sexp(form) {
            SExp::Pair(sexp, args) => (sexp, args),
            SExp::Atom(_) => (form, allocator.null())
        };

    print!("exp: {}\n", disassemble_f(allocator, sexp));
    print!("arg: {}\n", disassemble_f(allocator, args));
    print!("env: {}\n", disassemble_f(allocator, env));
    print!("val: {}\n", result);
    let mut sexp_stream = Stream::new(None);
    sexp_to_stream(
        allocator,
        sexp,
        &mut sexp_stream
    );
    let mut args_stream = Stream::new(None);
    sexp_to_stream(
        allocator,
        args,
        &mut args_stream
    );
    let mut benv_stream = Stream::new(None);
    sexp_to_stream(
        allocator,
        env,
        &mut benv_stream
    );
    print!("bexp: {}\n", sexp_stream.get_value().hex());
    print!("barg: {}\n", args_stream.get_value().hex());
    print!("benv: {}\n", benv_stream.get_value().hex());
    print!("--");
}

fn display_trace(
    allocator: &mut Allocator,
    trace: &Vec<NodePtr>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String,
    symbol_table: Option<HashMap<String, String>>,
    display_fun: &dyn Fn(
        &mut Allocator,
        &dyn Fn(&mut Allocator, NodePtr) -> String,
        NodePtr,
        Option<String>,
        NodePtr,
        &String
    )
) {
    for item in trace {
        let item_vec = proper_list(allocator, *item, true).unwrap();
        let form = item_vec[0];
        let env = item_vec[1];
        let rv =
            if item_vec.len() > 2 {
                disassemble_f(allocator, item_vec[2])
            } else {
                "(didn't finish)".to_string()
            };

        let h = sha256tree(allocator, form).hex();
        let symbol =
            symbol_table.clone().and_then(
                |st| st.get(&h).map(|x| x.to_string())
            );
        display_fun(allocator, disassemble_f, form, symbol, env, &rv);
    }
}

pub fn trace_to_text(
    allocator: &mut Allocator,
    trace: &Vec<NodePtr>,
    symbol_table: Option<HashMap<String, String>>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String
) {
    display_trace(allocator, trace, disassemble_f, symbol_table, &text_trace);
}

pub fn trace_to_table(
    allocator: &mut Allocator,
    trace: &Vec<NodePtr>,
    symbol_table: Option<HashMap<String, String>>,
    disassemble_f: &dyn Fn(&mut Allocator, NodePtr) -> String
) {
    display_trace(allocator, trace, disassemble_f, symbol_table, &table_trace);
}

pub fn trace_pre_eval(
    allocator: &mut Allocator,
    append_log: &dyn Fn(&mut Allocator, NodePtr),
    symbol_table: Option<HashMap<String, String>>,
    sexp: NodePtr,
    args: NodePtr
) -> Result<Option<TracePostAction>, EvalErr> {
    let h = sha256tree(allocator, sexp);
    let recognized = symbol_table.and_then(|symbol_table| symbol_table.get(&h.hex()).map(|x| x.to_string()));

    if recognized.is_none() {
        Ok(None)
    } else {
        m! {
            log_entry <- enlist(allocator, &vec!(sexp, args));
            let _ = append_log(allocator, log_entry);
            Ok(Some(TracePostAction::PostActionReplaceMostRecentLogEntry))
        }
    }
}
