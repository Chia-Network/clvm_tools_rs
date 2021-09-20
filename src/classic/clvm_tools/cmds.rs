use core::cell::RefCell;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::io;
use std::io::Write;
use std::rc::Rc;
use std::sync::mpsc::{
    channel,
    Sender,
    Receiver
};
use std::thread;
use std::time::SystemTime;
use std::fs;

use core::cmp::max;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::reduction::EvalErr;
use clvm_rs::run_program::PreEval;

use crate::classic::clvm::KEYWORD_FROM_ATOM;
use crate::classic::clvm::__type_compatibility__::{
    BytesFromType,
    Bytes,
    Stream,
    Tuple,
    t
};
use crate::classic::clvm_tools::debug::{
    TracePostAction,
    trace_to_text,
    trace_to_table
};
use crate::classic::clvm::serialize::{
    SimpleCreateCLVMObject,
    sexp_from_stream,
    sexp_to_stream
};
use crate::classic::clvm::sexp::{
    enlist,
    proper_list,
    sexp_as_bin
};
use crate::classic::clvm_tools::binutils::{
    assemble_from_ir,
    disassemble,
    disassemble_with_kw
};
use crate::classic::clvm_tools::debug::trace_pre_eval;
use crate::classic::clvm_tools::sha256tree::sha256tree;
use crate::classic::clvm_tools::stages;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    RunProgramOption,
    TRunProgram
};
use crate::classic::clvm_tools::stages::stage_2::operators::run_program_for_search_paths;
use crate::classic::clvm_tools::ir::reader::read_ir;

use crate::classic::platform::PathJoin;

use crate::classic::platform::argparse::{
    Argument,
    ArgumentParser,
    ArgumentValue,
    ArgumentValueConv,
    IntConversion,
    NArgsSpec,
    TArgOptionAction,
    TArgumentParserProps
};
use crate::util::collapse;

pub struct PathOrCodeConv { }

impl ArgumentValueConv for PathOrCodeConv {
    fn convert(&self, arg: &String) -> Result<ArgumentValue,String> {
        match fs::read_to_string(arg) {
            Ok(s) => { return Ok(ArgumentValue::ArgString(s)); },
            Err(_) => { return Ok(ArgumentValue::ArgString(arg.to_string())); }
        }
    }
}

// export function stream_to_bin(write_f: (f: Stream) => void){
//   const f = new Stream();
//   write_f(f);
//   return f.getValue();
// }

pub trait TConversion {
    fn invoke<'a>(&self, allocator: &'a mut Allocator, text: &String) -> Result<Tuple<NodePtr, String>, String>;
}
pub fn call_tool<'a>(allocator: &'a mut Allocator, tool_name: String, desc: String, conversion: Box<dyn TConversion>, input_args: &Vec<String>) {
    let props = TArgumentParserProps {
        description: desc,
        prog: tool_name.to_string()
    };

    let mut parser = ArgumentParser::new(Some(props));
    parser.add_argument(
        vec!(
            "-H".to_string(),
            "--script-hash".to_string()
        ),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Show only sha256 tree hash of program".to_string())
    );
    parser.add_argument(
        vec!("path_or_code".to_string()),
        Argument::new().
            set_n_args(NArgsSpec::KleeneStar).
            set_type(Rc::new(PathOrCodeConv {})).
            set_help("path to clvm script, or literal script".to_string())
    );

    let mut rest_args = Vec::new();
    for a in input_args[1..].into_iter() {
        rest_args.push(a.to_string());
    }
    let args_res = parser.parse_args(&rest_args);
    let args : HashMap<String, ArgumentValue>;

    match args_res {
        Ok(a) => { args = a; },
        Err(e) => {
            print!("{:?}\n", e);
            return;
        }
    }

    let args_path_or_code_val =
        match args.get(&"path_or_code".to_string()) {
            None => ArgumentValue::ArgArray(vec!()),
            Some(v) => v.clone()
        };

    let args_path_or_code =
        match args_path_or_code_val {
            ArgumentValue::ArgArray(v) => v,
            _ => vec!()
        };

    for program in args_path_or_code {
        match program {
            ArgumentValue::ArgString(s) => {
                if s == "-" {
                    panic!("Read stdin is not supported at this time");
                }

                let conv_result = conversion.invoke(allocator, &s);
                match conv_result {
                    Ok(conv_result) => {
                        let sexp = conv_result.first().clone();
                        let text = conv_result.rest();
                        if args.contains_key(&"script_hash".to_string()) {
                            print!("{}\n", sha256tree(allocator, sexp).hex());
                        } else if text.len() > 0 {
                            print!("{}\n", text);
                        }
                    },
                    Err(e) => {
                        panic!("Conversion returned error: {:?}", e);
                    }
                }
            },
            _ => {
                panic!("inappropriate argument conversion");
            }
        }

    }
}

pub struct OpcConversion { }

impl TConversion for OpcConversion {
    fn invoke<'a>(&self, allocator: &'a mut Allocator, hex_text: &String) -> Result<Tuple<NodePtr, String>, String> {
        return read_ir(hex_text).and_then(|ir_sexp| {
            return assemble_from_ir(
                allocator,
                Rc::new(ir_sexp)
            ).map_err(|e| e.1);
        }).map(|sexp| {
            return t(sexp, sexp_as_bin(allocator, sexp).hex());
        });
    }
}

pub struct OpdConversion { }

impl TConversion for OpdConversion {
    fn invoke<'a>(&self, allocator: &'a mut Allocator, hex_text: &String) -> Result<Tuple<NodePtr, String>, String> {
        let mut stream =
            Stream::new(Some(Bytes::new(Some(BytesFromType::Hex(hex_text.to_string())))));

        return sexp_from_stream(
            allocator,
            &mut stream,
            Box::new(SimpleCreateCLVMObject {})
        ).map_err(|e| e.1).map(|sexp| {
            let disassembled = disassemble(allocator, sexp.1);
            return t(sexp.1, disassembled);
        });
    }
}

pub fn opc(args: &Vec<String>) {
    let mut allocator = Allocator::new();
    call_tool(&mut allocator, "opc".to_string(), "Compile a clvm script.".to_string(), Box::new(OpcConversion {}), args);
}

pub fn opd(args: &Vec<String>) {
    let mut allocator = Allocator::new();
    call_tool(&mut allocator, "opd".to_string(), "Disassemble a compiled clvm script from hex.".to_string(), Box::new(OpdConversion {}), args);
}

struct StageImport {
}

impl ArgumentValueConv for StageImport {
    fn convert(&self, arg: &String) -> Result<ArgumentValue,String> {
        if arg == "0" {
            return Ok(ArgumentValue::ArgInt(0));
        }
        else if arg == "1" {
            return Ok(ArgumentValue::ArgInt(1));
        }
        else if arg == "2" {
            return Ok(ArgumentValue::ArgInt(2));
        }
        return Err(format!("Unknown stage: {}", arg));
    }
}

pub fn run(args: &Vec<String>) {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"run".to_string(), 2);
    io::stdout().write_all(s.get_value().data());
}

pub fn brun(args: &Vec<String>) {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"brun".to_string(), 0);
    io::stdout().write_all(s.get_value().data());
}

struct RunLog {
    log_entries: RefCell<Vec<NodePtr>>
}

impl RunLog {
    fn push(&self, new_log: NodePtr) {
        self.log_entries.replace_with(|log| {
            log.push(new_log);
            return log.to_vec();
        });
    }

    fn finish(&self) -> Vec<NodePtr> {
        let mut empty_log = Vec::new();
        self.log_entries.replace_with(|log| {
            empty_log = log.to_vec();
            return Vec::new();
        });
        return empty_log;
    }
}

fn calculate_cost_offset(
    allocator: &mut Allocator,
    run_program: Rc<dyn TRunProgram>,
    run_script: NodePtr
) -> i64 {
  /*
    These commands are used by the test suite, and many of them expect certain costs.
    If boilerplate invocation code changes by a fixed cost, you can tweak this
    value so you don't have to change all the tests' expected costs.
    Eventually you should re-tare this to zero and alter the tests' costs though.
    This is a hack and need to go away, probably when we do dialects for real,
    and then the dialect can have a `run_program` API.
   */
    let almost_empty_list = enlist(allocator, &vec!(allocator.null())).unwrap();
    let cost = run_program.run_program(
        allocator,
        run_script,
        almost_empty_list,
        None
    ).map(|x| x.0).unwrap_or_else(|_| 0);

    return 53 - cost as i64;
}

pub fn launch_tool(stdout: &mut Stream, args: &Vec<String>, tool_name: &String, default_stage: u32) {
    let props = TArgumentParserProps {
        description: "Execute a clvm script.".to_string(),
        prog: format!("clvm_tools {}", tool_name)
    };

    let mut parser = ArgumentParser::new(Some(props));
    parser.add_argument(
        vec!("--strict".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Unknown opcodes are always fatal errors in strict mode".to_string())
    );
    parser.add_argument(
        vec!("-x".to_string(), "--hex".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Read program and environment as hexadecimal bytecode".to_string())
    );
    parser.add_argument(
        vec!("-s".to_string(), "--stage".to_string()),
        Argument::new().
            set_type(Rc::new(StageImport {})).
            set_help("stage number to include".to_string()).
            set_default(ArgumentValue::ArgInt(default_stage as i64))
    );
    parser.add_argument(
        vec!("-v".to_string(), "--verbose".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Display resolve of all reductions, for debugging".to_string())
    );
    parser.add_argument(
        vec!("-t".to_string(), "--table".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Print diagnostic table of reductions, for debugging".to_string())
    );
    parser.add_argument(
        vec!("-c".to_string(), "--cost".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Show cost".to_string())
    );
    parser.add_argument(
        vec!("--time".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Print execution time".to_string())
    );
    parser.add_argument(
        vec!("-d".to_string(), "--dump".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("dump hex version of final output".to_string())
    );
    parser.add_argument(
        vec!("--quiet".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Suppress printing the program result".to_string())
    );
    parser.add_argument(
        vec!("-y".to_string(), "--symbol-table".to_string()),
        Argument::new().
            set_type(Rc::new(PathJoin {})).
            set_help(".SYM file generated by compiler".to_string())
    );
    parser.add_argument(
        vec!("-n".to_string(), "--no-keywords".to_string()),
        Argument::new().
            set_action(TArgOptionAction::StoreTrue).
            set_help("Output result as data, not as a program".to_string())
    );
    parser.add_argument(
        vec!("-i".to_string(), "--include".to_string()),
        Argument::new().
            set_type(Rc::new(PathJoin {})).
            set_help("add a search path for included files".to_string()).
            set_action(TArgOptionAction::Append).
            set_default(ArgumentValue::ArgArray(vec!()))
    );
    parser.add_argument(
        vec!("path_or_code".to_string()),
        Argument::new().
            set_type(Rc::new(PathOrCodeConv {})).
            set_help("filepath to clvm script, or a literal script".to_string())
    );
    parser.add_argument(
        vec!("env".to_string()),
        Argument::new().
            set_n_args(NArgsSpec::Optional).
            set_type(Rc::new(PathOrCodeConv {})).
            set_help("clvm script environment, as clvm src, or hex".to_string())
    );
    parser.add_argument(
        vec!("-m".to_string(), "--max-cost".to_string()),
        Argument::new().
            set_type(Rc::new(IntConversion::new(Rc::new(|| "help".to_string())))).
            set_default(ArgumentValue::ArgInt(11000000000)).
            set_help("Maximum cost".to_string())
    );

    let arg_vec = args[1..].to_vec();
    let parsedArgs: HashMap<String, ArgumentValue>;

    match parser.parse_args(&arg_vec) {
        Err(e) => {
            stdout.write_string(format!("FAIL: {}\n", e));
            return;
        },
        Ok(pa) => { parsedArgs = pa; }
    }

    let empty_map = HashMap::new();
    let keywords =
        match parsedArgs.get("no_keywords") {
            None => KEYWORD_FROM_ATOM(),
            Some(ArgumentValue::ArgBool(b)) => &empty_map,
            _ => KEYWORD_FROM_ATOM()
        };

    let mut run_program: Rc<dyn TRunProgram>;
    match parsedArgs.get("include") {
        Some(ArgumentValue::ArgArray(v)) => {
            let mut bare_paths = Vec::with_capacity(v.len());
            for p in v {
                match p {
                    ArgumentValue::ArgString(s) => bare_paths.push(s.to_string()),
                    _ => { }
                }
            }
            run_program = run_program_for_search_paths(&bare_paths);
        },
        _ => {
            run_program = Rc::new(DefaultProgramRunner::new());
        }
    }

    let mut allocator = Allocator::new();

    let mut input_serialized = None;
    let mut input_sexp = None;

    let time_start = SystemTime::now();
    let mut time_read_hex = SystemTime::now();
    let mut time_assemble = SystemTime::now();
    let mut time_parse_input;

    let mut input_program = "()".to_string();
    let mut input_args = "()".to_string();

    match parsedArgs.get("path_or_code") {
        Some(ArgumentValue::ArgString(path_or_code)) => {
            input_program = path_or_code.to_string();
        },
        _ => { }
    }

    match parsedArgs.get("hex") {
        Some(_) => {
            let assembled_serialized =
                Bytes::new(Some(BytesFromType::Hex(input_program.to_string())));
            if input_args.len() == 0 {
                input_args = "80".to_string();
            }

            let env_serialized =
                Bytes::new(Some(BytesFromType::Hex(input_args.to_string())));
            time_read_hex = SystemTime::now();

            input_serialized =
                Some(
                    Bytes::new(Some(BytesFromType::Raw(vec!(0xff)))).
                        concat(&assembled_serialized).
                        concat(&env_serialized)
                );

            let mut stream = Stream::new(input_serialized.clone());
            input_sexp = sexp_from_stream(
                &mut allocator,
                &mut stream,
                Box::new(SimpleCreateCLVMObject {}),
            ).map(|x| Some(x.1)).unwrap();
        },
        _ => {
            let src_sexp;
            match parsedArgs.get("path_or_code") {
                Some(ArgumentValue::ArgString(s)) => {
                    match read_ir(&s) {
                        Ok(s) => { src_sexp = s; },
                        Err(e) => {
                            stdout.write_string(format!("FAIL: {}\n", e));
                            return;
                        }
                    }
                },
                _ => {
                    stdout.write_string(format!("FAIL: {}\n", "non-string argument"));
                    return;
                }
            }

            let assembled_sexp =
                assemble_from_ir(&mut allocator, Rc::new(src_sexp)).unwrap();
            let mut parsed_args_result = "()".to_string();

            match parsedArgs.get("env") {
                Some(ArgumentValue::ArgString(s)) => {
                    parsed_args_result = s.to_string();
                },
                _ => { }
            }

            let env_ir = read_ir(&parsed_args_result).unwrap();
            let env = assemble_from_ir(&mut allocator, Rc::new(env_ir)).unwrap();
            time_assemble = SystemTime::now();

            input_sexp = allocator.new_pair(assembled_sexp, env).map(|x| Some(x)).unwrap();
        }
    }

    let mut pre_eval_f: Option<PreEval> = None;
    let log_entries: Rc<RunLog> =
        Rc::new(RunLog { log_entries: RefCell::new(Vec::new()) });
    let mut symbol_table: Option<HashMap<String,String>> = None;

    // clvm_rs uses boxed callbacks with unspecified lifetimes so in order to
    // support logging as intended, we must have values that can be moved so
    // the callbacks can become immortal.  Our strategy is to use channels
    // and threads for this.
    let (pre_eval_req_out, pre_eval_req_in) = channel();
    let (pre_eval_resp_out, pre_eval_resp_in): (Sender<()>, Receiver<()>) =
        channel();

    let (post_eval_req_out, post_eval_req_in) = channel();
    let (post_eval_resp_out, post_eval_resp_in): (Sender<()>, Receiver<()>) =
        channel();

    /*
    match (log_entries.pop(), n) {
        (Some(ent), Some(n)) => {
            match proper_list(alloc, ent, true) {
                Some(list) => {
                    enlist(
                        alloc,
                        &vec!(list[0], list[1], n)
                    ).map(|x| {
                        log_entries.push(x);
                        return x;
                    });
                },
                _ => { }
            }
        }
        _ => { }
    }
     */

    match parsedArgs.get("symbol_table").and_then(|jstring| match jstring {
        ArgumentValue::ArgString(s) => {
            let decoded_symbol_table: Option<HashMap<String,String>> =
                serde_json::from_str(s).ok();
            return decoded_symbol_table;
        },
        _ => None
    }) {
        Some(st) => {
            // Part 1 of supporting callbacks in unlifetimed boxes: allow the
            // callbacks to take everything they need with them, effectively
            // becoming immortal functions.
            //
            // This means they must *move* everything they need and can have
            // no shared references with anything in any function scope.
            let symbol_table_clone: HashMap<String,String> = st.clone();
            symbol_table = Some(st);

            let post_eval_fn: Rc<dyn Fn(Option<NodePtr>)> =
                Rc::new(move |n| {
                    post_eval_req_out.send(n);
                    post_eval_resp_in.recv().unwrap();
                });

            let pre_eval_fn: Rc<dyn Fn(&mut Allocator, NodePtr)> =
                Rc::new(move |allocator, new_log| {
                    pre_eval_req_out.send(new_log);
                    pre_eval_resp_in.recv().unwrap();
                });

            let closure: Rc<dyn Fn() -> Box<dyn Fn(Option<NodePtr>)>> = Rc::new(
                move || {
                    let post_eval_fn_clone = post_eval_fn.clone();
                    Box::new(move |n| {
                        let post_eval_fn_clone_2 = post_eval_fn_clone.clone();
                        (*post_eval_fn_clone_2)(n)
                    })
                }
            );

            let pre_eval_f_closure:
               Box<dyn Fn(&mut Allocator, NodePtr, NodePtr) ->
                  Result<Option<Box<(dyn Fn(Option<NodePtr>))>>, EvalErr>
               > =
                Box::new(move |allocator, sexp, args| {
                    let pre_eval_clone = pre_eval_fn.clone();
                    trace_pre_eval(
                        allocator,
                        &|allocator, n| (*pre_eval_clone)(allocator, n),
                        Some(symbol_table_clone.clone()),
                        sexp,
                        args,
                    ).map(|t| t.map(|_| {
                        let closure_clone = closure.clone();
                        return (*closure_clone)();
                    }))
                });

            pre_eval_f = Some(pre_eval_f_closure);
        },
        _ => {
            /*
            match (parsedArgs.get("verbose"), parsedArgs.get("table")) {
                (Some(ArgumentValue::ArgBool(true)), Some(_)) => {
                    pre_eval_f = Some(Box::new(|allocator, sexp, args| {
                        trace_pre_eval(
                            &mut allocator,
                            &mut log_entries,
                            None,
                            sexp,
                            args
                        ).map(|t| t.map(|_| {
                            let closure: Box<dyn Fn(Option<NodePtr>)> = Box::new(
                                move |n| {
                                    post_eval_req_out.send(n);
                                    post_eval_resp_in.recv().unwrap();
                                });
                            return closure;
                        }))
                    }))
                },
                _ => { }
            }
            */
        }
    }

    let run_script =
        match parsedArgs.get("stage") {
            Some(ArgumentValue::ArgInt(0)) => { stages::brun(&mut allocator) },
            _ => { stages::run(&mut allocator) }
        };

    let mut output = "(didn't finish)".to_string();
    let cost_offset = calculate_cost_offset(
        &mut allocator,
        run_program.clone(),
        run_script
    );

    let max_cost =
        parsedArgs.get("max_cost").map(|x| match x {
            ArgumentValue::ArgInt(i) => *i as i64 - cost_offset,
            _ => 0
        }).unwrap_or_else(|| 0);
    let max_cost = max(0, max_cost);

    if input_sexp.is_none() {
        input_sexp = sexp_from_stream(
            &mut allocator,
            &mut Stream::new(input_serialized.clone()),
            Box::new(SimpleCreateCLVMObject {})
        ).map(|x| Some(x.1)).unwrap();
    };

    time_parse_input = SystemTime::now();
    let res =
        run_program.run_program(
            &mut allocator,
            run_script,
            input_sexp.unwrap(),
            Some(RunProgramOption {
                operator_lookup: None,
                max_cost: if max_cost == 0 { None } else { Some(max_cost as u64) },
                pre_eval_f: pre_eval_f,
                strict: parsedArgs.get("strict").map(|_| true).unwrap_or_else(|| false)
            })
        ).map(|run_program_result| {
            let mut cost: i64 = run_program_result.0 as i64;
            let result = run_program_result.1;
            let time_done = SystemTime::now();

            let _ =
                if !parsedArgs.get("cost").is_none() {
                    if cost > 0 {
                        cost += cost_offset;
                    }
                    stdout.write_string(format!("cost = {}\n", cost));
                };

            let _ =
                match parsedArgs.get("time") {
                    Some(ArgumentValue::ArgInt(t)) => {
                        match parsedArgs.get("hex") {
                            Some(_) => {
                                stdout.write_string(format!("read_hex: {}\n", time_read_hex.duration_since(time_start).unwrap().as_millis()));
                            },
                            _ => {
                                stdout.write_string(format!("assemble_from_ir: {}\n", time_assemble.duration_since(time_start).unwrap().as_millis()));
                                stdout.write_string(format!("to_sexp_f: {}\n", time_parse_input.duration_since(time_assemble).unwrap().as_millis()));
                            }
                        }
                        stdout.write_string(format!("run_program: {}\n", time_done.duration_since(time_parse_input).unwrap().as_millis()));
                    },
                    _ => { }
                };

            let _ = output = disassemble_with_kw(&mut allocator, result, keywords);
            let _ =
                match parsedArgs.get("dump") {
                    Some(ArgumentValue::ArgBool(true)) => {
                        let mut f = Stream::new(None);
                        sexp_to_stream(&mut allocator, result, &mut f);
                        output = f.get_value().hex();
                    },
                    _ => {
                        match parsedArgs.get("quiet") {
                            Some(ArgumentValue::ArgBool(true)) => {
                                output = "".to_string();
                            },
                            _ => { }
                        }
                    }
                };

            output
        });

    let output = collapse(res.map_err(|ex| {
        format!("FAIL: {} {}", ex.1, disassemble_with_kw(&mut allocator, ex.0, keywords))
    }));

    stdout.write_string(format!("{}\n", output));
    let trace_to_text_enabled =
        !symbol_table.is_none() ||
        match parsedArgs.get("verbose") {
            Some(ArgumentValue::ArgBool(true)) => true,
            _ => false
        };

    let mut log_content = log_entries.finish();
    if trace_to_text_enabled {
        let use_symtab = symbol_table.clone().unwrap_or_else(|| HashMap::new());
        stdout.write_string(format!(""));
        trace_to_text(
            &mut allocator, &log_content, Some(use_symtab.clone()), &disassemble
        );
        if !parsedArgs.get("table").is_none() {
            trace_to_table(
                &mut allocator,
                &mut log_content,
                symbol_table,
                &disassemble
            );
        }
    }
}

// export function read_ir(args: str[]){
//   const parser = new argparse.ArgumentParser({description: "Read script and tokenize to IR."});
//   parser.add_argument(
//     ["script"], {help: "script in hex or uncompiled text"});
  
//   const parsedArgs = parser.parse_args(args.slice(1));
  
//   const sexp = reader.read_ir(parsedArgs["script"] as string);
//   const blob = stream_to_bin(f => sexp_to_stream(sexp, f));
//   print(blob.hex());
// }

/*
Copyright 2018 Chia Network Inc
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
   http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 */
