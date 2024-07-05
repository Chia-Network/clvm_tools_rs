use std::collections::HashMap;
use std::rc::Rc;

use clvmr::{Allocator, NodePtr};

use crate::classic::clvm::__type_compatibility__::{Bytes, Stream, UnvalidatedBytesFromType};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::platform::argparse::ArgumentValue;

use crate::classic::clvm_tools::binutils::assemble_from_ir;
use crate::classic::clvm_tools::ir::reader::read_ir;

use crate::compiler::dialect::{detect_modern, AcceptedDialect};

fn get_string_and_filename_with_default(
    parsed_args: &HashMap<String, ArgumentValue>,
    argument: &str,
    default: Option<&str>,
) -> Option<(Option<String>, String)> {
    if let Some(ArgumentValue::ArgString(path, content)) = parsed_args.get(argument) {
        Some((path.clone(), content.to_string()))
    } else {
        default.map(|p| (None, p.to_string()))
    }
}

pub struct ParsedInputPathOrCode {
    pub path: Option<String>,
    pub content: String,
    pub parsed: NodePtr,
}

pub fn parse_tool_input_sexp(
    allocator: &mut Allocator,
    argument: &str,
    parsed_args: &HashMap<String, ArgumentValue>,
    default_hex: Option<&str>,
    default_sexp: Option<&str>,
) -> Result<ParsedInputPathOrCode, String> {
    match parsed_args.get("hex") {
        Some(_) => {
            let (path, use_sexp_text) = if let Some(r) =
                get_string_and_filename_with_default(parsed_args, argument, default_hex)
            {
                r
            } else {
                return Err("missing argument {argument}".to_string());
            };

            let sexp_serialized =
                Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(use_sexp_text.clone())))
                    .map_err(|e| format!("{e:?}"))?;

            let mut prog_stream = Stream::new(Some(sexp_serialized));

            sexp_from_stream(
                allocator,
                &mut prog_stream,
                Box::new(SimpleCreateCLVMObject {}),
            )
            .map(|x| ParsedInputPathOrCode {
                path,
                content: use_sexp_text,
                parsed: x.1,
            })
            .map_err(|e| format!("{e:?}"))
        }
        _ => {
            let (path, use_sexp_text) = if let Some(r) =
                get_string_and_filename_with_default(parsed_args, argument, default_sexp)
            {
                r
            } else {
                return Err(format!("missing argument {argument}"));
            };

            read_ir(&use_sexp_text)
                .map_err(|e| format!("{e:?}"))
                .and_then(|v| {
                    Ok(ParsedInputPathOrCode {
                        path,
                        content: use_sexp_text,
                        parsed: assemble_from_ir(allocator, Rc::new(v))
                            .map_err(|e| format!("{e:?}"))?,
                    })
                })
        }
    }
}

pub struct RunAndCompileInputData {
    pub program: ParsedInputPathOrCode,
    pub args: ParsedInputPathOrCode,
    pub dialect: AcceptedDialect,
}

impl RunAndCompileInputData {
    pub fn new(
        allocator: &mut Allocator,
        parsed_args: &HashMap<String, ArgumentValue>,
    ) -> Result<RunAndCompileInputData, String> {
        let program = parse_tool_input_sexp(allocator, "path_or_code", parsed_args, None, None)?;
        let args = parse_tool_input_sexp(allocator, "env", parsed_args, Some("80"), Some("()"))?;
        let dialect = detect_modern(allocator, program.parsed);
        Ok(RunAndCompileInputData {
            program,
            args,
            dialect,
        })
    }
}
