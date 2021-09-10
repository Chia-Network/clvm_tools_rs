use std::collections::HashMap;
use std::fs;
use std::rc::Rc;
use std::path::PathBuf;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::{
    EvalErr,
    Reduction,
    Response
};

use clvm_rs::run_program::OperatorHandler;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    Stream
};

use crate::classic::clvm::{
    KEYWORD_TO_ATOM
};

use crate::classic::clvm_tools::binutils::{
    assemble_from_ir,
    disassemble_to_ir_with_kw
};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::ir::writer::write_ir_to_stream;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    RunProgramOption,
    TRunProgram
};
use crate::classic::clvm_tools::stages::stage_2::compile::make_do_com;
use crate::classic::clvm_tools::stages::stage_2::optimize::make_do_opt;

struct DoRead {
}

impl OperatorHandler for DoRead {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(f,r) => {
                match allocator.sexp(f) {
                    SExp::Atom(b) => {
                        let filename = Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                        return fs::read_to_string(filename).map_err(
                            |_| EvalErr(allocator.null(), "Failed to read file".to_string())
                        ).and_then(|content| {
                            return read_ir(&content).
                                map_err(|e| EvalErr(allocator.null(), e)).
                                and_then(|ir| {
                                    return assemble_from_ir(allocator, Rc::new(ir)).map(|ir_sexp| {
                                        return Reduction(1, ir_sexp);
                                    });
                                });
                        });
                    },
                    _ => {
                        return Err(EvalErr(allocator.null(), "filename is not an atom".to_string()));
                    }
                }
            },
            _ => {
                return Err(EvalErr(allocator.null(), "given a program that is an atom".to_string()));
            }
        }
    }
}

struct DoWrite {
}

impl OperatorHandler for DoWrite {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(filename_sexp,r) => {
                match allocator.sexp(r) {
                    SExp::Pair(data,_) => {
                        match allocator.sexp(filename_sexp) {
                            SExp::Atom(filename_buf) => {
                                let filename_buf = allocator.buf(&filename_buf);
                                let filename_bytes = Bytes::new(Some(BytesFromType::Raw(filename_buf.to_vec())));
                                let ir = disassemble_to_ir_with_kw(
                                    allocator,
                                    data,
                                    KEYWORD_TO_ATOM(),
                                    true,
                                    true
                                );
                                let mut stream = Stream::new(None);
                                write_ir_to_stream(Rc::new(ir), &mut stream);
                                return fs::write(filename_bytes.decode(), stream.get_value().decode()).map_err(|_| {
                                    return EvalErr(sexp, format!("failed to write {}", filename_bytes.decode()));
                                }).map(|_| {
                                    return Reduction(1, allocator.null());
                                });
                            },
                            _ => {}
                        }
                    },
                    _ => {}
                }
            }
        }

        return Err(EvalErr(sexp, "failed to write data".to_string()));
    }
}

struct GetFullPathForName {
    search_paths: Vec<String>
}

impl OperatorHandler for GetFullPathForName {
    fn op(&self, allocator: &mut Allocator, op: NodePtr, sexp: NodePtr, max_cost: Cost) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(l,r) => {
                match allocator.sexp(l) {
                    SExp::Atom(b) => {
                        let filename = Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                        for path in self.search_paths {
                            let path_buf = PathBuf::new();
                            path_buf.push(path);
                            path_buf.push(filename);
                            let f_path = path_buf.as_path();
                            if f_path.exists() {
                                return f_path.to_str().
                                    map(|r| Ok(r)).
                                    unwrap_or_else(|| Err(EvalErr(sexp, "could not compute absolute path".to_string()))).
                                    and_then(|p| {
                                        return allocator.new_atom(p.as_bytes()).map(|res| {
                                            return Reduction(1, res);
                                        });
                                    });
                            }
                        }
                    },
                    _ => { }
                }
            },
            _ => {}
        }

        return Err(EvalErr(sexp, "can't open file".to_string()));
    }
}

struct RunProgramWithSearchPaths {
    operator_lookup: HashMap<Vec<u8>, Rc<dyn OperatorHandler>>,
    search_paths: Vec<String>
}

impl<'a> RunProgramWithSearchPaths {
    fn new(
        operators: &HashMap<Vec<u8>, Rc<dyn OperatorHandler>>,
        search_paths: &Vec<String>
    ) -> Rc<Self> {
        let mut result = Rc::new(RunProgramWithSearchPaths {
            operator_lookup: operators.clone(),
            search_paths: search_paths.to_vec()
        });

        result.operator_lookup.insert(
            vec!('c' as u8, 'o' as u8, 'm' as u8),
            Rc::new(make_do_com(result.clone()))
        );
        result.operator_lookup.insert(
            vec!('o' as u8, 'p' as u8, 't' as u8),
            Rc::new(make_do_opt(result.clone()))
        );
        result.operator_lookup.insert(
            "_full_path_for_name".as_bytes().to_vec(),
            Rc::new(GetFullPathForName { search_paths: search_paths.to_vec() })
        );
        result.operator_lookup.insert("_read".as_bytes().to_vec(), Rc::new(DoRead {}));
        result.operator_lookup.insert("_write".as_bytes().to_vec(), Rc::new(DoWrite {}));

        return result;
    }
}

impl<'a> TRunProgram<'a> for RunProgramWithSearchPaths {
    fn run_program(
        &self,
        allocator: &'a mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>
    ) -> Response {
        let runner = DefaultProgramRunner::new();
        return runner.run_program(allocator, program, args, option);
    }
}

pub fn run_program_for_search_paths<'a>(
    operators: &HashMap<Vec<u8>, Rc<dyn OperatorHandler>>,
    search_paths: &Vec<String>
) -> Rc<RunProgramWithSearchPaths> {
    return RunProgramWithSearchPaths::new(operators, &search_paths.to_vec());
}
