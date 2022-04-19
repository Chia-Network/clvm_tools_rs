use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::cost::Cost;
use clvm_rs::operator_handler::OperatorHandler;
use clvm_rs::reduction::{EvalErr, Reduction, Response};

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};

use crate::classic::clvm::sexp::atom;
use crate::classic::clvm::KEYWORD_FROM_ATOM;

use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble_to_ir_with_kw};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::ir::writer::write_ir_to_stream;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner, RunProgramOption, TRunProgram,
};
use crate::classic::clvm_tools::stages::stage_2::compile::DoComProg;
use crate::classic::clvm_tools::stages::stage_2::optimize::DoOptProg;

struct DoRead {}

impl OperatorHandler for DoRead {
    fn op(
        &self,
        allocator: &mut Allocator,
        _op: NodePtr,
        sexp: NodePtr,
        _max_cost: Cost,
    ) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(f, _) => match allocator.sexp(f) {
                SExp::Atom(b) => {
                    let filename =
                        Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                    fs::read_to_string(filename)
                        .map_err(|_| EvalErr(allocator.null(), "Failed to read file".to_string()))
                        .and_then(|content| {
                            read_ir(&content)
                                .map_err(|e| EvalErr(allocator.null(), e))
                                .and_then(|ir| {
                                    assemble_from_ir(allocator, Rc::new(ir))
                                        .map(|ir_sexp| Reduction(1, ir_sexp))
                                })
                        })
                }
                _ => Err(EvalErr(
                    allocator.null(),
                    "filename is not an atom".to_string(),
                )),
            },
            _ => Err(EvalErr(
                allocator.null(),
                "given a program that is an atom".to_string(),
            )),
        }
    }
}

struct DoWrite {}

impl OperatorHandler for DoWrite {
    fn op(
        &self,
        allocator: &mut Allocator,
        _op: NodePtr,
        sexp: NodePtr,
        _max_cost: Cost,
    ) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(filename_sexp, r) => match allocator.sexp(r) {
                SExp::Pair(data, _) => match allocator.sexp(filename_sexp) {
                    SExp::Atom(filename_buf) => {
                        let filename_buf = allocator.buf(&filename_buf);
                        let filename_bytes =
                            Bytes::new(Some(BytesFromType::Raw(filename_buf.to_vec())));
                        let ir =
                            disassemble_to_ir_with_kw(allocator, data, KEYWORD_FROM_ATOM(), true);
                        let mut stream = Stream::new(None);
                        write_ir_to_stream(Rc::new(ir), &mut stream);
                        return fs::write(filename_bytes.decode(), stream.get_value().decode())
                            .map_err(|_| {
                                return EvalErr(
                                    sexp,
                                    format!("failed to write {}", filename_bytes.decode()),
                                );
                            })
                            .map(|_| Reduction(1, allocator.null()));
                    }
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }

        Err(EvalErr(sexp, "failed to write data".to_string()))
    }
}

struct GetFullPathForName {
    search_paths: Vec<String>,
}

impl OperatorHandler for GetFullPathForName {
    fn op(
        &self,
        allocator: &mut Allocator,
        _op: NodePtr,
        sexp: NodePtr,
        _max_cost: Cost,
    ) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(l, _r) => match allocator.sexp(l) {
                SExp::Atom(b) => {
                    let filename =
                        Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                    for path in &self.search_paths {
                        let mut path_buf = PathBuf::new();
                        path_buf.push(path);
                        path_buf.push(filename.clone());
                        let f_path = path_buf.as_path();
                        if f_path.exists() {
                            return f_path
                                .to_str()
                                .map(|r| Ok(r))
                                .unwrap_or_else(|| {
                                    Err(EvalErr(
                                        sexp,
                                        "could not compute absolute path".to_string(),
                                    ))
                                })
                                .and_then(|p| {
                                    allocator
                                        .new_atom(p.as_bytes())
                                        .map(|res| Reduction(1, res))
                                });
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }

        Err(EvalErr(sexp, "can't open file".to_string()))
    }
}

pub struct RunProgramWithSearchPaths {
    runner: RefCell<DefaultProgramRunner>,
    do_com_prog: RefCell<DoComProg>,
    do_opt_prog: RefCell<DoOptProg>,
    search_paths: Vec<String>,
}

impl OperatorHandler for RunProgramWithSearchPaths {
    fn op(
        &self,
        allocator: &mut Allocator,
        op: NodePtr,
        sexp: NodePtr,
        max_cost: Cost,
    ) -> Response {
        return m! {
            op_buf <- atom(allocator, op);
            let op_vec = allocator.buf(&op_buf).to_vec();
            if op_vec == vec!('c' as u8, 'o' as u8, 'm' as u8) {
                self.do_com_prog.borrow().op(allocator, op, sexp, max_cost)
            } else if op_vec == vec!('o' as u8, 'p' as u8, 't' as u8) {
                self.do_opt_prog.borrow().op(allocator, op, sexp, max_cost)
            } else if op_vec == "_set_symbol_table".as_bytes().to_vec() {
                self.do_com_prog.borrow().set_symbol_table(allocator, sexp)
            } else {
                Err(EvalErr(sexp, "unknown op".to_string()))
            }
        };
    }
}

impl RunProgramWithSearchPaths {
    fn new(search_paths: &Vec<String>) -> Self {
        RunProgramWithSearchPaths {
            do_com_prog: RefCell::new(DoComProg::new()),
            do_opt_prog: RefCell::new(DoOptProg::new()),
            runner: RefCell::new(DefaultProgramRunner::new()),
            search_paths: search_paths.to_vec(),
        }
    }

    fn setup(&self, myself: Rc<RunProgramWithSearchPaths>) {
        self.runner.replace_with(|runner| {
            runner.add_handler(
                &"_full_path_for_name".as_bytes().to_vec(),
                Rc::new(GetFullPathForName {
                    search_paths: self.search_paths.to_vec(),
                }),
            );
            runner.add_handler(&"_read".as_bytes().to_vec(), Rc::new(DoRead {}));
            runner.add_handler(&"_write".as_bytes().to_vec(), Rc::new(DoWrite {}));
            runner.add_handler(&"com".as_bytes().to_vec(), myself.clone());
            runner.add_handler(&"opt".as_bytes().to_vec(), myself.clone());
            runner.add_handler(&"_set_symbol_table".as_bytes().to_vec(), myself.clone());

            runner.clone()
        });

        self.do_com_prog.replace_with(|do_com_prog| {
            do_com_prog.set_runner(myself.clone());
            do_com_prog.clone()
        });

        self.do_opt_prog.replace_with(|do_opt_prog| {
            do_opt_prog.set_runner(myself.clone());
            do_opt_prog.clone()
        });
    }

    pub fn showtable(&self) -> String {
        self.runner.borrow().router.showtable()
    }

    pub fn get_compiles(&self) -> HashMap<String, String> {
        self.do_com_prog.borrow().get_compiles()
    }
}

impl TRunProgram for RunProgramWithSearchPaths {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response {
        return self
            .runner
            .borrow()
            .run_program(allocator, program, args, option);
    }
}

pub fn run_program_for_search_paths(search_paths: &Vec<String>) -> Rc<RunProgramWithSearchPaths> {
    let prog = Rc::new(RunProgramWithSearchPaths::new(&search_paths.to_vec()));
    prog.setup(prog.clone());
    prog
}
