use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::chia_dialect::{ChiaDialect, NO_NEG_DIV, NO_UNKNOWN_OPS};
use clvm_rs::cost::Cost;
use clvm_rs::dialect::Dialect;
use clvm_rs::reduction::{EvalErr, Reduction, Response};
use clvm_rs::run_program::run_program;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType, Stream};

use crate::classic::clvm::keyword_from_atom;
use crate::classic::clvm::sexp::proper_list;

use crate::classic::clvm_tools::binutils::{assemble_from_ir, disassemble_to_ir_with_kw};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::ir::writer::write_ir_to_stream;
use crate::classic::clvm_tools::sha256tree::TreeHash;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner, RunProgramOption, TRunProgram,
};
use crate::classic::clvm_tools::stages::stage_2::compile::do_com_prog_for_dialect;
use crate::classic::clvm_tools::stages::stage_2::optimize::do_optimize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AllocatorRefOrTreeHash {
    AllocatorRef(NodePtr),
    TreeHash(TreeHash),
}

impl AllocatorRefOrTreeHash {
    pub fn new_from_nodeptr(n: NodePtr) -> Self {
        AllocatorRefOrTreeHash::AllocatorRef(n)
    }

    pub fn new_from_sexp(allocator: &mut Allocator, n: NodePtr) -> Self {
        AllocatorRefOrTreeHash::TreeHash(TreeHash::new_from_sexp(allocator, n))
    }
}

pub struct CompilerOperatorsInternal {
    base_dialect: Rc<dyn Dialect>,
    source_file: String,
    search_paths: Vec<String>,
    symbols_extra_info: bool,
    compile_outcomes: RefCell<HashMap<String, String>>,
    runner: RefCell<Rc<dyn TRunProgram>>,
    opt_memo: RefCell<HashMap<AllocatorRefOrTreeHash, NodePtr>>,
}

pub fn full_path_for_filename(
    parent_sexp: NodePtr,
    filename: &str,
    search_paths: &[String],
) -> Result<String, EvalErr> {
    for path in search_paths.iter() {
        let mut path_buf = PathBuf::new();
        path_buf.push(path);
        path_buf.push(filename);
        let f_path = path_buf.as_path();
        if f_path.exists() {
            return f_path
                .to_str()
                .map(|x| x.to_owned())
                .map(Ok)
                .unwrap_or_else(|| {
                    Err(EvalErr(
                        parent_sexp,
                        "could not compute absolute path".to_string(),
                    ))
                });
        }
    }

    Err(EvalErr(parent_sexp, "can't open file".to_string()))
}

pub struct CompilerOperators {
    parent: Rc<CompilerOperatorsInternal>,
}

// This wrapper object is here to hold a drop trait that untangles CompilerOperatorsInternal.
// The design of this code requires the lifetime of the compiler object (via Rc<dyn TRunProgram>)
// to be uncertain from rust's perspective (i'm not given a lifetime parameter for the runnable
// passed to clvmr, so I chose this way to mitigate the lack of specifiable lifetime as passing
// down a reference became very hairy.  The downside is that a few objects had become fixed in
// an Rc cycle.  The drop trait below corrects that.
impl CompilerOperators {
    pub fn new(source_file: &str, search_paths: Vec<String>, symbols_extra_info: bool) -> Self {
        CompilerOperators {
            parent: Rc::new(CompilerOperatorsInternal::new(
                source_file,
                search_paths,
                symbols_extra_info,
            )),
        }
    }
}

impl Drop for CompilerOperators {
    fn drop(&mut self) {
        self.parent.neutralize();
    }
}

impl CompilerOperatorsInternal {
    pub fn new(source_file: &str, search_paths: Vec<String>, symbols_extra_info: bool) -> Self {
        let base_dialect = Rc::new(ChiaDialect::new(NO_NEG_DIV | NO_UNKNOWN_OPS));
        let base_runner = Rc::new(DefaultProgramRunner::new());
        CompilerOperatorsInternal {
            base_dialect,
            source_file: source_file.to_owned(),
            search_paths,
            symbols_extra_info,
            compile_outcomes: RefCell::new(HashMap::new()),
            runner: RefCell::new(base_runner),
            opt_memo: RefCell::new(HashMap::new()),
        }
    }

    pub fn neutralize(&self) {
        self.set_runner(Rc::new(DefaultProgramRunner::new()));
    }

    fn symbols_extra_info(&self, allocator: &mut Allocator) -> Response {
        if self.symbols_extra_info {
            Ok(Reduction(1, allocator.new_atom(&[1])?))
        } else {
            Ok(Reduction(1, allocator.null()))
        }
    }

    fn set_runner(&self, runner: Rc<dyn TRunProgram>) {
        self.runner.replace(runner);
    }

    fn get_runner(&self) -> Rc<dyn TRunProgram> {
        let borrow: Ref<'_, Rc<dyn TRunProgram>> = self.runner.borrow();
        borrow.clone()
    }

    fn read(&self, allocator: &mut Allocator, sexp: NodePtr) -> Response {
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

    fn write(&self, allocator: &mut Allocator, sexp: NodePtr) -> Response {
        if let SExp::Pair(filename_sexp, r) = allocator.sexp(sexp) {
            if let SExp::Pair(data, _) = allocator.sexp(r) {
                if let SExp::Atom(filename_buf) = allocator.sexp(filename_sexp) {
                    let filename_buf = allocator.buf(&filename_buf);
                    let filename_bytes =
                        Bytes::new(Some(BytesFromType::Raw(filename_buf.to_vec())));
                    let ir = disassemble_to_ir_with_kw(allocator, data, keyword_from_atom(), true);
                    let mut stream = Stream::new(None);
                    write_ir_to_stream(Rc::new(ir), &mut stream);
                    return fs::write(filename_bytes.decode(), stream.get_value().decode())
                        .map_err(|_| {
                            EvalErr(sexp, format!("failed to write {}", filename_bytes.decode()))
                        })
                        .map(|_| Reduction(1, allocator.null()));
                }
            }
        }

        Err(EvalErr(sexp, "failed to write data".to_string()))
    }

    fn get_compile_filename(&self, allocator: &mut Allocator) -> Response {
        let converted_filename = allocator.new_atom(self.source_file.as_bytes())?;
        Ok(Reduction(1, converted_filename))
    }

    fn get_include_paths(&self, allocator: &mut Allocator) -> Response {
        let mut converted_search_paths = allocator.null();
        for s in self.search_paths.iter().rev() {
            let search_path_string = allocator.new_atom(s.as_bytes())?;
            converted_search_paths =
                allocator.new_pair(search_path_string, converted_search_paths)?;
        }

        Ok(Reduction(1, converted_search_paths))
    }

    fn get_full_path_for_filename(&self, allocator: &mut Allocator, sexp: NodePtr) -> Response {
        if let SExp::Pair(l, _r) = allocator.sexp(sexp) {
            if let SExp::Atom(b) = allocator.sexp(l) {
                let filename =
                    Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                let full_name = full_path_for_filename(sexp, &filename, &self.search_paths)?;
                let converted_filename = allocator.new_atom(full_name.as_bytes())?;
                return Ok(Reduction(1, converted_filename));
            }
        }

        Err(EvalErr(sexp, "can't open file".to_string()))
    }

    fn get_source_file(&self, allocator: &mut Allocator) -> Result<Reduction, EvalErr> {
        let file_name_bytes = Bytes::new(Some(BytesFromType::String(self.source_file.clone())));
        let new_atom = allocator.new_atom(file_name_bytes.data())?;
        Ok(Reduction(1, new_atom))
    }

    pub fn set_symbol_table(
        &self,
        allocator: &mut Allocator,
        table: NodePtr,
    ) -> Result<Reduction, EvalErr> {
        if let Some(symtable) =
            proper_list(allocator, table, true).and_then(|t| proper_list(allocator, t[0], true))
        {
            for kv in symtable.iter() {
                if let SExp::Pair(hash, name) = allocator.sexp(*kv) {
                    if let (SExp::Atom(hash), SExp::Atom(name)) =
                        (allocator.sexp(hash), allocator.sexp(name))
                    {
                        let hash_text =
                            Bytes::new(Some(BytesFromType::Raw(allocator.buf(&hash).to_vec())))
                                .decode();
                        let name_text =
                            Bytes::new(Some(BytesFromType::Raw(allocator.buf(&name).to_vec())))
                                .decode();

                        self.compile_outcomes.replace_with(|co| {
                            let mut result = co.clone();
                            result.insert(hash_text, name_text);
                            result
                        });
                    }
                }
            }
        }

        Ok(Reduction(1, allocator.null()))
    }
}

impl Dialect for CompilerOperatorsInternal {
    fn val_stack_limit(&self) -> usize {
        10000000
    }
    fn quote_kw(&self) -> &[u8] {
        &[1]
    }
    fn apply_kw(&self) -> &[u8] {
        &[2]
    }

    fn op(
        &self,
        allocator: &mut Allocator,
        op: NodePtr,
        sexp: NodePtr,
        max_cost: Cost,
    ) -> Response {
        match allocator.sexp(op) {
            SExp::Atom(opname) => {
                let opbuf = allocator.buf(&opname);
                if opbuf == "_read".as_bytes() {
                    self.read(allocator, sexp)
                } else if opbuf == "_write".as_bytes() {
                    self.write(allocator, sexp)
                } else if opbuf == "com".as_bytes() {
                    do_com_prog_for_dialect(self.get_runner(), allocator, sexp)
                } else if opbuf == "opt".as_bytes() {
                    do_optimize(self.get_runner(), allocator, &self.opt_memo, sexp)
                } else if opbuf == "_set_symbol_table".as_bytes() {
                    self.set_symbol_table(allocator, sexp)
                } else if opbuf == "_get_compile_filename".as_bytes() {
                    self.get_compile_filename(allocator)
                } else if opbuf == "_get_include_paths".as_bytes() {
                    self.get_include_paths(allocator)
                } else if opbuf == "_full_path_for_name".as_bytes() {
                    self.get_full_path_for_filename(allocator, sexp)
                } else if opbuf == "_symbols_extra_info".as_bytes() {
                    self.symbols_extra_info(allocator)
                } else if opbuf == "_get_source_file".as_bytes() {
                    self.get_source_file(allocator)
                } else {
                    self.base_dialect.op(allocator, op, sexp, max_cost)
                }
            }
            _ => self.base_dialect.op(allocator, op, sexp, max_cost),
        }
    }
}

impl CompilerOperatorsInternal {
    pub fn get_compiles(&self) -> HashMap<String, String> {
        self.compile_outcomes.borrow().clone()
    }
}

impl CompilerOperators {
    pub fn get_compiles(&self) -> HashMap<String, String> {
        self.parent.get_compiles()
    }
}

impl TRunProgram for CompilerOperatorsInternal {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response {
        let max_cost = option.as_ref().and_then(|o| o.max_cost).unwrap_or(0);
        run_program(
            allocator,
            self,
            program,
            args,
            max_cost,
            option.and_then(|o| o.pre_eval_f),
        )
    }
}

impl TRunProgram for CompilerOperators {
    fn run_program(
        &self,
        allocator: &mut Allocator,
        program: NodePtr,
        args: NodePtr,
        option: Option<RunProgramOption>,
    ) -> Response {
        self.parent.run_program(allocator, program, args, option)
    }
}

pub fn run_program_for_search_paths(
    source_file: &str,
    search_paths: &[String],
    symbols_extra_info: bool,
) -> Rc<CompilerOperators> {
    let ops = Rc::new(CompilerOperators::new(
        source_file,
        search_paths.to_vec(),
        symbols_extra_info,
    ));
    ops.parent.set_runner(ops.parent.clone());
    ops
}
