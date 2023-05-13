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
use crate::classic::clvm::sexp::{enlist, First, proper_list, NodeSel, rest, Rest, SelectNode, ThisNode};

use crate::classic::clvm_tools::binutils::{assemble, assemble_from_ir, disassemble_to_ir_with_kw, disassemble};
use crate::classic::clvm_tools::clvmc::{compile_clvm_text, write_sym_output};
use crate::classic::clvm_tools::ir::reader::read_ir;
use crate::classic::clvm_tools::ir::writer::write_ir_to_stream;
use crate::classic::clvm_tools::sha256tree::TreeHash;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner, RunProgramOption, TRunProgram,
};
use crate::classic::clvm_tools::stages::stage_2::compile::{do_com_prog_for_dialect, make_symbols_name};
use crate::classic::clvm_tools::stages::stage_2::optimize::do_optimize;
use crate::classic::clvm_tools::stages::stage_2::reader::{convert_hex_to_sexp, PresentFile};

use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::sexp::decode_string;

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
    // A compiler opts as in the modern compiler.  If present, try using its
    // file system interface to read files.
    compiler_opts: RefCell<Option<Rc<dyn CompilerOpts>>>,
}

/// Given a list of search paths, find a full path to a file whose partial name
/// is given.  If the file can't be found in any search path, use the expression
/// the user gave to cause the file to be searched for in the error result.
/// They're searched in order so repetition doesn't do anything. (suggested Q+A)
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
                        format!("could not compute absolute path for the combination of search path {path} and file name {filename} during text conversion from path_buf")
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
            compiler_opts: RefCell::new(None),
        }
    }

    pub fn neutralize(&self) {
        self.set_runner(Rc::new(DefaultProgramRunner::new()));
        self.set_compiler_opts(None);
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

    fn set_compiler_opts(&self, opts: Option<Rc<dyn CompilerOpts>>) {
        self.compiler_opts.replace(opts);
    }

    fn get_compiler_opts(&self) -> Option<Rc<dyn CompilerOpts>> {
        let borrow: Ref<'_, Option<Rc<dyn CompilerOpts>>> = self.compiler_opts.borrow();
        borrow.clone()
    }

    fn primitive_read_internal(&self, allocator: &mut Allocator, parent_sexp: NodePtr, filename: &str) -> Result<PresentFile, EvalErr> {
        // Use the read interface in CompilerOpts if we have one.
        let (full_path, content) =
            if let Some(opts) = self.get_compiler_opts() {
                eprintln!("read with opts: {}", filename);
                eprintln!("read_with_include_paths: {:?}", opts.get_search_paths());
                if let Ok((filename, content)) =
                    opts.read_new_file(self.source_file.clone(), filename.to_string())
                {
                    (filename, content)
                } else {
                    return Err(EvalErr(allocator.null(), "Failed to read file".to_string()));
                }
            } else {
                let full_path = full_path_for_filename(parent_sexp, filename, &self.search_paths)?;
                // Use the filesystem like normal if the opts couldn't find
                // the file.
                eprintln!("try read file {}", full_path);
                let content = fs::read(&full_path)
                    .map_err(|_| EvalErr(allocator.null(), "Failed to read file".to_string()))?;
                (full_path, content)
            };

        Ok(PresentFile { data: content, full_path: full_path })
    }

    fn read(&self, allocator: &mut Allocator, sexp: NodePtr) -> Response {
        let First::Here(f) =
            First::Here(ThisNode::Here).select_nodes(allocator, sexp)?;
        match allocator.sexp(f) {
            SExp::Atom(b) => {
                let filename =
                    Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                let result = self.primitive_read_internal(allocator, sexp, &filename)?;
                read_ir(&decode_string(&result.data))
                    .map_err(|e| EvalErr(allocator.null(), e.to_string()))
                    .and_then(|ir| {
                        assemble_from_ir(allocator, Rc::new(ir)).map(|ir_sexp| Reduction(1, ir_sexp))
                    })
            }
            _ => Err(EvalErr(
                allocator.null(),
                "filename is not an atom".to_string(),
            )),
        }
    }

    /// Given an sexp representing an embedding preprocessor form of some kind such
    /// as (embed-file constant-name kind filename)
    /// or (compile-file constant-name filename)
    /// Return the resulting constant name and a quoted expression suitable for use
    /// as a constant or an error if the file wasn't found.
    fn embed(&self, allocator: &mut Allocator, embed_args: NodePtr) -> Response {
        let First::Here(declaration_sexp) =
            First::Here(ThisNode::Here).select_nodes(allocator, embed_args)?;
        eprintln!("embed declaration_sexp {}", disassemble(allocator, declaration_sexp));
        let rest_of_decl = rest(allocator, declaration_sexp)?;
        let (name_node, name, kind, filename) =
            if let Some(l) = proper_list(allocator, rest_of_decl, true) {
                if l.len() != 3 {
                    return Err(EvalErr(
                        declaration_sexp,
                        "must have a type and a name".to_string(),
                    ));
                }

                if let (SExp::Atom(name), SExp::Atom(kind), SExp::Atom(filename)) = (
                    allocator.sexp(l[0]),
                    allocator.sexp(l[1]),
                    allocator.sexp(l[2])
                ) {
                    (l[0], name, kind, filename)
                } else {
                    return Err(EvalErr(
                        declaration_sexp,
                        "malformed embed-file".to_string(),
                    ));
                }
            } else {
                return Err(EvalErr(
                    declaration_sexp,
                    "malformed embed-file".to_string(),
                ));
            };

        // Note: we don't want to keep borrowing here because we
        // need the mutable borrow below.
        let kind_buf = allocator.buf(&kind).to_vec();
        let filename_buf = allocator.buf(&filename).to_vec();
        let file = self.primitive_read_internal(
            allocator,
            declaration_sexp,
            &decode_string(&filename_buf),
        )?;

        // Include the file's contents in the constant pool.
        // The user can specify the format to read:
        //
        // bin
        // hex
        // sexp
        let processed_data =
            if kind_buf == b"bin" {
                allocator.new_atom(&file.data)?
            } else if kind_buf == b"hex" {
                convert_hex_to_sexp(allocator, &file.data)?
            } else if kind_buf == b"sexp" {
                assemble(allocator, &decode_string(&file.data))?
            } else {
                return Err(EvalErr(declaration_sexp, "no such embed kind".to_string()));
            };

        let result = allocator.new_pair(name_node, processed_data)?;
        Ok(Reduction(1, result))
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
        let convert_filename = |allocator: &mut Allocator, full_name: &String| {
            let converted_filename = allocator.new_atom(full_name.as_bytes())?;
            Ok(Reduction(1, converted_filename))
        };

        if let SExp::Pair(l, _r) = allocator.sexp(sexp) {
            if let SExp::Atom(b) = allocator.sexp(l) {
                let filename =
                    Bytes::new(Some(BytesFromType::Raw(allocator.buf(&b).to_vec()))).decode();
                eprintln!("try find file {}", filename);

                // If we have a compiler opts injected, let that handle reading
                // files.  The name will bubble up to the _read function.
                if self.get_compiler_opts().is_some() {
                    return convert_filename(allocator, &filename);
                }

                let full_name = full_path_for_filename(sexp, &filename, &self.search_paths)?;
                return convert_filename(allocator, &full_name);
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

    pub fn run_compiler(
        &self,
        allocator: &mut Allocator,
        sexp: NodePtr
    ) -> Result<Reduction, EvalErr> {
        eprintln!("in run_compiler {}", disassemble(allocator, sexp));
        let mut symtab = HashMap::new();
        let First::Here(NodeSel::Cons(compile_arg, First::Here(varname_arg))) =
            First::Here(NodeSel::Cons(ThisNode::Here, First::Here(ThisNode::Here))).select_nodes(allocator, sexp)?;
        eprintln!("compile_arg {}", disassemble(allocator, compile_arg));
        let name =
            if let SExp::Atom(b) = allocator.sexp(compile_arg) {
                allocator.buf(&b).to_vec()
            } else {
                return Err(EvalErr(sexp, "malformed _run_compiler arguments: bad filename".to_string()));
            };

        let varname =
            if let SExp::Atom(b) = allocator.sexp(varname_arg) {
                allocator.buf(&b).to_vec()
            } else {
                return Err(EvalErr(sexp, "malformed _run_compiler arguments: bad varname".to_string()));
            };

        eprintln!("name is {}", decode_string(&name));
        let file = self.primitive_read_internal(
            allocator,
            sexp,
            &decode_string(&name)
        )?;

        eprintln!("got content {}", decode_string(&file.data));
        let compiled_res = compile_clvm_text(
            allocator,
            self.get_compiler_opts().unwrap_or_else(|| {
                Rc::new(DefaultCompilerOpts::new(&self.source_file)).set_search_paths(&self.search_paths)
            }),
            &mut symtab,
            &decode_string(&file.data),
            &decode_string(&varname),
            self.get_compiler_opts().is_some(),
        );

        eprintln!("compiled_res {compiled_res:?}");

        let compiled = compiled_res?;

        eprintln!("got program {}", disassemble(allocator, compiled));

        // Write symbols for the compiled inner module.
        let target_symbols_name =
            make_symbols_name(&self.source_file, &decode_string(&varname));

        // Not a hard error if we can't write the symbols,
        // given the way most write chialisp.
        write_sym_output(&symtab, &target_symbols_name).ok();

        Ok(Reduction(1, compiled))
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
                if opbuf == "_embed".as_bytes() {
                    self.embed(allocator, sexp)
                } else if opbuf == "_read".as_bytes() {
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
                } else if opbuf == "_run_compiler".as_bytes() {
                    self.run_compiler(allocator, sexp)
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

    pub fn set_compiler_opts(&self, opts: Option<Rc<dyn CompilerOpts>>) {
        self.parent.set_compiler_opts(opts);
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
