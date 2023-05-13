use std::rc::Rc;

use clvmr::allocator::{Allocator, NodePtr, SExp};
use clvmr::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{Bytes, Stream, UnvalidatedBytesFromType};
use crate::classic::clvm::serialize::{sexp_from_stream, SimpleCreateCLVMObject};
use crate::classic::clvm::sexp::{enlist, NodeSel, SelectNode, ThisNode};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::sexp::decode_string;

/// An object that represents file contents that were found when fulfilling a
/// form that requested some data be embedded at compile time in this program.
pub struct PresentFile {
    pub data: Vec<u8>,
    pub full_path: String,
}

/// Given u8 data from a hex file, build an sexp from it.
/// This is used for the compile-file and embed-file feature.
pub fn convert_hex_to_sexp(
    allocator: &mut Allocator,
    file_data: &[u8],
) -> Result<NodePtr, EvalErr> {
    let content_bytes = Bytes::new_validated(Some(UnvalidatedBytesFromType::Hex(decode_string(
        file_data,
    ))))
    .map_err(|e| EvalErr(allocator.null(), e.to_string()))?;
    let mut reader_stream = Stream::new(Some(content_bytes));
    Ok(sexp_from_stream(
        allocator,
        &mut reader_stream,
        Box::new(SimpleCreateCLVMObject {}),
    )?
    .1)
}

/// Given an sexp representing an embedding preprocessor form of some kind such
/// as (embed-file constant-name kind filename)
/// or (compile-file constant-name filename)
/// Return the resulting constant name and a quoted expression suitable for use
/// as a constant or an error if the file wasn't found.
pub fn process_embed_file(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    declaration_sexp: NodePtr,
) -> Result<(Vec<u8>, NodePtr), EvalErr> {
    let command_name = allocator.new_atom(b"_embed")?;
    let env_atom = allocator.new_atom(&[1])?;
    let command = enlist(allocator, &[command_name, env_atom])?;

    let result = runner
        .run_program(allocator, command, declaration_sexp, None)?
        .1;

    let NodeSel::Cons(name, content) =
        NodeSel::Cons(ThisNode::Here, ThisNode::Here).select_nodes(allocator, result)?;
    if let SExp::Atom(name_buf) = allocator.sexp(name) {
        Ok((allocator.buf(&name_buf).to_vec(), content))
    } else {
        Err(EvalErr(
            declaration_sexp,
            "Wrong result from embed primitive".to_string(),
        ))
    }
}
