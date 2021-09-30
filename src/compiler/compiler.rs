use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType
};
use crate::compiler::comptypes::{
    CompileErr,
    CompilerOpts
};
use crate::compiler::sexp::{
    SExp,
    parse_sexp
};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::frontend::frontend;
use crate::compiler::codegen::codegen;

pub fn compile_file(
    opts: Rc<dyn CompilerOpts>,
    content: String
) -> Result<String, CompileErr> {
    let pre_forms =
        parse_sexp(Srcloc::start(&opts.filename()), &content).map_err(|e| {
            CompileErr(e.0, e.1)
        })?;

    frontend(opts.clone(), pre_forms).
        and_then(|g| codegen(opts.clone(), &g)).
        map(|result| {
            if opts.assemble() {
                Bytes::new(Some(BytesFromType::Raw(result.encode()))).hex()
            } else {
                result.to_string()
            }
        })
}
