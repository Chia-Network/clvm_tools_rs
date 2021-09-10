use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use crate::classic::clvm_tools::binutils::assemble;

pub fn run<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(a (opt (com 2)) 3)".to_string()
    ).unwrap();
}
// export const brun = binutils.assemble("(a 2 3)");
