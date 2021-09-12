use clvm_rs::allocator::{
    Allocator,
    NodePtr
};
use crate::classic::clvm_tools::binutils::assemble;

pub mod stage_0;
pub mod stage_1;
pub mod stage_2;

pub fn run<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(a (opt (com 2)) 3)".to_string()
    ).unwrap();
}

pub fn brun<'a>(allocator: &'a mut Allocator) -> NodePtr {
    return assemble(
        allocator,
        &"(a 2 3)".to_string()
    ).unwrap();
}
