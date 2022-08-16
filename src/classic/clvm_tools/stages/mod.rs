use crate::classic::clvm_tools::binutils::assemble;
use clvm_rs::allocator::{Allocator, NodePtr};

pub mod stage_0;
pub mod stage_1;
pub mod stage_2;

pub fn run(allocator: &mut Allocator) -> NodePtr {
    assemble(allocator, "(a (opt (com 2)) 3)").unwrap()
}

pub fn brun(allocator: &mut Allocator) -> NodePtr {
    assemble(allocator, "(a 2 3)").unwrap()
}
