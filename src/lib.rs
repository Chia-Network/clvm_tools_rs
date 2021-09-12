#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate indoc;

#[macro_use]
extern crate do_notation;

mod util;

pub mod classic;
pub mod compiler;

#[cfg(test)]
mod tests;
