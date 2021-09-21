#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate indoc;

#[macro_use]
extern crate do_notation;

#[macro_use]
extern crate serde_json;

#[macro_use]
extern crate pyo3;

mod util;

pub mod classic;
pub mod compiler;

// Python impl
mod py;

#[cfg(test)]
mod tests;
