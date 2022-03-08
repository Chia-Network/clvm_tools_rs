#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate indoc;

#[macro_use]
extern crate do_notation;

#[macro_use]
#[cfg(not(any(test, target_family = "wasm")))]
extern crate pyo3;

extern crate tempfile;

mod util;

pub mod classic;
pub mod compiler;

// Python impl
#[cfg(not(any(test, target_family = "wasm")))]
mod py;

#[cfg(test)]
mod tests;

#[cfg(target_family = "wasm")]
pub mod wasm;
