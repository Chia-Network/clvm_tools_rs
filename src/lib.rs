#![feature(in_band_lifetimes)]

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

mod util;

pub mod classic;
pub mod compiler;

#[cfg(test)]
mod tests;
