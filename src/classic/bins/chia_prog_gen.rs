extern crate clvmr as clvm_rs;
use rand_chacha::ChaCha8Rng;
use rand::prelude::*;
use rand::SeedableRng;

use std::borrow::Borrow;
use std::collections::HashSet;
use std::io::{self, BufRead, Write};

use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use clvm_tools_rs::compiler::compiler::DefaultCompilerOpts;
#[cfg(feature="fuzzer")]
use clvm_tools_rs::compiler::fuzzer::CollectProgramStructure;
use clvm_tools_rs::compiler::repl::Repl;
use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

use clvm_tools_rs::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
#[cfg(feature="fuzzer")]
use clvm_tools_rs::fuzzing::make_random_u64_seed;
#[cfg(feature="fuzzer")]
use clvm_tools_rs::fuzzing::fuzzrng::FuzzPseudoRng;

#[cfg(feature="fuzzer")]
fn do_program(programs: &mut Vec<Vec<u8>>, unique: &mut HashSet<String>, dialect: Rc<SExp>, buf: &[u8]) {
    let mut fpr = FuzzPseudoRng::new(&buf);
    let mut cps: CollectProgramStructure = fpr.gen();
    let program = cps.to_program();
    let pt = program.to_sexp();
    let pts = program.to_sexp().to_string();
    if !unique.contains(&pts) {
        if let SExp::Cons(_,args,body) = pt.borrow() {
            let include_directive = Rc::new(SExp::Cons(
                pt.loc(),
                Rc::new(SExp::atom_from_string(pt.loc(), "include")),
                Rc::new(SExp::Cons(
                    pt.loc(),
                    dialect,
                    Rc::new(SExp::Nil(pt.loc()))
                ))
            ));
            let new_mod = SExp::Cons(
                pt.loc(),
                Rc::new(SExp::atom_from_string(pt.loc(), "mod")),
                Rc::new(SExp::Cons(
                    pt.loc(),
                    args.clone(),
                    Rc::new(SExp::Cons(
                        pt.loc(),
                        include_directive,
                        body.clone()
                    ))
                ))
            );
            println!("{}", new_mod);
            programs.push(buf.to_vec());
            unique.insert(pts);
        }
    }
}

#[cfg(feature="fuzzer")]
fn main() {
    let mut rng = ChaCha8Rng::seed_from_u64(make_random_u64_seed());
    let mut buf = &[0,0,0,0];
    let this_len = buf.len();
    let mut programs = Vec::new();
    let mut unique = HashSet::new();
    let loc = Srcloc::start("*rng*");
    let dialect = Rc::new(SExp::atom_from_string(loc, "*standard-cl-21*"));
    do_program(&mut programs, &mut unique, dialect.clone(), buf);
    for p in 0..200000 {
        let choice = rng.gen_range(0..programs.len());
        let mut this_buf = programs[choice].to_vec();
        let mut next_byte = rng.gen_range(0..=buf.len());
        if next_byte >= buf.len() - 3 {
            for i in 0..4 {
                this_buf.push(rng.gen());
            }
        } else {
            for i in 0..4 {
                let next_bit = rng.gen_range(0..8);
                this_buf[next_byte + i] ^= rng.gen::<u8>();
            }
        }
        do_program(&mut programs, &mut unique, dialect.clone(), &this_buf);
    }
}

#[cfg(not(feature="fuzzer"))]
fn main() {
}
