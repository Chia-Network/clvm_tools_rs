extern crate clvmr as clvm_rs;
use rand::prelude::*;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use base64::{engine::general_purpose, Engine as _};

use std::borrow::Borrow;

use std::rc::Rc;

use clvm_tools_rs::compiler::fuzzer::CollectProgramStructure;
use clvm_tools_rs::compiler::sexp::SExp;
use clvm_tools_rs::compiler::srcloc::Srcloc;

use clvm_tools_rs::fuzzing::fuzzrng::FuzzPseudoRng;
use clvm_tools_rs::fuzzing::make_random_u64_seed;

fn do_program(dialect: Rc<SExp>, buf: &[u8]) -> Rc<SExp> {
    let mut fpr = FuzzPseudoRng::new(buf);
    let mut cps: CollectProgramStructure = fpr.gen();
    let program = cps.to_program();
    let pt = program.to_sexp();
    if let SExp::Cons(_, args, body) = pt.borrow() {
        let include_directive = Rc::new(SExp::Cons(
            pt.loc(),
            Rc::new(SExp::atom_from_string(pt.loc(), "include")),
            Rc::new(SExp::Cons(pt.loc(), dialect, Rc::new(SExp::Nil(pt.loc())))),
        ));
        Rc::new(SExp::Cons(
            pt.loc(),
            Rc::new(SExp::atom_from_string(pt.loc(), "mod")),
            Rc::new(SExp::Cons(
                pt.loc(),
                args.clone(),
                Rc::new(SExp::Cons(pt.loc(), include_directive, body.clone())),
            )),
        ))
    } else {
        pt
    }
}

fn write_prog_to_db(db: &mut sqlite::Connection, buf: &[u8], sexp: Rc<SExp>) {
    let pts = sexp.to_string();
    let encoded: String = general_purpose::STANDARD.encode(buf);
    let mut stmt = db
        .prepare("insert or ignore into programs (b, t) values (?, ?)")
        .expect("should work");
    let binds: &[sqlite::Value] = &[sqlite::Value::String(encoded), sqlite::Value::String(pts)];
    stmt.bind(binds).unwrap();
    stmt.next().expect("should work");
}

fn main() {
    let mut rng = ChaCha8Rng::seed_from_u64(make_random_u64_seed());
    let mut buf = vec![0, 0, 0, 0];

    let mut conn = sqlite::open("prog.db").expect("db");

    if conn
        .execute("create table if not exists programs (b text primary key, t text)")
        .is_err()
    {
        eprintln!("failed to create db");
        return;
    }

    let loc = Srcloc::start("*rng*");
    let dialect = Rc::new(SExp::atom_from_string(loc, "*standard-cl-21*"));

    let sexp = do_program(dialect.clone(), &buf);
    write_prog_to_db(&mut conn, &buf, sexp);

    for _ in 0..10000 {
        // Read a random row.
        {
            let mut stmt = conn
                .prepare("SELECT b as b FROM programs ORDER BY RANDOM() LIMIT 1;")
                .expect("should have selectable stuff");

            if let Ok(sqlite::State::Row) = stmt.next() {
                let this_buf_repr = stmt
                    .read::<String, _>("b")
                    .expect("should have the right column");
                buf = general_purpose::STANDARD
                    .decode(this_buf_repr)
                    .expect("should exist");
            }
        }

        let next_byte = rng.gen_range(0..=buf.len());
        if next_byte >= buf.len() - 3 {
            for _ in 0..4 {
                buf.push(rng.gen());
            }
        } else {
            for i in 0..4 {
                buf[next_byte + i] ^= rng.gen::<u8>();
            }
        }
        let sexp = do_program(dialect.clone(), &buf);
        eprintln!("{}", sexp);
        write_prog_to_db(&mut conn, &buf, sexp);
    }
}
