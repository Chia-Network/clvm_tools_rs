extern crate clvmr as clvm_rs;

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;

use crate::compiler::clvm::sha256tree;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, CompilerOpts};
use crate::compiler::evaluate::Evaluator;
use crate::compiler::sexp::SExp;
use crate::util::u8_from_number;

// We consider lower case atoms as uncurried by convention.
fn consider_as_uncurried(v: &Vec<u8>) -> bool {
    v.len() > 0 && v[0] >= b'a' && v[0] <= b'z'
}

fn produce_env_captures(
    envmap: &mut HashMap<Vec<u8>, Rc<BodyForm>>,
    envlist: &mut HashMap<Vec<u8>, Vec<u8>>,
    base_name: Vec<u8>,
    args: Rc<SExp>,
) {
    match args.borrow() {
        SExp::Cons(_, a, b) => {
            produce_env_captures(envmap, envlist, base_name.clone(), a.clone());
            produce_env_captures(envmap, envlist, base_name, b.clone());
        }
        SExp::Atom(l, a) => {
            let mut new_name = a.clone();
            new_name.append(&mut "_$_".as_bytes().to_vec());
            new_name.append(&mut base_name.clone());
            envmap.insert(
                a.clone(),
                Rc::new(BodyForm::Value(SExp::Atom(l.clone(), new_name.clone()))),
            );
            envlist.insert(new_name, a.clone());
        }
        _ => {}
    }
}

fn remove_present_atoms(envlist: &mut HashMap<Vec<u8>, Vec<u8>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Cons(_, a, b) => {
            remove_present_atoms(envlist, a.clone());
            remove_present_atoms(envlist, b.clone());
        }
        SExp::Atom(_, b) => {
            envlist.remove(b);
        }
        // Appearing in the output, all atom types are equivalent.
        SExp::QuotedString(_, _, b) => {
            envlist.remove(b);
        }
        SExp::Integer(_, i) => {
            envlist.remove(&u8_from_number(i.clone()));
        }
        _ => {}
    }
}

pub fn check_parameters_used_compileform(
    opts: Rc<dyn CompilerOpts>,
    program: Rc<CompileForm>,
) -> Result<HashSet<Vec<u8>>, CompileErr> {
    let mut allocator = Allocator::new();
    let mut env = HashMap::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let mut replacement_to_original = HashMap::new();
    let base_name = Bytes::new(Some(BytesFromType::Raw(sha256tree(program.to_sexp()))))
        .hex()
        .as_bytes()
        .to_vec();
    let e = Evaluator::new(opts.clone(), runner.clone(), program.helpers.clone()).mash_conditions();

    produce_env_captures(
        &mut env,
        &mut replacement_to_original,
        base_name,
        program.args.clone(),
    );

    let result = e.shrink_bodyform(
        &mut allocator,
        program.args.clone(),
        &env,
        program.exp.clone(),
        false,
    )?;

    remove_present_atoms(&mut replacement_to_original, result.to_sexp());

    let mut result_set = HashSet::new();
    for kv in replacement_to_original.iter() {
        if consider_as_uncurried(kv.0) {
            result_set.insert(kv.1.clone());
        }
    }
    Ok(result_set)
}
