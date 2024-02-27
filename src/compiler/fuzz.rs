use num_bigint::ToBigInt;
use rand::prelude::*;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

pub trait Rule<S> {
    fn check(&self, state: &mut S, tag: &[u8], idx: usize, terminate: bool, parents: &[Rc<SExp>]) -> Option<Rc<SExp>>;
}

#[derive(Clone, Debug)]
struct FuzzChoice {
    tag: Vec<u8>,
    atom: Rc<SExp>,
}

pub struct FuzzGenerator<S> {
    idx: usize,
    structure: Rc<SExp>,
    waiting: Vec<FuzzChoice>,
    rules: Vec<Rc<dyn Rule<S>>>,
}

fn find_in_structure_inner(
    parents: &mut Vec<Rc<SExp>>,
    structure: Rc<SExp>,
    target: Rc<SExp>,
    mask: Number,
    parent: Number,
) -> Option<Number> {
    let this_path = mask.clone() | parent.clone();

    if let SExp::Cons(_, a, b) = structure.borrow() {
        let next_mask = mask * 2_u32.to_bigint().unwrap();

        parents.push(structure.clone());
        if let Some(path) = find_in_structure_inner(
            parents,
            a.clone(),
            target.clone(),
            next_mask.clone(),
            parent.clone()
        ) {
            return Some(this_path);
        }
        if let Some(path) = find_in_structure_inner(
            parents,
            b.clone(),
            target.clone(),
            next_mask.clone(),
            this_path.clone(),
        ) {
            return Some(this_path);
        }

        parents.pop();
    }

    if structure == target {
        return Some(this_path);
    }

    None
}

fn find_in_structure(
    structure: Rc<SExp>,
    target: Rc<SExp>,
    mask: Number,
    parent: Number,
) -> Option<(Number, Vec<Rc<SExp>>)> {
    let mut parents = Vec::new();
    find_in_structure_inner(
        &mut parents,
        structure,
        target,
        mask,
        parent
    ).map(|path| {
        (path, parents)
    })
}

fn find_waiters(
    waiters: &mut Vec<FuzzChoice>,
    structure: Rc<SExp>,
) {
    match structure.borrow() {
        SExp::Cons(_, a, b) => {
            find_waiters(waiters, a.clone());
            find_waiters(waiters, b.clone());
        }
        SExp::Atom(_, a) => {
            if a.starts_with(b"${") && a.ends_with(b"}") {
                let mut found_colon = a.iter().enumerate().filter_map(|(i,c)| if *c == b':' { Some(i) } else { None });
                if let Some(c_idx) = found_colon.next() {
                    let tag_str: Vec<u8> = a.iter().take(a.len() - 1).skip(c_idx + 1).copied().collect();
                    waiters.push(FuzzChoice {
                        tag: tag_str,
                        atom: structure.clone()
                    });
                }
            }
        }
        _ => {}
    }
}

fn replace_node(
    structure: Rc<SExp>,
    to_replace: Rc<SExp>,
    new_value: Rc<SExp>
) -> Rc<SExp> {
    if let SExp::Cons(l, a, b) = structure.borrow() {
        let new_a = replace_node(a.clone(), to_replace.clone(), new_value.clone());
        let new_b = replace_node(b.clone(), to_replace.clone(), new_value.clone());
        if Rc::as_ptr(&new_a) != Rc::as_ptr(a) || Rc::as_ptr(&new_b) != Rc::as_ptr(b) {
            return Rc::new(SExp::Cons(l.clone(), new_a, new_b));
        }
    }

    if structure == to_replace {
        return new_value;
    }

    structure
}

impl<S> FuzzGenerator<S> {
    pub fn new(rules: &[Rc<dyn Rule<S>>]) -> Self {
        let srcloc = Srcloc::start("*fuzz*");
        let node = Rc::new(SExp::Atom(srcloc.clone(), b"${0:top}".to_vec()));
        FuzzGenerator {
            idx: 1,
            structure: node.clone(),
            waiting: vec![FuzzChoice {
                tag: b"top".to_vec(),
                atom: node,
            }],
            rules: rules.to_vec()
        }
    }

    pub fn result(&self) -> Rc<SExp> { self.structure.clone() }

    fn remove_waiting(&mut self, waiting_atom: Rc<SExp>) {
        let mut to_remove_waiting: Vec<usize> = self.waiting.iter().enumerate().filter_map(|(i,w)| {
            if w.atom == waiting_atom {
                Some(i)
            } else {
                None
            }
        }).collect();

        if to_remove_waiting.is_empty() {
            panic!("remove_waiting must succeed");
        }

        self.waiting.remove(to_remove_waiting[0]);
    }

    pub fn expand<R: Rng + Sized>(&mut self, state: &mut S, terminate: bool, rng: &mut R) -> Result<bool, ()> {
        let waiting_nodes: Vec<String> = self.waiting.iter().map(|h| h.atom.to_string()).collect();
        eprintln!("expand {} waiting {waiting_nodes:?}", self.structure);
        let mut waiting = self.waiting.clone();

        while !waiting.is_empty() {
            let mut rules = self.rules.clone();
            let waiting_choice: usize = rng.gen::<usize>() % waiting.len();

            let chosen = waiting[waiting_choice].clone();
            waiting.remove(waiting_choice);

            let heritage =
                if let Some((_, heritage)) = find_in_structure(self.structure.clone(), chosen.atom.clone(), bi_one(), bi_zero()) {
                    heritage
                } else {
                    // XXX if the atom isn't in the structure, something very wierd
                    // happened, because we got this from there.
                    continue;
                };

            while !rules.is_empty() {
                let rule_choice: usize = rng.gen::<usize>() % rules.len();
                let chosen_rule = rules[rule_choice].clone();
                rules.remove(rule_choice);

                if let Some(res) = chosen_rule.check(
                    state,
                    &chosen.tag,
                    self.idx,
                    terminate,
                    &heritage
                ) {
                    let mut new_waiters = Vec::new();
                    find_waiters(&mut new_waiters, res.clone());
                    for n in new_waiters.into_iter() {
                        self.idx += 1;
                        self.waiting.push(n);
                    }

                    self.remove_waiting(chosen.atom.clone());
                    self.structure = replace_node(self.structure.clone(), chosen.atom.clone(), res);
                    return Ok(!self.waiting.is_empty());
                }
            }
        }

        Err(())
    }
}
