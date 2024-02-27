use num_bigint::ToBigInt;
use rand::prelude::*;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

#[derive(Clone, Debug)]
struct FuzzChoice<Expr> {
    tag: Vec<u8>,
    atom: Expr,
}

pub trait ExprModifier {
    type Item;

    /// Add identified in-progress expansions into waiters.
    fn find_waiters(&self, waiters: &mut Vec<FuzzChoice<Self::Item>>);

    /// Replace a value where it appears in the structure with a new value.
    fn replace_node(&self, to_replace: &Self::Item, new_value: Self::Item) -> Self::Item;

    /// Find the expression in the target structure and give the path down to it
    /// expressed as a snapshot of the traversed nodes.
    fn find_in_structure(&self, target: &Self::Item) -> Option<Vec<Self::Item>>;
}

fn find_in_structure_inner(
    parents: &mut Vec<Rc<SExp>>,
    structure: Rc<SExp>,
    target: &Rc<SExp>,
) -> bool {
    if let SExp::Cons(_, a, b) = structure.borrow() {
        parents.push(structure.clone());
        if find_in_structure_inner(
            parents,
            a.clone(),
            target,
        ) {
            return true;
        }
        if find_in_structure_inner(
            parents,
            b.clone(),
            target,
        ) {
            return true;
        }

        parents.pop();
    }

    structure == *target
}

impl ExprModifier for Rc<SExp> {
    type Item = Self;
    fn find_waiters(
        &self,
        waiters: &mut Vec<FuzzChoice<Self::Item>>,
    ) {
        match self.borrow() {
            SExp::Cons(_, a, b) => {
                a.find_waiters(waiters);
                b.find_waiters(waiters);
            }
            SExp::Atom(_, a) => {
                if a.starts_with(b"${") && a.ends_with(b"}") {
                    let mut found_colon = a.iter().enumerate().filter_map(|(i,c)| if *c == b':' { Some(i) } else { None });
                    if let Some(c_idx) = found_colon.next() {
                        let tag_str: Vec<u8> = a.iter().take(a.len() - 1).skip(c_idx + 1).copied().collect();
                        waiters.push(FuzzChoice {
                            tag: tag_str,
                            atom: self.clone()
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn replace_node(
        &self,
        to_replace: &Self::Item,
        new_value: Self::Item,
    ) -> Self::Item {
        if let SExp::Cons(l, a, b) = self.borrow() {
            let new_a = a.replace_node(to_replace, new_value.clone());
            let new_b = b.replace_node(to_replace, new_value.clone());
            if Rc::as_ptr(&new_a) != Rc::as_ptr(a) || Rc::as_ptr(&new_b) != Rc::as_ptr(b) {
                return Rc::new(SExp::Cons(l.clone(), new_a, new_b));
            }
        }

        if self == to_replace {
            return new_value;
        }

        self.clone()
    }

    fn find_in_structure(
        &self,
        target: &Self::Item,
    ) -> Option<Vec<Self::Item>> {
        let mut parents = Vec::new();
        if find_in_structure_inner(
            &mut parents,
            self.clone(),
            target,
        ) {
            Some(parents)
        } else {
            None
        }
    }
}

pub trait Rule<State,Expr> {
    fn check(&self, state: &mut State, tag: &[u8], idx: usize, terminate: bool, parents: &[Expr]) -> Option<Expr>;
}

pub struct FuzzGenerator<State,Expr> {
    idx: usize,
    structure: Expr,
    waiting: Vec<FuzzChoice<Expr>>,
    rules: Vec<Rc<dyn Rule<State,Expr>>>,
}

impl<State,Expr> FuzzGenerator<State,Expr>
where
    Expr: Eq + Clone + ExprModifier<Item = Expr>
{
    pub fn new(node: Expr, rules: &[Rc<dyn Rule<State,Expr>>]) -> Self {
        let srcloc = Srcloc::start("*fuzz*");
        FuzzGenerator {
            idx: 1,
            structure: node.clone(),
            waiting: vec![FuzzChoice {
                tag: b"top".to_vec(),
                atom: node,
            }],
            rules: rules.to_vec(),
        }
    }

    pub fn result(&self) -> Expr { self.structure.clone() }

    fn remove_waiting(&mut self, waiting_atom: &Expr) {
        let mut to_remove_waiting: Vec<usize> = self.waiting.iter().enumerate().filter_map(|(i,w)| {
            if w.atom == *waiting_atom {
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

    pub fn expand<R: Rng + Sized>(&mut self, state: &mut State, terminate: bool, rng: &mut R) -> Result<bool, ()> {
        let mut waiting = self.waiting.clone();

        while !waiting.is_empty() {
            let mut rules = self.rules.clone();
            let waiting_choice: usize = rng.gen::<usize>() % waiting.len();

            let chosen = waiting[waiting_choice].clone();
            waiting.remove(waiting_choice);

            let heritage =
                if let Some(heritage) = self.structure.find_in_structure(&chosen.atom) {
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
                    res.find_waiters(&mut new_waiters);
                    for n in new_waiters.into_iter() {
                        self.idx += 1;
                        self.waiting.push(n);
                    }

                    self.remove_waiting(&chosen.atom);
                    self.structure = self.structure.replace_node(&chosen.atom, res);
                    return Ok(!self.waiting.is_empty());
                }
            }
        }

        Err(())
    }
}
