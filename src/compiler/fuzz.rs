use rand::prelude::*;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct FuzzChoice<Expr> {
    pub tag: Vec<u8>,
    pub atom: Expr,
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

pub trait Rule<State,Expr,Error> {
    fn check(&self, state: &mut State, tag: &[u8], idx: usize, terminate: bool, parents: &[Expr]) -> Result<Option<Expr>, Error>;
}

pub struct FuzzGenerator<State,Expr,Error: for<'a> From<&'a str>> {
    idx: usize,
    structure: Expr,
    waiting: Vec<FuzzChoice<Expr>>,
    rules: Vec<Rc<dyn Rule<State,Expr,Error>>>,
}

impl<State,Expr,Error: for<'a> From<&'a str>> FuzzGenerator<State,Expr,Error>
where
    Expr: Eq + Clone + ExprModifier<Item = Expr>
{
    pub fn new(node: Expr, rules: &[Rc<dyn Rule<State,Expr,Error>>]) -> Self {
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

    fn remove_waiting(&mut self, waiting_atom: &Expr) -> Result<(), Error> {
        let mut to_remove_waiting: Vec<usize> = self.waiting.iter().enumerate().filter_map(|(i,w)| {
            if w.atom == *waiting_atom {
                Some(i)
            } else {
                None
            }
        }).collect();

        if to_remove_waiting.is_empty() {
            return Err("remove_waiting must succeed".into());
        }

        self.waiting.remove(to_remove_waiting[0]);
        Ok(())
    }

    pub fn expand<R: Rng + Sized>(&mut self, state: &mut State, terminate: bool, rng: &mut R) -> Result<bool, Error> {
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
                    return Err("Parity wasn't kept between the structure and waiting list".into());
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
                )? {
                    let mut new_waiters = Vec::new();
                    res.find_waiters(&mut new_waiters);
                    for n in new_waiters.into_iter() {
                        self.idx += 1;
                        self.waiting.push(n);
                    }

                    self.remove_waiting(&chosen.atom)?;
                    self.structure = self.structure.replace_node(&chosen.atom, res);
                    return Ok(!self.waiting.is_empty());
                }
            }
        }

        Err("rule deadlock".into())
    }
}
