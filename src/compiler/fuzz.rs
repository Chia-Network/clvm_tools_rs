use rand::prelude::*;
use std::rc::Rc;

pub trait FuzzTypeParams {
    type Tag: Eq + Clone;
    type Expr: Eq + Clone + ExprModifier<Item = Self::Expr, Tag = Self::Tag>;
    type Error: for<'a> From<&'a str>;
    type State;
}

#[derive(Clone, Debug)]
pub struct FuzzChoice<Item, Tag> {
    pub tag: Tag,
    pub atom: Item,
}

pub trait ExprModifier {
    type Tag;
    type Item;

    /// Add identified in-progress expansions into waiters.
    fn find_waiters(&self, waiters: &mut Vec<FuzzChoice<Self::Item, Self::Tag>>);

    /// Replace a value where it appears in the structure with a new value.
    fn replace_node(&self, to_replace: &Self::Item, new_value: Self::Item) -> Self::Item;

    /// Find the expression in the target structure and give the path down to it
    /// expressed as a snapshot of the traversed nodes.
    fn find_in_structure(&self, target: &Self::Item) -> Option<Vec<Self::Item>>;
}

pub trait Rule<FT: FuzzTypeParams> {
    fn check(
        &self,
        state: &mut FT::State,
        tag: &FT::Tag,
        idx: usize,
        terminate: bool,
        parents: &[FT::Expr],
    ) -> Result<Option<FT::Expr>, FT::Error>;
}

pub struct FuzzGenerator<FT: FuzzTypeParams> {
    idx: usize,
    structure: FT::Expr,
    waiting: Vec<FuzzChoice<FT::Expr, FT::Tag>>,
    rules: Vec<Rc<dyn Rule<FT>>>,
}

impl<FT: FuzzTypeParams> FuzzGenerator<FT> {
    pub fn new(node: FT::Expr, rules: &[Rc<dyn Rule<FT>>]) -> Self {
        let mut waiting = Vec::new();
        node.find_waiters(&mut waiting);
        FuzzGenerator {
            idx: 1,
            structure: node,
            waiting,
            rules: rules.to_vec(),
        }
    }

    pub fn result(&self) -> &FT::Expr {
        &self.structure
    }

    fn remove_waiting(&mut self, waiting_atom: &FT::Expr) -> Result<(), FT::Error> {
        let to_remove_waiting: Vec<usize> = self
            .waiting
            .iter()
            .enumerate()
            .filter_map(|(i, w)| {
                if w.atom == *waiting_atom {
                    Some(i)
                } else {
                    None
                }
            })
            .collect();

        if to_remove_waiting.is_empty() {
            return Err("remove_waiting must succeed".into());
        }

        self.waiting.remove(to_remove_waiting[0]);
        Ok(())
    }

    pub fn expand<R: Rng + Sized>(
        &mut self,
        state: &mut FT::State,
        terminate: bool,
        rng: &mut R,
    ) -> Result<bool, FT::Error> {
        let mut waiting = self.waiting.clone();

        while !waiting.is_empty() {
            let mut rules = self.rules.clone();
            let waiting_choice: usize = rng.gen::<usize>() % waiting.len();

            let chosen = waiting[waiting_choice].clone();
            waiting.remove(waiting_choice);

            let heritage = if let Some(heritage) = self.structure.find_in_structure(&chosen.atom) {
                heritage
            } else {
                return Err("Parity wasn't kept between the structure and waiting list".into());
            };

            while !rules.is_empty() {
                let rule_choice: usize = rng.gen::<usize>() % rules.len();
                let chosen_rule = rules[rule_choice].clone();
                rules.remove(rule_choice);

                if let Some(res) =
                    chosen_rule.check(state, &chosen.tag, self.idx, terminate, &heritage)?
                {
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
