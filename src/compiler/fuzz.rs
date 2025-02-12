use rand::prelude::*;
use std::rc::Rc;

/// A trait that conveys the types of various things needed by this kind of fuzz
/// generation.
///
/// Tag is the type of step identifiers used during expansion.  Each node in the
/// generic tree this generator creates is either concrete or contains a tag and
/// an index which gives it a unique value.
///
/// Expr is the type of value being generated in this fuzz tree, and what will
/// ultimately result from generation.  It must be able to contain a value that
/// is recognizable as containing a Tag and index or something that has been
/// fully generated and needs nothing else.
///
/// Error is the type of error that can be throw while generating an Expr tree.
/// It should be str convertible so we can add context.
///
/// State is the mutable part of expression generation where needed context is
/// held.  All rules will receive a mutable State reference to record information
/// about what they're doing so it can be referred to later during expression
/// generation or after.
///
/// As an example of State use, imagine that this fuzzer is creating an arithmetic
/// expression.  State might remember the names of randomly generated variables in
/// an expression so that they can be given values when the expression is used, or
/// separately remember what operations are being applied so a test can
/// calculate the expected result on its own before trying something that evaluates
/// the expression separately so some other process of evaluation can be checked.
pub trait FuzzTypeParams {
    type Tag: Eq + Clone;
    type Expr: Eq + Clone + ExprModifier<Expr = Self::Expr, Tag = Self::Tag>;
    type Error: for<'a> From<&'a str>;
    type State;
}

#[derive(Clone, Debug)]
/// Specifies to the fuzz engine an unfinished node from an expression tree.  The
/// actual way this is represented in the tree type is situational so this type
/// allows the user to determine that.  Expr will be an Expr from FuzzTypeParams
/// and Tag will be a Tag from FuzzTypeParams.
pub struct FuzzChoice<Expr, Tag> {
    pub tag: Tag,
    pub atom: Expr,
}

/// This trait is provided for a specific Expr type that can be generated by this
/// fuzz system.  These methods allow the system to search a generated expression
/// for incomplete nodes, specify a replacement generated by a rule and capture the
/// path to a node to be given to the rules during generation.
pub trait ExprModifier {
    type Tag;
    type Expr;

    /// Add identified in-progress expansions into waiters.
    /// These are used as expansion candidates during each step of generation.
    /// Each will be tried in a random order with all rules in a random order until
    /// one of the rules returns a replacement.
    fn find_waiters(&self, waiters: &mut Vec<FuzzChoice<Self::Expr, Self::Tag>>);

    /// Replace a value where it appears in the structure with a new value.
    fn replace_node(&self, to_replace: &Self::Expr, new_value: Self::Expr) -> Self::Expr;

    /// Find the expression in the target structure and give the path down to it
    /// expressed as a snapshot of the traversed nodes.
    fn find_in_structure(&self, target: &Self::Expr) -> Option<Vec<Self::Expr>>;
}

/// This is the main active part the user provides for this system.  Each rule is
/// given a chance to provide a replacement for some incomplete part of the
/// expression tree.  The replacement can itself contain incomplete parts which
/// will be evaluated later, thus rules can be modular, recognizing some tag and
/// generating a partial expansion which can then be completed by some combination
/// of other rule evaluations.
///
/// State is a mutable reference to a common state shared by the rules to
/// accumulate information about the result expression.
///
/// Terminate is set by the user after some target complexity or number of
/// iterations is passed.  Rules should respond to terminate by generating the
/// smallest possible expansion or refusing expansion if some other rule provides
/// a smaller alternative.
///
/// Parents is a list which provides in order the Expr nodes which are one step
/// closer to the root than the last (with the implied last one being the one
/// containing Tag).
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

/// The fuzz generator object.  It can be stepped to generate an Expr according to
/// a given set of Rules.  It uses the methods of the ExprModifier trait carried
/// by the Expr type to obtain the incomplete nodes, determine the path to each,
/// and replace them with the nodes given by rules when those rules choose to
/// provide them.  It starts with a single incomplete node and generates a tree
/// of complete nodes.
pub struct FuzzGenerator<FT: FuzzTypeParams> {
    idx: usize,
    structure: FT::Expr,
    waiting: Vec<FuzzChoice<FT::Expr, FT::Tag>>,
    rules: Vec<Rc<dyn Rule<FT>>>,
}

impl<FT: FuzzTypeParams> FuzzGenerator<FT> {
    /// Given a possibly incomplete root Expr node and a set of Rules, initialize
    /// a fuzzer so we can step it until it completes or we decide to stop.
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

    /// Get the current Expr tree even if it contains incomplete nodes.
    pub fn result(&self) -> &FT::Expr {
        &self.structure
    }

    fn remove_waiting(&mut self, waiting_atom: &FT::Expr) -> Result<(), FT::Error> {
        if let Some(pos) = self.waiting.iter().position(|w| w.atom == *waiting_atom) {
            self.waiting.remove(pos);
            Ok(())
        } else {
            Err("remove_waiting must succeed".into())
        }
    }

    /// Perform one step of expansion of the Expr tree, updating State.
    /// The result will be Ok(true) if the tree is complete, Ok(false) if expansion
    /// succeeded but wasn't complete, or Error if something failed.
    ///
    /// Give terminate if the result() Expr has sufficient complexity or the
    /// process is taking too long to tell the rules to stop expanding as much as
    /// possible.
    pub fn expand<R: Rng + Sized>(
        &mut self,
        state: &mut FT::State,
        terminate: bool,
        rng: &mut R,
    ) -> Result<bool, FT::Error> {
        let mut waiting = self.waiting.clone();

        while !waiting.is_empty() {
            let mut rules = self.rules.clone();
            let waiting_choice: usize = (rng.random::<u64>() as usize) % waiting.len();

            let chosen = waiting[waiting_choice].clone();
            waiting.remove(waiting_choice);

            let heritage = if let Some(heritage) = self.structure.find_in_structure(&chosen.atom) {
                heritage
            } else {
                return Err("Parity wasn't kept between the structure and waiting list".into());
            };

            while !rules.is_empty() {
                let rule_choice: usize = (rng.random::<u64>() as usize) % rules.len();
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
