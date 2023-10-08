use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::{BodyForm, CompileForm, HelperForm, SExp};
use crate::compiler::sexp::ToSExp;
use crate::compiler::srcloc::Srcloc;

pub struct FunctionDependencyGraph {
    pub loc: Srcloc,
    pub helpers: HashSet<Vec<u8>>,
    pub helper_depends_on: HashMap<Vec<u8>, HashSet<Vec<u8>>>,
    pub helper_is_depended_on: HashMap<Vec<u8>, HashSet<Vec<u8>>>,
}

fn insert_into_collection(collection: &mut HashMap<Vec<u8>, HashSet<Vec<u8>>>, at: &[u8], new_member: &[u8]) {
    if let Some(d) = collection.get_mut(at) {
        d.insert(new_member.to_vec());
    } else {
        let hs: HashSet<Vec<u8>> = [new_member.to_vec()].iter().cloned().collect();
        collection.insert(at.to_vec(), hs);
    }
}

impl FunctionDependencyGraph {
    pub fn to_sexp(&self) -> Rc<SExp> {
        let list = vec![
            ("helpers", self.helpers.to_sexp(self.loc.clone())),
            ("helper_depends_on", self.helper_depends_on.to_sexp(self.loc.clone())),
            ("helper_is_depended_on", self.helper_is_depended_on.to_sexp(self.loc.clone())),
        ];

        list.to_sexp(self.loc.clone())
    }

    pub fn get_full_depended_on_by(&self, depended_on_by: &mut HashSet<Vec<u8>>, helper_name: &[u8]) {
        if let Some(depended_on) = self.helper_is_depended_on.get(helper_name) {
            for d in depended_on.iter() {
                if !depended_on_by.contains(d) {
                    depended_on_by.insert(d.to_vec());
                    self.get_full_depended_on_by(depended_on_by, d);
                }
            }
        }
    }

    pub fn get_full_depends_on(&self, depends_on_fun: &mut HashSet<Vec<u8>>, helper_name: &[u8]) {
        if let Some(depends_on) = self.helper_depends_on.get(helper_name) {
            for d in depends_on.iter() {
                if !depends_on_fun.contains(d) {
                    depends_on_fun.insert(d.clone());
                    self.get_full_depends_on(depends_on_fun, d);
                }
            }
        }
    }

    fn process_expr(&mut self, helper_name: &[u8], expr: Rc<BodyForm>) {
        match expr.borrow() {
            BodyForm::Value(SExp::Atom(_, name)) => {
                if self.helpers.contains(name) {
                    // This introduces a function dependency.
                    insert_into_collection(&mut self.helper_depends_on, helper_name, &name);
                    insert_into_collection(&mut self.helper_is_depended_on, &name, helper_name);
                }
            }
            BodyForm::Value(_) => { }
            BodyForm::Let(_, letdata) => {
                for b in letdata.bindings.iter() {
                    self.process_expr(helper_name, b.body.clone());
                }

                self.process_expr(helper_name, letdata.body.clone());
            }
            BodyForm::Call(_, args, tail) => {
                if let Some(t) = tail.as_ref() {
                    self.process_expr(helper_name, t.clone());
                }

                for a in args.iter() {
                    self.process_expr(helper_name, a.clone());
                }
            }
            BodyForm::Lambda(ldata) => {
                self.process_expr(helper_name, ldata.captures.clone());
                self.process_expr(helper_name, ldata.body.clone());
            }
            BodyForm::Quoted(_) => { }
            BodyForm::Mod(_, _) => { }
        }
    }

    fn process_helper(&mut self, h: &HelperForm) {
        if let HelperForm::Defun(_, defun) = h {
            self.process_expr(&defun.name, defun.body.clone());
        }
    }

    pub fn new(program: &CompileForm) -> Self {
        let helpers: HashSet<Vec<u8>> = program.helpers.iter().map(|h| {
            h.name().to_vec()
        }).collect();

        let mut graph = FunctionDependencyGraph {
            loc: program.loc.clone(),
            helpers: helpers,
            helper_depends_on: HashMap::default(),
            helper_is_depended_on: HashMap::default(),
        };

        for h in program.helpers.iter() {
            graph.process_helper(h);
        }

        graph
    }

}
