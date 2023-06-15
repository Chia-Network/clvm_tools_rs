extern crate clvm_tools_rs;
extern crate num_bigint;
extern crate rand;
extern crate rand_chacha;

use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::rc::Rc;

use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use clvm_tools_rs::compiler::clvm::truthy;
use clvm_tools_rs::compiler::comptypes::{Binding, BindingPattern, BodyForm, CompileForm, ConstantKind, DefconstData, DefunData, HelperForm, LambdaData, LetData, LetFormKind};
use clvm_tools_rs::compiler::evaluate::make_operator2;
use clvm_tools_rs::compiler::sexp::{enlist, SExp};
use clvm_tools_rs::compiler::srcloc::Srcloc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operator {
    If,
    IsList,
    Plus,
    Times,
    Minus,
    Sha256Tree,
    Cons,
    First,
    Rest,
    Exn,
}

impl Operator {
    fn to_expr(&self, l: &Srcloc) -> (usize, Rc<BodyForm>) {
        match self {
            Operator::If => (3, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"i".to_vec())))),
            Operator::IsList => (1, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"l".to_vec())))),
            Operator::Plus => (0, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"+".to_vec())))),
            Operator::Times => (0, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"*".to_vec())))),
            Operator::Minus => (2, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"-".to_vec())))),
            Operator::Sha256Tree => (1, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"sha256tree".to_vec())))),
            Operator::Cons => (2, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"c".to_vec())))),
            Operator::First => (1, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"f".to_vec())))),
            Operator::Rest => (1, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"r".to_vec())))),
            Operator::Exn => (0, Rc::new(BodyForm::Value(SExp::Atom(l.clone(), b"x".to_vec())))),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprAction {
    PushNil,
    PushLiteral(i32),
    PushConstant(usize),
    PushVariable(usize),
    MakeLambda(usize,usize),
    LetVar,
    FinishLet,
    CallFunction(usize),
    ApplyFunction(usize),
    ApplyOperator(Operator)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HelperAction {
    PushArgument,
    Expr(ExprAction)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramAction {
    PushArgument,
    PushHelper(u8, HelperAction),
    PushConstant(u8, ExprAction),
    Expr(ExprAction)
}

impl Distribution<Operator> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Operator {
        let kind: u8 = rng.gen();
        match kind % 10 {
            0 => Operator::If,
            2 => Operator::IsList,
            3 => Operator::Plus,
            4 => Operator::Times,
            5 => Operator::Sha256Tree,
            6 => Operator::Cons,
            7 => Operator::First,
            8 => Operator::Rest,
            _ => Operator::Exn
        }
    }
}

impl Distribution<ExprAction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ExprAction {
        let kind: u8 = rng.gen();
        match kind % 7 {
            0 => ExprAction::PushNil,
            1 => ExprAction::PushConstant(rng.gen()),
            2 => ExprAction::PushVariable(rng.gen()),
            3 => ExprAction::MakeLambda(rng.gen(), rng.gen()),
            4 => ExprAction::LetVar,
            5 => ExprAction::FinishLet,
            _ => ExprAction::ApplyOperator(rng.gen())
        }
    }
}

impl Distribution<HelperAction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> HelperAction {
        let kind: u8 = rng.gen();
        match kind % 2 {
            0 => HelperAction::PushArgument,
            _ => HelperAction::Expr(rng.gen())
        }
    }
}

impl Distribution<ProgramAction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ProgramAction {
        let kind: u8 = rng.gen();
        match kind % 2 {
            0 => ProgramAction::PushHelper(rng.gen(), rng.gen()),
            _ => ProgramAction::Expr(rng.gen())
        }
    }
}

#[derive(Debug, Clone)]
struct ExpressionContext {
    let_binding_stack: Vec<Rc<BodyForm>>,
    expression_stack: Vec<Rc<BodyForm>>,
}

pub fn make_captures(sexp: Rc<SExp>) -> Rc<BodyForm> {
    if let SExp::Cons(l, f, r) = sexp.borrow() {
        Rc::new(make_operator2(
            l,
            "c".to_string(),
            make_captures(f.clone()),
            make_captures(r.clone()),
        ))
    } else if !truthy(sexp.clone()) {
        Rc::new(BodyForm::Quoted(SExp::Nil(sexp.loc())))
    } else {
        let sexp_borrowed: &SExp = sexp.borrow();
        Rc::new(BodyForm::Value(sexp_borrowed.clone()))
    }
}

impl ExpressionContext {
    fn new(l: &Srcloc) -> Self {
        ExpressionContext {
            let_binding_stack: Vec::new(),
            expression_stack: Vec::new()
        }
    }

    fn pop_expr(&mut self, l: &Srcloc) -> Rc<BodyForm> {
        self.expression_stack.pop().unwrap_or_else(|| {
            Rc::new(BodyForm::Quoted(SExp::Nil(l.clone())))
        })
    }

    fn update(&mut self, l: &Srcloc, functions: usize, constants: usize, vars: &mut usize, command: &ExprAction) {
        match command {
            ExprAction::LetVar => {
                let top_element = self.pop_expr(l);
                self.let_binding_stack.push(top_element);
                *vars += 1;
            }
            ExprAction::FinishLet => {
                if self.let_binding_stack.is_empty() {
                    return;
                }

                let count_from = *vars - self.let_binding_stack.len();
                let bindings = self.let_binding_stack.iter().enumerate()
                    .map(|(i,expr)| {
                        let name =
                            format!("v{}", count_from + i).as_bytes().to_vec();
                        Rc::new(Binding {
                            loc: l.clone(),
                            nl: l.clone(),
                            pattern: BindingPattern::Name(name),
                            body: expr.clone(),
                        })
                    }).collect();
                self.let_binding_stack.clear();
                let body = self.pop_expr(l);
                self.expression_stack.push(
                    Rc::new(BodyForm::Let(LetFormKind::Parallel, Box::new(LetData {
                        loc: l.clone(),
                        kw: None,
                        inline_hint: None,
                        bindings: bindings,
                        body: body
                    })))
                );
            }
            ExprAction::PushNil => {
                self.expression_stack.push(Rc::new(BodyForm::Quoted(SExp::Nil(l.clone()))));
            }
            ExprAction::PushLiteral(n) => {
                self.expression_stack.push(Rc::new(BodyForm::Quoted(SExp::Integer(l.clone(), n.to_bigint().unwrap()))));
            }
            ExprAction::PushConstant(cid) => {
                if constants == 0 {
                    return;
                }
                let constant_id = cid % constants;
                let constant_name = format!("c{}", constant_id).as_bytes().to_vec();
                self.expression_stack.push(Rc::new(BodyForm::Value(SExp::Atom(l.clone(), constant_name))));
            }
            ExprAction::PushVariable(vid) => {
                if *vars == 0 {
                    return;
                }
                let variable_id = vid % *vars;
                let variable_name = format!("v{}", variable_id).as_bytes().to_vec();
                self.expression_stack.push(Rc::new(BodyForm::Value(SExp::Atom(l.clone(), variable_name))));
            }
            ExprAction::MakeLambda(raw_captures,new_args) => {
                let num_captures =
                    if *vars == 0 {
                        0
                    } else {
                        raw_captures % *vars
                    };
                let num_new_args =
                    if *vars == 0 {
                        0
                    } else {
                        new_args % *vars
                    };
                let captures: Vec<Rc<SExp>> = (0..num_captures).map(|c| {
                    let name = format!("v{}", *vars - c - 1).as_bytes().to_vec();
                    Rc::new(SExp::Atom(l.clone(), name))
                }).collect();
                let arg_list: Vec<Rc<SExp>> = (0..num_new_args).map(|a| {
                    let name = format!("v{}", a).as_bytes().to_vec();
                    Rc::new(SExp::Atom(l.clone(), name))
                }).collect();
                let args = Rc::new(enlist(l.clone(), &arg_list));
                let capture_form = Rc::new(enlist(l.clone(), &captures));
                let lambda_body = self.pop_expr(l);
                let new_lambda = Rc::new(BodyForm::Lambda(Box::new(LambdaData{
                    loc: l.clone(),
                    kw: None,
                    capture_args: capture_form.clone(),
                    captures: make_captures(capture_form),
                    args,
                    body: lambda_body
                })));
                self.expression_stack.push(new_lambda);
            }
            ExprAction::CallFunction(which) => {
                if functions == 0 {
                    return;
                }
                let fname = format!("func_{}", which % functions).as_bytes().to_vec();
                let mut args = self.expression_stack.clone();
                self.expression_stack.clear();
                let function_expr = Rc::new(BodyForm::Value(SExp::Atom(l.clone(), fname)));
                args.insert(0, function_expr);
                self.expression_stack.push(Rc::new(BodyForm::Call(
                    l.clone(),
                    args
                )));
            }
            ExprAction::ApplyFunction(which) => {
                if functions == 0 {
                    return;
                }
                let fname = format!("func_{}", which % functions).as_bytes().to_vec();
                let args = self.pop_expr(l);
                self.expression_stack.push(Rc::new(BodyForm::Call(
                    l.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(l.clone(), vec![2]))),
                        Rc::new(BodyForm::Value(SExp::Atom(l.clone(), fname))),
                        args
                    ]
                )));
            }
            ExprAction::ApplyOperator(op) => {
                let (nargs, op_expr) = op.to_expr(l);
                let mut args_list = vec![op_expr];
                if nargs == 0 {
                    args_list.append(&mut self.expression_stack);
                    self.expression_stack.clear();
                } else {
                    for a in 0..nargs {
                        args_list.push(self.pop_expr(l));
                    }
                }
                self.expression_stack.push(Rc::new(BodyForm::Call(
                    l.clone(),
                    args_list
                )));
            }
        }
    }
}

#[derive(Debug, Clone)]
struct HelperContext {
    args: Rc<SExp>,
    vars_in_scope: usize,
    inline: bool,
    expression: ExpressionContext,
}

impl HelperContext {
    fn new(l: &Srcloc, inline: bool) -> Self {
        HelperContext {
            args: Rc::new(SExp::Nil(l.clone())),
            vars_in_scope: 0,
            inline,
            expression: ExpressionContext::new(l),
        }
    }

    fn update(&mut self, l: &Srcloc, functions: usize, constants: usize, command: &HelperAction) {
        match command {
            HelperAction::PushArgument => {
                let aname = format!("v{}", self.vars_in_scope).as_bytes().to_vec();
                self.vars_in_scope += 1;
                self.args = Rc::new(SExp::Cons(
                    l.clone(),
                    Rc::new(SExp::Atom(l.clone(), aname)),
                    self.args.clone()
                ));
            }
            HelperAction::Expr(ea) => {
                self.expression.update(l, functions, constants, &mut self.vars_in_scope, ea);
            }
        }
    }

    fn to_helperform(&self, i: usize, l: &Srcloc) -> HelperForm {
        let mut e_clone = self.expression.clone();
        HelperForm::Defun(self.inline, DefunData {
            loc: l.clone(),
            name: format!("func_{}", i).as_bytes().to_vec(),
            kw: None,
            nl: l.clone(),
            orig_args: self.args.clone(),
            args: self.args.clone(),
            body: e_clone.pop_expr(l),
            synthetic: None,
            ty: None
        })
    }
}

#[derive(Debug, Clone)]
struct ProgramContext {
    args: Rc<SExp>,
    vars_in_scope: usize,
    constants: Vec<ExpressionContext>,
    helpers: Vec<HelperContext>,
    expression: ExpressionContext,
}

impl ProgramContext {
    fn new<R: Rng + ?Sized>(rng: &mut R, l: &Srcloc, num_helpers: usize, num_constants: usize) -> Self {
        let helpers = (0..num_helpers)
            .map(|_| HelperContext::new(l, rng.gen())).collect();
        let constants = (0..num_constants)
            .map(|_| ExpressionContext::new(l)).collect();
        ProgramContext {
            args: Rc::new(SExp::Nil(l.clone())),
            vars_in_scope: 0,
            constants: constants,
            helpers: helpers,
            expression: ExpressionContext::new(l),
        }
    }

    fn update(&mut self, l: &Srcloc, command: &ProgramAction) {
        match command {
            ProgramAction::PushArgument => {
                let aname = format!("v{}", self.vars_in_scope).as_bytes().to_vec();
                self.vars_in_scope += 1;
                self.args = Rc::new(SExp::Cons(
                    l.clone(),
                    Rc::new(SExp::Atom(l.clone(), aname)),
                    self.args.clone()
                ));
            }
            ProgramAction::PushHelper(which, ha) => {
                if self.helpers.is_empty() {
                    return;
                }
                let which_helper = (*which as usize) % self.helpers.len();
                let hlen = self.helpers.len();
                self.helpers[which_helper].update(l, hlen, self.constants.len(), ha);
            }
            ProgramAction::PushConstant(which, ea) => {
                if self.constants.is_empty() {
                    return;
                }
                let which_constant = (*which as usize) % self.constants.len();
                let mut vars = 0;
                self.constants[which_constant].update(l, 0, which_constant, &mut vars, &ea);
            }
            ProgramAction::Expr(ea) => {
                self.expression.update(l, self.helpers.len(), self.constants.len(), &mut self.vars_in_scope, ea);
            }
        }
    }

    fn to_compileform(&self, l: &Srcloc) -> CompileForm {
        let mut helpers: Vec<HelperForm> = self.constants.iter().enumerate().map(|(i,c)| {
            let mut c_clone = c.clone();
            HelperForm::Defconstant(DefconstData {
                loc: l.clone(),
                kind: ConstantKind::Complex,
                name: format!("c{}", i).as_bytes().to_vec(),
                kw: None,
                nl: l.clone(),
                body: c_clone.pop_expr(l),
                tabled: true,
                ty: None,
            })
        }).collect();
        let mut defuns = self.helpers.iter().enumerate().map(|(i,h)| {
            h.to_helperform(i, l)
        }).collect();
        helpers.append(&mut defuns);
        let mut e_clone = self.expression.clone();
        CompileForm {
            loc: l.clone(),
            include_forms: Vec::new(),
            args: self.args.clone(),
            helpers,
            exp: e_clone.pop_expr(l),
            ty: None
        }
    }
}

fn random_list_of<X, R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<X>
where
    Standard: Distribution<X>
{
    (0..n).map(|_| rng.gen()).collect()
}

fn main() {
    let mut rng = ChaCha8Rng::from_entropy();
    let list_of_things: Vec<ProgramAction> = random_list_of(&mut rng, 200);
    let num_helpers: usize = rng.gen();
    let num_constants: usize = rng.gen();
    let srcloc = Srcloc::start("*program*");
    let mut pc = ProgramContext::new(&mut rng, &srcloc, num_helpers % 7, num_constants % 5);
    for thing in list_of_things.iter() {
        pc.update(&srcloc, thing);
    }
    let program = pc.to_compileform(&srcloc);
    eprintln!("program {}", program.to_sexp());
    todo!();
}
