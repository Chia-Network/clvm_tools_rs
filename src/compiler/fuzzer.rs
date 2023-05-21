use num_bigint::{BigInt, ToBigInt};
use num_traits::ToPrimitive;

use rand::distributions::Standard;
use rand::prelude::*;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use std::borrow::Borrow;
use std::cmp::max;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::compiler::clvm::{run, truthy};
use crate::compiler::codegen::create_name_lookup_;
use crate::compiler::prims;
use crate::compiler::sexp::{enlist, SExp};

use crate::compiler::sexp::{random_atom_name, random_sexp};

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType, Stream};
use crate::classic::clvm::casts::bigint_to_bytes_clvm;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::srcloc::Srcloc;
use crate::util::{number_from_u8, Number};

const MIN_ARGLIST: usize = 3;
const MAX_STEPS: usize = 1000;
pub const MAX_LIST_BOUND: usize = 3;
const CURRENT_DIALECT: u32 = 21;
const BINDING_NAME_MIN: usize = 3;

lazy_static! {
    pub static ref FUZZ_ONE_ARG: Vec<FuzzOneArg> = {
        vec![
            FuzzOneArg::First,
            FuzzOneArg::Rest,
            FuzzOneArg::IsList,
            FuzzOneArg::Strlen,
            FuzzOneArg::PubkeyForExp,
            FuzzOneArg::Lognot,
            FuzzOneArg::Not
        ]
    };

    pub static ref FUZZ_TWO_ARG: Vec<FuzzTwoArg> = {
        vec![
            FuzzTwoArg::Cons,
            FuzzTwoArg::Equal,
            FuzzTwoArg::GreaterThanString,
            FuzzTwoArg::Subtract,
            FuzzTwoArg::Divide,
            FuzzTwoArg::Divmod,
            FuzzTwoArg::Greater,
            FuzzTwoArg::Ash,
            FuzzTwoArg::Lsh,
            FuzzTwoArg::Logxor,
        ]
    };

    pub static ref FUZZ_THREE_ARG: Vec<FuzzThreeArg> = {
        vec![
            FuzzThreeArg::IfCond,
            FuzzThreeArg::Substr,
        ]
    };

    pub static ref FUZZ_MULTI_ARG: Vec<FuzzMultiArg> = {
        vec![
            FuzzMultiArg::Add,
            FuzzMultiArg::Multiply,
            FuzzMultiArg::Logand,
            FuzzMultiArg::Logior,
            FuzzMultiArg::Sha256,
            FuzzMultiArg::Concat,
            FuzzMultiArg::Any,
            FuzzMultiArg::All,
            FuzzMultiArg::PointAdd
        ]
    };
}

#[derive(Debug, Clone)]
pub struct FuzzBinding {
    pub name: Vec<u8>,
    pub expr: FuzzOperation,
}

#[derive(Debug, Clone)]
pub enum FuzzOneArg {
    First,
    Rest,
    IsList,
    Strlen,
    PubkeyForExp,
    Lognot,
    Not
}

// Next step is to put apply in here by evaluating the given program
// and parsing it back into FuzzOperation.
#[derive(Debug, Clone)]
pub enum FuzzTwoArg {
    // Apply,
    Cons,
    Equal,
    GreaterThanString,
    Subtract,
    Divide,
    Divmod,
    Greater,
    Ash,
    Lsh,
    Logxor
}

#[derive(Debug, Clone)]
pub enum FuzzThreeArg {
    IfCond,
    Substr,
}

#[derive(Debug, Clone)]
pub enum FuzzMultiArg {
    Add,
    Multiply,
    Logand,
    Logior,
    Sha256,
    Concat,
    Any,
    All,
    PointAdd
}

// We don't actually need all operators here, just a good selection with
// semantics that are distinguishable.
#[derive(Debug, Clone)]
pub enum FuzzOperation {
    // Basic values.
    Argref(usize),
    Quote(SExp),

    // Primitives.
    OneArg(FuzzOneArg, Rc<FuzzOperation>),
    TwoArg(FuzzTwoArg, Rc<FuzzOperation>, Rc<FuzzOperation>),
    ThreeArg(
        FuzzThreeArg,
        Rc<FuzzOperation>,
        Rc<FuzzOperation>,
        Rc<FuzzOperation>
    ),
    MultiArg(FuzzMultiArg, Vec<FuzzOperation>),

    // Standard macros.
    List(Vec<FuzzOperation>),
    If(Rc<FuzzOperation>, Rc<FuzzOperation>, Rc<FuzzOperation>),

    // Language features.
    Let(Vec<FuzzBinding>, Rc<FuzzOperation>),
    Call(u8, Vec<FuzzOperation>),
}

#[derive(Debug, Clone)]
pub enum ArgListType {
    ProperList(u8),
    Structure(SExp),
}

#[derive(Debug, Clone)]
pub struct FuzzFunction {
    pub inline: bool,
    pub number: u8,
    pub args: ArgListType,
    pub body: FuzzOperation,
}

#[derive(Debug, Clone)]
pub struct FuzzProgram {
    pub args: ArgListType,
    pub functions: Vec<FuzzFunction>,
    pub body: FuzzOperation,
}

#[derive(Debug, Clone)]
pub struct FuzzOldProgram {
    pub program: FuzzProgram,
}

fn select_from_list<R: Rng + ?Sized, T>(rng: &mut R, v: &[T]) -> T
where
    T: Clone
{
    v[rng.gen_range(0..v.len())].clone()
}

impl Distribution<FuzzOneArg> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOneArg {
        select_from_list(rng, &FUZZ_ONE_ARG)
    }
}

impl Distribution<FuzzTwoArg> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzTwoArg {
        select_from_list(rng, &FUZZ_TWO_ARG)
    }
}

impl Distribution<FuzzThreeArg> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzThreeArg {
        select_from_list(rng, &FUZZ_THREE_ARG)
    }
}

impl Distribution<FuzzMultiArg> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzMultiArg {
        select_from_list(rng, &FUZZ_MULTI_ARG)
    }
}

fn atom_list(sexp: &SExp) -> Vec<Vec<u8>> {
    match sexp {
        SExp::Nil(_) => vec![],
        SExp::Atom(_, v) => {
            if v.is_empty() {
                vec![]
            } else {
                vec![v.clone()]
            }
        }
        SExp::QuotedString(_, _, _) => vec![],
        SExp::Integer(_, _) => vec![],
        SExp::Cons(_, a, b) => {
            let mut a_vec = atom_list(a.borrow());
            let b_vec = atom_list(b.borrow());
            for b_item in b_vec.iter() {
                a_vec.push(b_item.clone());
            }
            a_vec
        }
    }
}

fn select_argument(
    num: usize,
    fun: &FuzzProgram,
    bindings: &[Vec<FuzzBinding>],
) -> (SExp, Option<FuzzOperation>) {
    let args_sexp = fun.args.to_sexp();
    let select_group = (num >> 8) % (bindings.len() + 1);
    if select_group == bindings.len() {
        // Select from arguments
        let arg_list = atom_list(&args_sexp);
        let nil = SExp::Nil(args_sexp.loc());
        if arg_list.is_empty() {
            (nil.clone(), Some(FuzzOperation::Quote(nil)))
        } else {
            let selected_arg = arg_list[num & 0xff % arg_list.len()].clone();
            (SExp::Atom(args_sexp.loc(), selected_arg), None)
        }
    } else {
        // Select a binding group using the second byte,
        let group = &bindings[select_group];
        let select_binding = (num & 0xff) % group.len();
        let selected_binding = &group[select_binding];
        // Select a binding using the first byte.
        (
            SExp::Atom(args_sexp.loc(), selected_binding.name.clone()),
            Some(selected_binding.expr.clone()),
        )
    }
}

fn select_call(num: u8, prog: &FuzzProgram) -> (String, FuzzFunction) {
    if prog.functions.len() == 0 {
        panic!("we make programs with at least one function");
    }
    let selected_num = num % prog.functions.len() as u8;
    let selected = &prog.functions[selected_num as usize];
    (format!("fun_{}", selected_num), selected.clone())
}

fn make_operator(op: String, args: Vec<SExp>) -> SExp {
    let loc = Srcloc::start(&"*rng*".to_string());
    let mut result = SExp::Nil(loc.clone());

    for i_reverse in 0..args.len() {
        let i = args.len() - i_reverse - 1;
        result = SExp::Cons(loc.clone(), Rc::new(args[i].clone()), Rc::new(result));
    }

    SExp::Cons(
        loc.clone(),
        Rc::new(SExp::atom_from_string(loc.clone(), &op)),
        Rc::new(result),
    )
}

fn distribute_args(
    a: ArgListType,
    fun: &FuzzProgram,
    bindings: &[Vec<FuzzBinding>],
    arginputs: &Vec<SExp>,
    spine: bool,
    argn: u8,
) -> (u8, SExp) {
    let loc = Srcloc::start(&"*rng*".to_string());
    match a {
        ArgListType::ProperList(0) => (argn, SExp::Nil(loc.clone())),
        ArgListType::ProperList(n) => {
            let rest_result = distribute_args(
                ArgListType::ProperList(n - 1),
                fun,
                bindings,
                arginputs,
                spine,
                argn + 1,
            );
            (
                rest_result.0,
                SExp::Cons(
                    loc.clone(),
                    Rc::new(arginputs[argn as usize].clone()),
                    Rc::new(rest_result.1),
                ),
            )
        }
        ArgListType::Structure(SExp::Nil(l)) => (argn, SExp::Nil(l.clone())),
        ArgListType::Structure(SExp::Cons(l, a, b)) => {
            let a_borrow: &SExp = a.borrow();
            let b_borrow: &SExp = b.borrow();
            let first_res = distribute_args(
                ArgListType::Structure(a_borrow.clone()),
                fun,
                bindings,
                arginputs,
                false,
                argn,
            );
            let rest_res = distribute_args(
                ArgListType::Structure(b_borrow.clone()),
                fun,
                bindings,
                arginputs,
                spine,
                argn + first_res.0,
            );
            let res = if spine {
                SExp::Cons(l.clone(), Rc::new(first_res.1), Rc::new(rest_res.1))
            } else {
                make_operator("c".to_string(), vec![first_res.1, rest_res.1])
            };
            (rest_res.0, res)
        }
        ArgListType::Structure(_) => {
            if spine {
                distribute_args(
                    ArgListType::ProperList(1),
                    fun,
                    bindings,
                    arginputs,
                    spine,
                    argn,
                )
            } else {
                (argn + 1_u8, arginputs[argn as usize].clone())
            }
        }
    }
}

fn random_args<R: Rng + ?Sized>(rng: &mut R, loc: Srcloc, a: ArgListType) -> SExp {
    match a {
        ArgListType::ProperList(0) => SExp::Nil(loc.clone()),
        ArgListType::ProperList(n) => {
            let loc = Srcloc::start("*rng*");
            enlist(loc, (0..n).map(|_| Rc::new(rng.gen())).collect())
        }
        ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
        ArgListType::Structure(SExp::Cons(_, a, b)) => {
            let borrowed_a: &SExp = a.borrow();
            let borrowed_b: &SExp = b.borrow();
            SExp::Cons(
                loc.clone(),
                Rc::new(random_args(
                    rng,
                    loc.clone(),
                    ArgListType::Structure(borrowed_a.clone()),
                )),
                Rc::new(random_args(
                    rng,
                    loc.clone(),
                    ArgListType::Structure(borrowed_b.clone()),
                )),
            )
        }
        ArgListType::Structure(_) => {
            let random_64: u64 = rng.gen();
            SExp::Integer(loc.clone(), random_64.to_bigint().unwrap())
        }
    }
}

impl FuzzOperation {
    pub fn to_sexp(&self, fun: &FuzzProgram, bindings: &[Vec<FuzzBinding>]) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            FuzzOperation::Argref(argument_num) => {
                let argument = select_argument(*argument_num as usize, fun, &bindings);
                argument.0
            }
            FuzzOperation::Quote(s) => SExp::Cons(
                loc.clone(),
                Rc::new(SExp::atom_from_string(loc.clone(), &"q".to_string())),
                Rc::new(s.clone()),
            ),
            FuzzOperation::If(cond, ct, cf) => make_operator(
                "if".to_string(),
                vec![
                    cond.to_sexp(fun, bindings),
                    ct.to_sexp(fun, bindings),
                    cf.to_sexp(fun, bindings),
                ],
            ),
            FuzzOperation::OneArg(op, a) => {
                let operator =
                    match op {
                        FuzzOneArg::First => "f",
                        FuzzOneArg::Rest => "r",
                        FuzzOneArg::IsList => "l",
                        FuzzOneArg::Strlen => "strlen",
                        FuzzOneArg::PubkeyForExp => "pubkey_for_exp",
                        FuzzOneArg::Lognot => "lognot",
                        FuzzOneArg::Not => "not"
                    };
                make_operator(
                    operator.to_string(),
                    vec![a.to_sexp(fun, bindings)]
                )
            },
            FuzzOperation::TwoArg(op, a, b) => {
                let operator =
                    match op {
                        FuzzTwoArg::Cons => "c",
                        FuzzTwoArg::Equal => "=",
                        FuzzTwoArg::GreaterThanString => ">s",
                        FuzzTwoArg::Subtract => "-",
                        FuzzTwoArg::Divide => "/",
                        FuzzTwoArg::Divmod => "divmod",
                        FuzzTwoArg::Greater => ">",
                        FuzzTwoArg::Ash => "ash",
                        FuzzTwoArg::Lsh => "lsh",
                        FuzzTwoArg::Logxor => "logxor",
                    };
                make_operator(
                    operator.to_string(),
                    vec![a.to_sexp(fun, bindings), b.to_sexp(fun, bindings)]
                )
            },
            FuzzOperation::ThreeArg(op, a, b, c) => {
                let operator =
                    match op {
                        FuzzThreeArg::IfCond => "i",
                        FuzzThreeArg::Substr => "substr"
                    };
                make_operator(
                    operator.to_string(),
                    vec![
                        a.to_sexp(fun, bindings),
                        b.to_sexp(fun, bindings),
                        c.to_sexp(fun, bindings)
                    ]
                )
            },
            FuzzOperation::MultiArg(op, mults) => {
                let operator =
                    match op {
                        FuzzMultiArg::Add => "+",
                        FuzzMultiArg::Multiply => "*",
                        FuzzMultiArg::Logand => "logand",
                        FuzzMultiArg::Logior => "logior",
                        FuzzMultiArg::Sha256 => "sha256",
                        FuzzMultiArg::Concat => "concat",
                        FuzzMultiArg::Any => "any",
                        FuzzMultiArg::All => "all",
                        FuzzMultiArg::PointAdd => "point_add"
                    };
                make_operator(
                    operator.to_string(),
                    mults.iter().map(|arg| arg.to_sexp(fun, bindings)).collect()
                )
            },
            FuzzOperation::List(lst) => {
                make_operator(
                    "list".to_string(),
                    lst.iter().map(|arg| arg.to_sexp(fun, bindings)).collect()
                )
            },
            FuzzOperation::Let(our_bindings, body) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let mut bindings_done = SExp::Nil(loc.clone());

                for b in our_bindings.iter().rev() {
                    bindings_done = SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            Rc::new(SExp::Atom(loc.clone(), b.name.clone())),
                            Rc::new(SExp::Cons(
                                loc.clone(),
                                Rc::new(b.expr.to_sexp(fun, bindings)),
                                Rc::new(SExp::Nil(loc.clone())),
                            )),
                        )),
                        Rc::new(bindings_done),
                    );
                }

                let mut inner_bindings = bindings.to_vec();
                inner_bindings.push(our_bindings.clone());

                make_operator(
                    "let".to_string(),
                    vec![bindings_done, body.to_sexp(fun, &inner_bindings)],
                )
            }
            FuzzOperation::Call(selection, args) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let called_fun = select_call(*selection, fun);
                let mut reified_args = Vec::new();
                for a in args.iter() {
                    reified_args.push(a.to_sexp(fun, bindings));
                }
                let args = distribute_args(
                    called_fun.1.args.clone(),
                    fun,
                    bindings,
                    &reified_args,
                    true,
                    0,
                );
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &called_fun.0)),
                    Rc::new(args.1),
                )
            }
        }
    }
}

fn make_random_call<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzOperation {
    FuzzOperation::Call(
        rng.gen(),
        (0..=255)
            .map(|_| random_operation(rng, dialect, remaining - 1))
            .collect(),
    )
}

// FuzzOperation is potentially infinite so we'll limit the depth to something
// sensible.
fn random_operation<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzOperation {
    if remaining < 2 {
        FuzzOperation::Quote(random_sexp(rng, remaining))
    } else {
        let op_bound = if dialect >= 21 { 9 } else { 8 };
        let alternative: usize = rng.gen_range(0..=op_bound);
        match alternative {
            0 => FuzzOperation::Quote(random_sexp(rng, remaining)),
            1 => FuzzOperation::Argref(rng.gen()),
            2 => FuzzOperation::If(
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            3 => {
                let bound: usize = rng.gen_range(1..=MAX_LIST_BOUND);
                FuzzOperation::List(
                    (0..=bound)
                        .map(|_| random_operation(rng, dialect, remaining - 1))
                        .collect()
                )
            },
            4 => FuzzOperation::OneArg(
                rng.gen(),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            5 => FuzzOperation::TwoArg(
                rng.gen(),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            6 => FuzzOperation::ThreeArg(
                rng.gen(),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            7 => {
                let bound: usize = rng.gen_range(1..=MAX_LIST_BOUND);
                FuzzOperation::MultiArg(
                    rng.gen(),
                    (0..=bound)
                        .map(|_| random_operation(rng, dialect, remaining - 1))
                        .collect()
                )
            },
            8 => make_random_call(rng, dialect, remaining - 1),
            _ => {
                let bound: usize = rng.gen_range(1..=5);
                let new_bindings: Vec<FuzzBinding> = (1..=bound)
                    .map(|_| FuzzBinding {
                        name: random_atom_name(rng, BINDING_NAME_MIN),
                        expr: random_operation(rng, dialect, remaining - 1),
                    })
                    .collect();
                FuzzOperation::Let(
                    new_bindings,
                    Rc::new(random_operation(rng, dialect, remaining - 1)),
                )
            }
        }
    }
}

impl Distribution<FuzzOperation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOperation {
        random_operation(rng, 22, MAX_LIST_BOUND)
    }
}

fn min_arglist(remaining: usize) -> usize {
    max(remaining, MIN_ARGLIST)
}

fn random_arglist_cons<R: Rng + ?Sized>(rng: &mut R, loc: &Srcloc, remaining: usize) -> SExp {
    if rng.gen() || remaining < 1 {
        SExp::Atom(loc.clone(), random_atom_name(rng, 2))
    } else {
        let left = random_arglist_cons(rng, loc, remaining - 1);
        let right = random_arglist_cons(rng, loc, remaining - 1);
        SExp::Cons(loc.clone(), Rc::new(left), Rc::new(right))
    }
}

fn random_arglist<R: Rng + ?Sized>(rng: &mut R, remaining: usize) -> ArgListType {
    let loc = Srcloc::start("*arglist*");
    let truncated_len = (remaining % 255) as u8;
    if rng.gen() {
        ArgListType::ProperList(rng.gen_range(0..=truncated_len))
    } else {
        let mut structure = SExp::Nil(loc.clone());
        for _ in 0..=min_arglist(truncated_len as usize) {
            structure = SExp::Cons(
                loc.clone(),
                Rc::new(random_arglist_cons(rng, &loc, remaining - 1)),
                Rc::new(structure),
            );
        }

        ArgListType::Structure(structure)
    }
}

impl Distribution<ArgListType> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ArgListType {
        random_arglist(rng, MAX_LIST_BOUND)
    }
}

impl ArgListType {
    pub fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for _ in 0..*n {
                    let random_bytes: Vec<u8> = (0..=MAX_LIST_BOUND).map(|_| rng.gen()).collect();
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_vec(loc.clone(), &random_bytes)),
                        Rc::new(args.clone()),
                    );
                }
                args
            }
            ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
            ArgListType::Structure(SExp::Cons(l, a, b)) => {
                let aborrow: &SExp = a.borrow();
                let bborrow: &SExp = b.borrow();
                let aclone = aborrow.clone();
                let bclone = bborrow.clone();
                let arg_a = ArgListType::Structure(aclone).random_args(rng);
                let arg_b = ArgListType::Structure(bclone).random_args(rng);
                SExp::Cons(l.clone(), Rc::new(arg_a), Rc::new(arg_b))
            }
            ArgListType::Structure(_) => rng.gen(),
        }
    }

    fn to_sexp(&self) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for i_reverse in 0..*n {
                    let i = n - i_reverse;
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_string(loc.clone(), &format!("arg_{}", i))),
                        Rc::new(args.clone()),
                    );
                }
                args
            }
            ArgListType::Structure(s) => s.clone(),
        }
    }
}

fn random_function<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzFunction {
    FuzzFunction {
        inline: rng.gen(),
        number: 0,
        args: random_arglist(rng, remaining - 1),
        body: random_operation(rng, dialect, remaining - 1),
    }
}

impl Distribution<FuzzFunction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzFunction {
        random_function(rng, CURRENT_DIALECT, MAX_LIST_BOUND)
    }
}

impl FuzzFunction {
    fn to_sexp(&self, fun: &FuzzProgram) -> SExp {
        let fuzzloc = Srcloc::start(&"*fuzz*".to_string());
        let initial_atom = if self.inline {
            SExp::atom_from_string(fuzzloc.clone(), &"defun-inline".to_string())
        } else {
            SExp::atom_from_string(fuzzloc.clone(), &"defun".to_string())
        };
        let name_atom = SExp::atom_from_string(fuzzloc.clone(), &format!("fun_{}", self.number));
        let args_sexp = self.args.to_sexp();
        let body_sexp = self.body.to_sexp(&self.to_program(fun), &Vec::new());
        SExp::Cons(
            fuzzloc.clone(),
            Rc::new(initial_atom),
            Rc::new(SExp::Cons(
                fuzzloc.clone(),
                Rc::new(name_atom),
                Rc::new(SExp::Cons(
                    fuzzloc.clone(),
                    Rc::new(args_sexp),
                    Rc::new(SExp::Cons(
                        fuzzloc.clone(),
                        Rc::new(body_sexp),
                        Rc::new(SExp::Nil(fuzzloc.clone())),
                    )),
                )),
            )),
        )
    }

    fn to_program(&self, parent: &FuzzProgram) -> FuzzProgram {
        FuzzProgram {
            args: self.args.clone(),
            functions: parent.functions.clone(),
            body: self.body.clone(),
        }
    }
}

/*
 * Produce chialisp frontend code with an expected result
 */
fn random_program<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzProgram {
    let num_funs = rng.gen_range(1..=MAX_LIST_BOUND);
    let funs: Vec<FuzzFunction> = (1..=num_funs)
        .map(|_| random_function(rng, dialect, remaining - 1))
        .enumerate()
        .map(|(i, f): (usize, FuzzFunction)| {
            let mut fcopy = f.clone();
            fcopy.number = i as u8;
            fcopy
        })
        .collect();
    FuzzProgram {
        args: random_arglist(rng, remaining),
        functions: funs,
        body: random_operation(rng, dialect, remaining),
    }
}

impl Distribution<FuzzProgram> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzProgram {
        random_program(rng, CURRENT_DIALECT, MAX_LIST_BOUND)
    }
}

fn evaluate_to_number(
    prog: &FuzzProgram,
    args: &SExp,
    bindings: &[Vec<FuzzBinding>],
    a: &FuzzOperation,
    steps: usize,
) -> Result<BigInt, RunFailure> {
    let a_val = interpret_program(prog, args, bindings, a, steps - 1)?;
    match &a_val {
        SExp::Integer(_, a) => Ok(a.clone()),
        SExp::Cons(l, _, _) => Err(RunFailure::RunErr(
            l.clone(),
            format!("expected atom got {}", a_val.to_string()),
        )),
        a => {
            let num_a = a
                .get_number()
                .map_err(|e| RunFailure::RunErr(a.loc(), e.1))?;
            Ok(num_a)
        }
    }
}

fn byte_vec_of_sexp(val: &SExp) -> Result<Vec<u8>, RunFailure> {
    match val {
        SExp::Nil(_) => Ok(Vec::new()),
        SExp::Atom(_, a) => Ok(a.clone()),
        SExp::QuotedString(_, _, s) => Ok(s.clone()),
        SExp::Integer(_, i) => Ok(bigint_to_bytes_clvm(i).data().clone()),
        _ => Err(RunFailure::RunErr(
            val.loc(),
            format!("attempt to convert {} to bytes", val.to_string()),
        )),
    }
}

fn choose_path(path: Number, args: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
    if path == bi_one() {
        Ok(args)
    } else {
        match args.borrow() {
            SExp::Cons(_, a, b) => {
                let odd = bi_one() & path.clone();
                if odd != bi_zero() {
                    choose_path(path >> 1, b.clone())
                } else {
                    choose_path(path >> 1, a.clone())
                }
            }
            _ => Err(RunFailure::RunErr(args.loc(), "path into atom".to_string())),
        }
    }
}

fn do_multi_arg<F>(
    loc: Srcloc,
    prog: &FuzzProgram,
    args: &SExp,
    bindings: &[Vec<FuzzBinding>],
    op: F,
    lst: &[FuzzOperation],
    steps: usize
) -> Result<SExp, RunFailure>
where
    F: Fn(Number, Number) -> Number
{
    let mut result = evaluate_to_number(prog, args, bindings, &lst[0], steps)?;
    for i in lst.iter().skip(1) {
        let b_val =
            evaluate_to_number(prog, args, bindings, &i, steps)?;
        result = op(result, b_val);
    }
    Ok(SExp::Integer(loc, result))
}

fn run_op(
    loc: Srcloc,
    op: SExp,
    args: &[SExp]
) -> Result<SExp, RunFailure> {
    let mut allocator = Allocator::new();
    let runner = Rc::new(DefaultProgramRunner::new());
    let prim_map = prims::prim_map();
    let mut opargs = SExp::Nil(loc.clone());
    for arg in args.iter().rev() {
        opargs = SExp::Cons(
            loc.clone(),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc.clone(), vec![1])),
                Rc::new(arg.clone()),
            )),
            Rc::new(opargs)
        );
    }
    run(
        &mut allocator,
        runner,
        prim_map,
        Rc::new(SExp::Cons(
            loc.clone(),
            Rc::new(op),
            Rc::new(opargs)
        )),
        Rc::new(SExp::Nil(loc)),
        None
    ).map(|v| {
        let vb: &SExp = v.borrow();
        vb.clone()
    })
}

fn interpret_program(
    prog: &FuzzProgram,
    args: &SExp,
    bindings: &[Vec<FuzzBinding>],
    expr: &FuzzOperation,
    steps: usize,
) -> Result<SExp, RunFailure> {
    if steps < 1 {
        return Err(RunFailure::RunErr(
            args.loc(),
            "too many steps taken".to_string(),
        ));
    }
    let loc = Srcloc::start(&"*interp*".to_string());
    eprintln!("running {} with {} in {}", expr.to_sexp(prog, bindings), args, prog.to_sexp());
    match &expr {
        FuzzOperation::Argref(n) => {
            let (argname, run_expression) = select_argument(*n as usize, prog, bindings);
            if let Some(to_run) = run_expression {
                // Run binding code selected.
                interpret_program(prog, args, bindings, &to_run, steps - 1)
            } else {
                // Select argument from env.
                let argpath = create_name_lookup_(
                    args.loc(),
                    &argname.to_string().as_bytes(),
                    Rc::new(prog.args.to_sexp()),
                    Rc::new(prog.args.to_sexp()),
                )
                .map_err(|e| RunFailure::RunErr(e.0.clone(), e.1.clone()))?;
                let argval = choose_path(argpath.to_bigint().unwrap(), Rc::new(args.clone()))?;
                let argval_borrow: &SExp = argval.borrow();
                interpret_program(
                    prog,
                    args,
                    bindings,
                    &FuzzOperation::Quote(argval_borrow.clone()),
                    steps - 1,
                )
            }
        }
        FuzzOperation::Quote(exp) => {
            Ok(exp.clone())
        },
        FuzzOperation::If(cond, iftrue, iffalse) => {
            let borrowed_cond: &FuzzOperation = cond.borrow();
            interpret_program(prog, args, bindings, borrowed_cond, steps - 1)
                .map(|cond_res| truthy(Rc::new(cond_res)))
                .and_then(|cond_res| {
                    if cond_res {
                        let borrowed_iftrue: &FuzzOperation = iftrue.borrow();
                        interpret_program(prog, args, bindings, borrowed_iftrue, steps - 1)
                    } else {
                        let borrowed_iffalse: &FuzzOperation = iffalse.borrow();
                        interpret_program(prog, args, bindings, borrowed_iffalse, steps - 1)
                    }
                })
        }
        FuzzOperation::OneArg(FuzzOneArg::First, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            match output {
                SExp::Cons(_, a, _) => {
                    let first: &SExp = a.borrow();
                    Ok(first.clone())
                }
                _ => Err(RunFailure::RunErr(output.loc(), "first of non-cons".to_string()))
            }
        },
        FuzzOperation::OneArg(FuzzOneArg::Rest, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            match output {
                SExp::Cons(_, _, b) => {
                    let rest: &SExp = b.borrow();
                    Ok(rest.clone())
                }
                _ => Err(RunFailure::RunErr(output.loc(), "first of non-cons".to_string()))
            }
        },
        FuzzOperation::OneArg(FuzzOneArg::IsList, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            let is_list = matches!(output, SExp::Cons(_, _, _));
            Ok(SExp::Integer(output.loc(), (is_list as u32).to_bigint().unwrap()))
        }
        FuzzOperation::OneArg(FuzzOneArg::Strlen, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            let bv = byte_vec_of_sexp(&output)?;
            Ok(SExp::Integer(output.loc(), bv.len().to_bigint().unwrap()))
        }
        FuzzOperation::OneArg(FuzzOneArg::PubkeyForExp, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            run_op(
                loc.clone(),
                SExp::Atom(loc.clone(), b"pubkey_for_exp".to_vec()),
                &[output]
            )
        }
        FuzzOperation::OneArg(FuzzOneArg::Lognot, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            let bv: Vec<u8> = byte_vec_of_sexp(&output)?.iter().map(|b| b ^ 0xff).collect();
            if bv.is_empty() {
                Ok(SExp::Atom(loc, vec![0xff]))
            } else {
                Ok(SExp::Atom(loc, bv))
            }
        }
        FuzzOperation::OneArg(FuzzOneArg::Not, arg) => {
            let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
            let is_truthy = !truthy(Rc::new(output));
            Ok(SExp::Integer(loc, (is_truthy as u32).to_bigint().unwrap()))
        }
        FuzzOperation::TwoArg(op, a, b) => {
            let a_output = interpret_program(prog, args, bindings, a, steps - 1)?;
            let b_output = interpret_program(prog, args, bindings, b, steps - 1)?;
            match op {
                FuzzTwoArg::Cons => {
                    Ok(SExp::Cons(loc, Rc::new(a_output), Rc::new(b_output)))
                }
                FuzzTwoArg::Equal => {
                    let a_bv = byte_vec_of_sexp(&a_output)?;
                    let b_bv = byte_vec_of_sexp(&b_output)?;
                    let equal = ((a_bv == b_bv) as u32).to_bigint().unwrap();
                    Ok(SExp::Integer(loc, equal))
                }
                FuzzTwoArg::GreaterThanString => {
                    let a_bv = byte_vec_of_sexp(&a_output)?;
                    let b_bv = byte_vec_of_sexp(&b_output)?;
                    let greater = ((a_bv > b_bv) as u32).to_bigint().unwrap();
                    Ok(SExp::Integer(loc, greater))
                }
                FuzzTwoArg::Greater => {
                    let a_n =
                        evaluate_to_number(prog, args, bindings, a, steps - 1)?;
                    let b_n =
                        evaluate_to_number(prog, args, bindings, b, steps - 1)?;
                    let greater = ((a_n > b_n) as u32).to_bigint().unwrap();
                    Ok(SExp::Integer(loc, greater))
                }
                FuzzTwoArg::Lsh => {
                    run_op(
                        loc.clone(),
                        SExp::Atom(loc.clone(), b"lsh".to_vec()),
                        &[a_output, b_output]
                    )
                }
                FuzzTwoArg::Ash => {
                    run_op(
                        loc.clone(),
                        SExp::Atom(loc.clone(), b"ash".to_vec()),
                        &[a_output, b_output]
                    )
                }
                FuzzTwoArg::Logxor => {
                    run_op(
                        loc.clone(),
                        SExp::Atom(loc.clone(), b"logxor".to_vec()),
                        &[a_output, b_output]
                    )
                }
                FuzzTwoArg::Subtract => {
                    let a_n =
                        evaluate_to_number(prog, args, bindings, a, steps - 1)?;
                    let b_n =
                        evaluate_to_number(prog, args, bindings, b, steps - 1)?;
                    Ok(SExp::Integer(loc, a_n - b_n))
                }
                FuzzTwoArg::Divide => {
                    run_op(
                        loc.clone(),
                        SExp::Atom(loc.clone(), b"/".to_vec()),
                        &[a_output, b_output]
                    )
                }
                FuzzTwoArg::Divmod => {
                    run_op(
                        loc.clone(),
                        SExp::Atom(loc.clone(), b"divmod".to_vec()),
                        &[a_output, b_output]
                    )
                }
            }
        }
        FuzzOperation::ThreeArg(FuzzThreeArg::IfCond, a, b, c) => {
            let a_output = interpret_program(prog, args, bindings, a, steps - 1)?;
            let b_output = interpret_program(prog, args, bindings, b, steps - 1)?;
            let c_output = interpret_program(prog, args, bindings, c, steps - 1)?;
            if truthy(Rc::new(a_output)) {
                Ok(b_output)
            } else {
                Ok(c_output)
            }
        }
        FuzzOperation::ThreeArg(FuzzThreeArg::Substr, s, start, end) => {
            let output = interpret_program(prog, args, bindings, &s, steps - 1)?;
            let bv: Vec<u8> =
                byte_vec_of_sexp(&output)?.iter().map(|b| b ^ 0xff).collect();
            let first =
                evaluate_to_number(prog, args, bindings, start, steps - 1)?;
            let last =
                evaluate_to_number(prog, args, bindings, end, steps - 1)?;
            if first < bi_zero() || last < bi_zero() || first > last || last > (bv.len().to_bigint().unwrap()) {
                Err(RunFailure::RunErr(loc, "bad substr".to_string()))
            } else {
                Ok(SExp::Atom(loc, bv.iter().take(last.to_usize().unwrap()).skip(first.to_usize().unwrap()).copied().collect()))
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Sha256, lst) => {
            let loc = Srcloc::start(&"*sha256*".to_string());
            let mut bytes_stream = Stream::new(None);
            for elt in lst.iter() {
                let output = interpret_program(prog, args, bindings, &elt, steps - 1)?;
                let output_bytes = byte_vec_of_sexp(&output)?;
                bytes_stream.write(Bytes::new(Some(BytesFromType::Raw(output_bytes))));
            }
            Ok(SExp::Atom(
                loc,
                sha256(bytes_stream.get_value()).data().clone(),
            ))
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Concat, lst) => {
            let loc = Srcloc::start(&"*sha256*".to_string());
            let mut bytes_stream = Stream::new(None);
            for elt in lst.iter() {
                let output = interpret_program(prog, args, bindings, &elt, steps - 1)?;
                let output_bytes = byte_vec_of_sexp(&output)?;
                bytes_stream.write(Bytes::new(Some(BytesFromType::Raw(output_bytes))));
            }
            Ok(SExp::QuotedString(
                loc,
                b'"',
                bytes_stream.get_value().data().clone()
            ))
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Any, lst) => {
            let mut result = SExp::Integer(loc.clone(), bi_zero());
            for x in lst.iter() {
                if truthy(Rc::new(interpret_program(prog, args, bindings, &x, steps - 1)?)) {
                    result = SExp::Integer(loc.clone(), bi_one());
                }
            }

            Ok(result)
        }
        FuzzOperation::MultiArg(FuzzMultiArg::All, lst) => {
            if lst.is_empty() {
                Ok(SExp::Integer(loc, bi_one()))
            } else {
                do_multi_arg(loc, prog, args, bindings, |a,b| {
                    let new_val = (a != bi_zero() && b != bi_zero()) as u32;
                    new_val.to_bigint().unwrap()
                }, lst, steps - 1)
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Add, lst) => {
            if lst.is_empty() {
                Ok(SExp::Integer(loc, bi_zero()))
            } else {
                do_multi_arg(loc, prog, args, bindings, |a,b| a + b, lst, steps - 1)
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Multiply, lst) => {
            if lst.is_empty() {
                Ok(SExp::Integer(loc, bi_one()))
            } else {
                do_multi_arg(loc, prog, args, bindings, |a,b| a * b, lst, steps - 1)
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Logand, lst) => {
            if lst.is_empty() {
                Ok(SExp::Integer(loc, -1_i32.to_bigint().unwrap()))
            } else {
                do_multi_arg(loc, prog, args, bindings, |a,b| a & b, lst, steps - 1)
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::Logior, lst) => {
            if lst.is_empty() {
                Ok(SExp::Integer(loc, bi_zero()))
            } else {
                do_multi_arg(loc, prog, args, bindings, |a,b| a | b, lst, steps - 1)
            }
        }
        FuzzOperation::MultiArg(FuzzMultiArg::PointAdd, lst) => {
            if lst.is_empty() {
                let mut s = vec![0; 48];
                s[0] = 0xc0;
                Ok(SExp::QuotedString(loc, b'"', s))
            } else {
                let mut outargs = Vec::new();
                for arg in lst.iter() {
                    let output = interpret_program(prog, args, bindings, &arg, steps - 1)?;
                    outargs.push(output);
                }
                run_op(
                    loc.clone(),
                    SExp::Atom(loc.clone(), b"pubkey_for_exp".to_vec()),
                    &outargs
                )
            }
        }
        FuzzOperation::List(lst) => {
            let mut list = SExp::Nil(loc.clone());
            for elt in lst.iter().rev() {
                let output = interpret_program(prog, args, bindings, &elt, steps - 1)?;
                list = SExp::Cons(
                    loc.clone(),
                    Rc::new(output),
                    Rc::new(list)
                );
            }
            Ok(list)
        }
        FuzzOperation::Let(new_bindings, body) => {
            let mut total_bindings = bindings.to_vec();
            total_bindings.push(new_bindings.clone());
            interpret_program(prog, args, &total_bindings, body.borrow(), steps - 1)
        }
        FuzzOperation::Call(fun, call_args) => {
            let called_fun = select_call(*fun, prog);
            let mut reified_args = Vec::new();

            // Interpret all arguments.
            for a in call_args.iter() {
                reified_args.push(interpret_program(prog, args, bindings, a, steps - 1)?);
            }

            // Use reified arguments since we're assuming they're sexp.
            let distributed_args = distribute_args(
                called_fun.1.args.clone(),
                prog,
                bindings,
                &reified_args,
                true,
                0,
            );
            interpret_program(
                &called_fun.1.to_program(prog),
                &distributed_args.1,
                &Vec::new(),
                &called_fun.1.body.clone(),
                steps - 1,
            )
        }
    }
}

impl FuzzProgram {
    pub fn to_sexp(&self) -> SExp {
        let mut body_vec = Vec::new();
        body_vec.push(self.args.to_sexp());
        for f in &self.functions {
            body_vec.push(f.to_sexp(self))
        }
        body_vec.push(self.body.to_sexp(self, &Vec::new()));
        make_operator("mod".to_string(), body_vec)
    }

    pub fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        let srcloc = Srcloc::start(&"*args*".to_string());
        random_args(rng, srcloc, self.args.clone())
    }

    pub fn interpret(&self, args: SExp) -> Result<SExp, RunFailure> {
        interpret_program(self, &args, &Vec::new(), &self.body, MAX_STEPS)
    }
}

fn random_old_program<R: Rng + ?Sized>(rng: &mut R, remaining: usize) -> FuzzOldProgram {
    FuzzOldProgram {
        program: random_program(rng, 0, remaining),
    }
}

impl Distribution<FuzzOldProgram> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOldProgram {
        random_old_program(rng, MAX_LIST_BOUND)
    }
}

pub fn make_random_u64_seed() -> u64 {
    let mut rng = ChaCha8Rng::from_entropy();
    let random_seed = random_atom_name(&mut rng, 10);
    let random_seed_as_bigint =
        number_from_u8(&random_seed) & 0xffffffffffff_u64.to_bigint().unwrap();
    random_seed_as_bigint.to_u64().unwrap()
}
