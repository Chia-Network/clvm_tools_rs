use num_bigint::ToBigInt;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::codegen::generate_expr_code;
use crate::compiler::comptypes::{
    BodyForm,
    CompiledCode,
    CompileErr,
    CompilerOpts,
    InlineFunction,
    PrimaryCodegen
};
use crate::compiler::sexp::{
    SExp,
    decode_string
};
use crate::compiler::srcloc::Srcloc;

use crate::util::{
    Number,
    u8_from_number
};

#[derive(Clone)]
struct InlineArgPath {
    name: Vec<u8>,
    path: Number
}

#[derive(Clone)]
enum InlineArgsSelect {
    This(Vec<u8>),
    Paths(Vec<InlineArgPath>)
}

#[derive(Clone)]
enum InlineArgsType {
    Whole(Vec<u8>),
    List(Vec<InlineArgsSelect>)
}

fn at_form(loc: Srcloc, path: Number) -> Rc<BodyForm> {
    Rc::new(BodyForm::Call(loc.clone(), vec!(
        Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), &"@".to_string()))),
        Rc::new(BodyForm::Value(SExp::Integer(loc.clone(), path.clone())))
    )))
}

fn explore_arg_paths(arg: Rc<SExp>) -> Vec<InlineArgPath> {
    match arg.borrow() {
        SExp::Nil(_) => Vec::new(),
        SExp::QuotedString(_,_,a) => Vec::new(),
        SExp::Atom(_,a) => vec!(InlineArgPath { name: a.clone(), path: bi_one() }),
        SExp::Integer(_,i) => vec!(InlineArgPath { name: u8_from_number(i.clone()), path: bi_one() }),
        SExp::Cons(_,a,b) => {
            let mut first_paths: Vec<InlineArgPath> =
                explore_arg_paths(a.clone()).iter().map(|x| {
                    InlineArgPath {
                        name: x.name.clone(),
                        path: x.path.clone() * 2_i32.to_bigint().unwrap()
                    }
                }).collect();
            let mut rest_paths: Vec<InlineArgPath> =
                explore_arg_paths(b.clone()).iter().map(|x| {
                    InlineArgPath {
                        name: x.name.clone(),
                        path: bi_one() + x.path.clone() * 2_i32.to_bigint().unwrap()
                    }
                }).collect();
            first_paths.append(&mut rest_paths);
            first_paths
        }
    }
}

fn classify_inline_args(loc: Srcloc, args: Rc<SExp>) -> Result<InlineArgsType, CompileErr> {
    let mut arg_look = args.clone();
    let mut arg_list = Vec::new();

    loop {
        match arg_look.borrow() {
            SExp::Nil(_) => { return Ok(InlineArgsType::List(arg_list)); },
            SExp::Cons(_,a,b) => {
                match a.borrow() {
                    SExp::Nil(_) => {
                        arg_list.push(InlineArgsSelect::This(Vec::new()));
                        arg_look = b.clone();
                    },
                    SExp::Cons(l,_,_) => {
                        let paths = explore_arg_paths(a.clone());
                        arg_list.push(InlineArgsSelect::Paths(paths));
                        arg_look = b.clone();
                    },
                    SExp::Atom(_,a) => {
                        if a.len() == 0 {
                            return Ok(InlineArgsType::List(arg_list));
                        }

                        arg_list.push(InlineArgsSelect::This(a.clone()));
                        arg_look = b.clone();
                    },
                    _ => {
                        break;
                    }
                }
            },
            SExp::Atom(_,a) => { return Ok(InlineArgsType::Whole(a.clone())); }
            _ => {
                break;
            }
        }
    }

    return Err(CompileErr(loc.clone(), format!("inappropriate arg form {} in args {}", arg_look.to_string(), args.to_string())));
}

fn replace_in_inline_expr(
    loc: Srcloc,
    arg_lookup: &HashMap<Vec<u8>, Rc<BodyForm>>,
    expr: Rc<BodyForm>
) -> Result<Rc<BodyForm>, CompileErr> {
    match expr.borrow() {
        BodyForm::Let(l,bindings,body) => {
            Err(CompileErr(loc.clone(), "let binding should have been hoisted before optimization".to_string()))
        },
        BodyForm::Quoted(v) => Ok(expr.clone()),
        BodyForm::Call(l,args) => {
            let mut new_args = Vec::new();
            for i in 0..args.len() {
                if i == 0 {
                    new_args.push(args[i].clone());
                } else {
                    let replaced = replace_in_inline_expr(args[i].loc(), arg_lookup, args[i].clone())?;
                    new_args.push(replaced);
                }
            }
            Ok(Rc::new(BodyForm::Call(l.clone(), new_args)))
        },
        BodyForm::Value(SExp::Atom(_,a)) => {
            arg_lookup.get(a).map(|x| Ok(x.clone())).unwrap_or_else(|| Ok(expr.clone()))
        },
        BodyForm::Value(SExp::QuotedString(_,_,s)) => Ok(expr.clone()),
        BodyForm::Value(SExp::Integer(_,i)) => {
            let possible_name = u8_from_number(i.clone());
            arg_lookup.get(&possible_name).map(|x| Ok(x.clone())).unwrap_or_else(|| Ok(expr.clone()))
        }
        BodyForm::Value(v) => Ok(expr.clone())
    }
}

// Destructuring version.
fn create_args_alist(
    loc: Srcloc,
    args: &Vec<InlineArgsSelect>,
    arglist: &Vec<Rc<BodyForm>>
) -> HashMap<Vec<u8>, Rc<BodyForm>> {
    let mut arg_lookup = HashMap::new();

    for i in 0..args.len() {
        match &args[i] {
            InlineArgsSelect::This(n) => {
                arg_lookup.insert(n.clone(), arglist[i].clone());
            },
            InlineArgsSelect::Paths(p) => {
                for path in p.iter() {
                    arg_lookup.insert(path.name.clone(), Rc::new(
                        BodyForm::Call(loc.clone(), vec!(
                            Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), &"a".to_string()))),
                            at_form(loc.clone(), path.path.clone()),
                            arglist[i].clone()
                        ))
                    ));
                }
            }
        }
    }
    arg_lookup
}

fn synthesize_args(arg_: Rc<SExp>) -> Vec<Rc<BodyForm>> {
    let mut start = 5_i32.to_bigint().unwrap();
    let mut result = Vec::new();
    let mut arg = arg_.clone();
    loop {
        match arg.borrow() {
            SExp::Cons(l,_,b) => {
                result.push(at_form(l.clone(), start.clone()));
                start = bi_one() + start.clone() * 2_i32.to_bigint().unwrap();
                arg = b.clone();
            },
            _ => { return result; }
        }
    }
}

pub fn replace_in_inline(
    allocator: &mut Allocator,
    runner: Rc<dyn TRunProgram>,
    opts: Rc<dyn CompilerOpts>,
    compiler: &PrimaryCodegen,
    loc: Srcloc,
    name: Vec<u8>,
    inline: &InlineFunction,
    args_: Option<&Vec<Rc<BodyForm>>>
) -> Result<CompiledCode, CompileErr> {
    let mut arg_lookup = HashMap::new();
    let args_type = classify_inline_args(loc.clone(), inline.args.clone())?;

    let args = args_.map(|x| x.clone()).unwrap_or_else(|| synthesize_args(inline.args.clone()));

    let make_consed_args = || {
        let mut arg_form = Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone())));

        for i_reverse in 0..args.len() {
            let i = args.len() - i_reverse - 1;
            arg_form = Rc::new(BodyForm::Call(loc.clone(), vec!(
                Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), &"c".to_string()))),
                args[i].clone(),
                arg_form.clone()
            )));
        }

        arg_form
    };

    match args_type {
        InlineArgsType::Whole(name) => {
            // The given name receives a consed set of all arguments.
            let arg_form = make_consed_args();
            arg_lookup.insert(name.clone(), arg_form.clone());
        },
        InlineArgsType::List(alist) => {
            // Most common case: arguments are presented as a list:
            // we take each argument and put it in arg_lookup.
            if alist.len() != args.len() {
                return Err(CompileErr(loc.clone(), format!("wrong number of parameters for argument list of function {}, want {} given {}", decode_string(&name), alist.len(), args.len())));
            }

            arg_lookup = create_args_alist(loc.clone(), &alist, &args);
        }
    }

    let final_expr = replace_in_inline_expr(loc.clone(), &arg_lookup, inline.body.clone())?;
    generate_expr_code(
        allocator,
        runner,
        opts,
        compiler,
        final_expr
    )
}
