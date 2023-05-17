use std::borrow::Borrow;
use std::collections::HashSet;
use std::rc::Rc;

use clvmr::allocator::{Allocator, NodePtr};
use clvmr::reduction::EvalErr;

use log::debug;

use crate::classic::clvm::sexp::proper_list;
use crate::compiler::clvm::{convert_from_clvm_rs, convert_to_clvm_rs};
use crate::compiler::compiler::DefaultCompilerOpts;
use crate::compiler::comptypes::{CompilerOpts, HelperForm};
use crate::compiler::frontend::{compile_helperform, recover_arg_type};
use crate::compiler::prims::prims;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{enlist, SExp};
use crate::compiler::srcloc::Srcloc;

lazy_static! {
    pub static ref NOOP_WORDS: HashSet<Vec<u8>> = {
        let mut h = HashSet::new();
        h.insert("coerce".as_bytes().to_vec());
        h.insert("bless".as_bytes().to_vec());
        h.insert("explode".as_bytes().to_vec());
        h.insert("lift".as_bytes().to_vec());
        h.insert("unlift".as_bytes().to_vec());
        h
    };
}

fn run_failure_to_eval_err(sexp: NodePtr, e: &RunFailure) -> EvalErr {
    match e {
        RunFailure::RunExn(l, t) => EvalErr(sexp, format!("{l}: exception: {t}")),
        RunFailure::RunErr(l, t) => EvalErr(sexp, format!("{l}: {t}")),
    }
}

fn flatten_type_level_operators_call(sexp: Rc<SExp>) -> Rc<SExp> {
    if let SExp::Cons(l, a, b) = sexp.borrow() {
        let new_a = flatten_type_level_operators(a.clone());
        let new_b = flatten_type_level_operators_call(b.clone());
        Rc::new(SExp::Cons(l.clone(), new_a, new_b))
    } else {
        flatten_type_level_operators(sexp)
    }
}

fn choose_operator(_l: Srcloc, n: &[u8]) -> Option<Rc<SExp>> {
    for p in prims() {
        if n == p.0 {
            return Some(Rc::new(p.1));
        }
    }

    None
}

fn flatten_type_level_operators(sexp: Rc<SExp>) -> Rc<SExp> {
    match sexp.borrow() {
        SExp::Cons(l, a, b) => {
            if let SExp::Atom(la, n) = a.atomize() {
                if n.len() == 1 {
                    if n[0] == 1 || n[0] == b'q' {
                        return Rc::new(SExp::Cons(
                            l.clone(),
                            Rc::new(SExp::Atom(la, vec![1])),
                            b.clone(),
                        ));
                    } else {
                        let op = choose_operator(la, &n).unwrap_or_else(|| a.clone());
                        return Rc::new(SExp::Cons(
                            l.clone(),
                            op,
                            flatten_type_level_operators_call(b.clone()),
                        ));
                    }
                } else if n.len() == 2 && n[1] == b'*' {
                    let op = choose_operator(la, &[n[0]]).unwrap_or_else(|| a.clone());
                    return Rc::new(SExp::Cons(
                        l.clone(),
                        op,
                        flatten_type_level_operators_call(b.clone()),
                    ));
                } else if NOOP_WORDS.contains(&n) {
                    if let SExp::Cons(_, t, _nil) = b.borrow() {
                        return t.clone();
                    }
                } else {
                    return Rc::new(SExp::Cons(
                        l.clone(),
                        Rc::new(SExp::Atom(la, n)),
                        flatten_type_level_operators_call(b.clone()),
                    ));
                }
            }

            let new_tail = flatten_type_level_operators_call(b.clone());
            Rc::new(SExp::Cons(l.clone(), a.clone(), new_tail))
        }
        _ => sexp.clone(),
    }
}

fn process_helper(
    opts: Rc<dyn CompilerOpts>,
    sexp: NodePtr,
    form: Rc<SExp>,
) -> Result<Vec<Rc<SExp>>, EvalErr> {
    if let Some(lst_) = form.proper_list() {
        let lst: Vec<Rc<SExp>> = lst_.iter().map(|x| Rc::new(x.clone())).collect();
        let head = lst[0].atomize();
        if let SExp::Atom(_, n) = &head {
            if n == &"deftype".as_bytes().to_vec() {
                debug!("deftype");
                let result = compile_helperform(opts.clone(), form.clone())
                    .map_err(|e| EvalErr(sexp, format!("{}: {}", e.0, e.1)))?;
                if let Some(result) = result {
                    debug!("result {:?}", result.new_helpers);
                    let mut result_forms = Vec::new();
                    for f in result.new_helpers.iter() {
                        if matches!(f, HelperForm::Defun(_, _)) {
                            let downstream = process_helper(opts.clone(), sexp, f.to_sexp())?;
                            for h in downstream.iter() {
                                result_forms.push(h.clone());
                            }
                        }
                    }
                    Ok(result_forms)
                } else {
                    Ok(vec![])
                }
            } else if n == &"defun".as_bytes().to_vec() || n == &"defun-inline".as_bytes().to_vec()
            {
                debug!("defun {}", form.to_string());
                let def = untype_definition(opts.clone(), form.loc(), sexp, &lst, 2)?
                    .unwrap_or_else(|| form.clone());
                Ok(vec![def])
            } else {
                Ok(vec![form.clone()])
            }
        } else {
            Ok(vec![form.clone()])
        }
    } else {
        Ok(vec![form.clone()])
    }
}

fn untype_definition(
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
    l: NodePtr,
    converted: &[Rc<SExp>],
    offset: usize,
) -> Result<Option<Rc<SExp>>, EvalErr> {
    let mut use_tail_idx = offset + 1;
    if converted.len() > offset + 2 {
        if let SExp::Atom(_, n2) = &converted[offset + 1].atomize() {
            if n2 == &vec![b':'] || n2 == &vec![b'-', b'>'] {
                // Definitely have a type annotation
                use_tail_idx += 2;
            }
        }
    }

    let arguments = if let Some(typed) = recover_arg_type(converted[offset].clone(), false)
        .map_err(|e| EvalErr(l, format!("{}: {}", e.0, e.1)))?
    {
        typed.stripped_args
    } else {
        converted[offset].clone()
    };

    // Pick up first part of definition
    let mut output_list: Vec<Rc<SExp>> = converted.iter().take(offset).cloned().collect();

    // get args
    output_list.push(arguments);

    // Push stripped helpers
    for c in converted
        .iter()
        .take(converted.len() - 1)
        .skip(use_tail_idx)
    {
        for h in process_helper(opts.clone(), l, c.clone())?.iter() {
            output_list.push(h.clone());
        }
    }

    // Push normalized body
    output_list.push(flatten_type_level_operators(
        converted[converted.len() - 1].clone(),
    ));

    Ok(Some(Rc::new(enlist(loc, &output_list))))
}

fn matches_mod(
    opts: Rc<dyn CompilerOpts>,
    loc: Srcloc,
    l: NodePtr,
    converted: &[Rc<SExp>],
) -> Result<Option<Rc<SExp>>, EvalErr> {
    if converted.len() < 3 {
        return Ok(None);
    }

    if !converted[0].equal_to(&SExp::Atom(converted[0].loc(), "mod".as_bytes().to_vec())) {
        return Ok(None);
    }

    untype_definition(opts.clone(), loc, l, converted, 1)
}

// Remove type annotations in a chialisp mod, giving the helper forms that would
// be synthesized by deftype calls.
//
// Module and function annotation:
// (mod ARGS : T ...)
// (mod ARGS -> T ...)
// Argument annotations:
// (X : T)
// (@ X DEF : T)
//
// A few forms are used in helper code that are explicitly noops:
// coerce, bless, lift, unlift
//
// These are type-punned operators: a*, c*
pub fn untype_code(
    allocator: &mut Allocator,
    loc: Srcloc,
    sexp: NodePtr,
) -> Result<NodePtr, EvalErr> {
    let file_borrowed: &String = loc.file.borrow();
    let opts = Rc::new(DefaultCompilerOpts::new(file_borrowed));
    if let Some(l) = proper_list(allocator, sexp, true) {
        // This is only allowed on (mod ...)
        let mut converted = Vec::new();
        for c in l.iter() {
            converted.push(
                convert_from_clvm_rs(allocator, loc.clone(), *c)
                    .map_err(|e| run_failure_to_eval_err(*c, &e))?,
            );
        }

        if let Some(reformed) = matches_mod(opts, loc.clone(), sexp, &converted)? {
            debug!("reformed {}", reformed.to_string());
            return convert_to_clvm_rs(allocator, reformed)
                .map_err(|e| run_failure_to_eval_err(sexp, &e));
        }
    };

    Ok(sexp)
}
