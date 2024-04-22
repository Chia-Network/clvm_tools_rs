use std::borrow::Borrow;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};

use crate::compiler::clvm::truthy;
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{
    Binding, BindingPattern, BodyForm, CompileErr, CompilerOpts, LambdaData,
};
use crate::compiler::evaluate::make_operator2;
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;
use crate::util::Number;

fn make_captures(opts: Rc<dyn CompilerOpts>, sexp: Rc<SExp>) -> Result<Rc<BodyForm>, CompileErr> {
    if let SExp::Cons(l, f, r) = sexp.borrow() {
        Ok(Rc::new(make_operator2(
            l,
            "c".to_string(),
            make_captures(opts.clone(), f.clone())?,
            make_captures(opts, r.clone())?,
        )))
    } else if !truthy(sexp.clone()) {
        Ok(Rc::new(BodyForm::Quoted(SExp::Nil(sexp.loc()))))
    } else {
        Ok(Rc::new(compile_bodyform(opts, sexp)?))
    }
}

struct FoundLambdaCaptures {
    args: Rc<SExp>,
    capture_args: Rc<SExp>,
    captures: Rc<BodyForm>,
}

fn find_and_compose_captures(
    opts: Rc<dyn CompilerOpts>,
    sexp: &SExp,
) -> Result<FoundLambdaCaptures, CompileErr> {
    let mut found = FoundLambdaCaptures {
        args: Rc::new(sexp.clone()),
        capture_args: Rc::new(SExp::Nil(sexp.loc())),
        captures: Rc::new(BodyForm::Quoted(SExp::Nil(sexp.loc()))),
    };
    if let SExp::Cons(_, l, r) = sexp {
        if let SExp::Cons(_, head, rest) = l.borrow() {
            if let SExp::Atom(_, name) = head.borrow() {
                if name == b"&" {
                    found.args = r.clone();
                    found.capture_args = rest.clone();
                    found.captures = make_captures(opts, rest.clone())?;
                }
            }
        }
    }

    Ok(found)
}

fn make_operator(loc: Srcloc, op: u8, arg1: Rc<BodyForm>, arg2: Rc<BodyForm>) -> BodyForm {
    BodyForm::Call(
        loc.clone(),
        vec![
            Rc::new(BodyForm::Value(SExp::Integer(loc, op.to_bigint().unwrap()))),
            arg1,
            arg2,
        ],
        // Tail safe: creates a primitive.
        None,
    )
}

pub fn make_cons(loc: Srcloc, arg1: Rc<BodyForm>, arg2: Rc<BodyForm>) -> BodyForm {
    make_operator(loc, 4, arg1, arg2)
}

fn make_list(loc: Srcloc, args: &[BodyForm]) -> BodyForm {
    let mut res = BodyForm::Quoted(SExp::Nil(loc.clone()));
    let cons_atom = BodyForm::Value(SExp::Atom(loc.clone(), vec![4]));
    for a in args.iter().rev() {
        res = BodyForm::Call(
            loc.clone(),
            vec![Rc::new(cons_atom.clone()), Rc::new(a.clone()), Rc::new(res)],
            // Tail safe: creating a list with primitives.
            None,
        );
    }
    res
}

//
// Lambda
//
// (lambda ((& captures) arguments)
//   (body)
//   )
//
// Yields:
//
// (list 2
//    (c 1 <name>)
//    (list 4 (list 4 (c 1 compose_captures) @))
//    )
//
pub fn lambda_codegen(name: &[u8], ldata: &LambdaData) -> Result<BodyForm, CompileErr> {
    // Code to retrieve and quote the captures.
    let quote_atom = BodyForm::Value(SExp::Integer(ldata.loc.clone(), bi_one()));
    let apply_atom = BodyForm::Value(SExp::Integer(ldata.loc.clone(), 2_u32.to_bigint().unwrap()));
    let cons_atom = BodyForm::Value(SExp::Integer(ldata.loc.clone(), 4_u32.to_bigint().unwrap()));
    let whole_env = quote_atom.clone();

    let compose_captures = make_cons(
        ldata.loc.clone(),
        Rc::new(quote_atom.clone()),
        ldata.captures.clone(),
    );

    let lambda_output = make_list(
        ldata.loc.clone(),
        &[
            apply_atom,
            make_cons(
                ldata.loc.clone(),
                Rc::new(quote_atom),
                Rc::new(BodyForm::Value(SExp::Atom(
                    ldata.loc.clone(),
                    name.to_vec(),
                ))),
            ),
            make_list(ldata.loc.clone(), &[cons_atom, compose_captures, whole_env]),
        ],
    );
    Ok(lambda_output)
}

pub fn handle_lambda(
    opts: Rc<dyn CompilerOpts>,
    site_loc: Srcloc,
    kw_loc: Option<Srcloc>,
    v: &[SExp],
) -> Result<BodyForm, CompileErr> {
    if v.len() < 2 {
        return Err(CompileErr(
            site_loc,
            "Must provide at least arguments and body to lambda".to_string(),
        ));
    }

    let found = find_and_compose_captures(opts.clone(), &v[0])?;

    // Requires captures
    let subparse = compile_bodyform(opts, Rc::new(v[1].clone()))?;

    Ok(BodyForm::Lambda(Box::new(LambdaData {
        loc: v[0].loc(),
        kw: kw_loc,
        args: found.args.clone(),
        capture_args: found.capture_args.clone(),
        captures: found.captures,
        body: Rc::new(subparse),
    })))
}

// Used during type elaboration.  This generates a path of f and r operators into
// the single unary argument of the lambda to extract a specific binding.
fn generate_get_from_var(mask: Number, target_path: Number, arg: Rc<BodyForm>) -> Rc<BodyForm> {
    let two = 2_u32.to_bigint().unwrap();
    if mask.clone() * two.clone() > target_path {
        // Found where we're going
        return arg;
    }
    let is_right = mask.clone() & target_path.clone() != bi_zero();
    let new_op = if is_right { b"r" } else { b"f" };
    let new_body = Rc::new(BodyForm::Call(
        arg.loc(),
        vec![
            Rc::new(BodyForm::Value(SExp::Atom(arg.loc(), new_op.to_vec()))),
            arg.clone(),
        ],
        // Tail safe: generating a primitive.
        None,
    ));
    generate_get_from_var(mask * two, target_path, new_body)
}

// Recurse over the argument bindings of a lambda and generate Binding objects
// for a let form which binds the multiple destructured arguments (virtually)
// from the literal unary argument.
fn form_lambda_bindings_inner(
    bindings: &mut Vec<Rc<Binding>>,
    arg: Rc<SExp>,
    mask: Number,
    path: Number,
    args: Rc<SExp>,
) {
    match args.borrow() {
        SExp::Cons(_, l, r) => {
            if let Some((name, farther)) = is_at_capture(l.clone(), r.clone()) {
                form_lambda_bindings_inner(
                    bindings,
                    arg.clone(),
                    mask.clone(),
                    path.clone(),
                    Rc::new(SExp::Atom(args.loc(), name.to_vec())),
                );
                form_lambda_bindings_inner(bindings, arg, mask, path, farther);
                return;
            }
            let right_path = path.clone() | mask.clone();
            let new_mask = mask * 2_u32.to_bigint().unwrap();
            form_lambda_bindings_inner(bindings, arg.clone(), new_mask.clone(), path, l.clone());
            form_lambda_bindings_inner(bindings, arg, new_mask, right_path, r.clone());
        }
        SExp::Atom(l, _a) => {
            let target_path = path | mask;
            let arg_borrowed: &SExp = arg.borrow();
            let body = generate_get_from_var(
                bi_one(),
                target_path,
                Rc::new(BodyForm::Value(arg_borrowed.clone())),
            );
            bindings.push(Rc::new(Binding {
                nl: l.clone(),
                loc: l.clone(),
                pattern: BindingPattern::Complex(args),
                body,
            }));
        }
        _ => {}
    }
}

/// For typing: let the argument be a single argument.
/// for each argument in the environment, add a binding to a let that retrieves
/// it from the argument type.
pub fn form_lambda_bindings(arg_name: &[u8], args: Rc<SExp>) -> Vec<Rc<Binding>> {
    let mut bindings = Vec::new();
    let arg = Rc::new(SExp::Atom(args.loc(), arg_name.to_vec()));
    form_lambda_bindings_inner(&mut bindings, arg, bi_one(), bi_zero(), args);
    bindings
}
