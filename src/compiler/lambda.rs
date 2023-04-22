use std::borrow::Borrow;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::compiler::clvm::truthy;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts, LambdaData, PrimaryCodegen};
use crate::compiler::evaluate::{make_operator1, make_operator2};
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

pub fn compose_constant_function_env(compiler: &PrimaryCodegen) -> Result<Rc<SExp>, CompileErr> {
    match compiler.env.borrow() {
        SExp::Cons(_, left, _) => Ok(left.clone()),
        _ => Ok(Rc::new(SExp::Nil(compiler.env.loc()))),
    }
}

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
            Rc::new(BodyForm::Value(SExp::Atom(loc, vec![op]))),
            arg1,
            arg2,
        ],
    )
}

fn make_cons(loc: Srcloc, arg1: Rc<BodyForm>, arg2: Rc<BodyForm>) -> BodyForm {
    make_operator(loc, 4, arg1, arg2)
}

fn make_list(loc: Srcloc, args: &[BodyForm]) -> BodyForm {
    let mut res = BodyForm::Quoted(SExp::Nil(loc.clone()));
    let cons_atom = BodyForm::Value(SExp::Atom(loc.clone(), vec![4]));
    for a in args.iter().rev() {
        res = BodyForm::Call(
            loc.clone(),
            vec![Rc::new(cons_atom.clone()), Rc::new(a.clone()), Rc::new(res)],
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
// M = (mod ((captures) arguments) (body))
// (list 2
//    (c 1 (mod ((captures) arguments) body))
//    (list 4 (c 1 (@ 2)) (list 4 (c 1 compose_captures) @))
//    )
//
pub fn lambda_codegen(name: &[u8], ldata: &LambdaData) -> Result<BodyForm, CompileErr> {
    // Requires captures
    // Code to retrieve the left env.
    let retrieve_left_env = Rc::new(make_operator1(
        &ldata.loc,
        "@".to_string(),
        Rc::new(BodyForm::Value(SExp::Integer(
            ldata.loc.clone(),
            2_u32.to_bigint().unwrap(),
        ))),
    ));
    // Code to retrieve and quote the captures.
    let quote_atom = BodyForm::Value(SExp::Atom(ldata.loc.clone(), vec![1]));
    let apply_atom = BodyForm::Value(SExp::Atom(ldata.loc.clone(), vec![2]));
    let cons_atom = BodyForm::Value(SExp::Atom(ldata.loc.clone(), vec![4]));
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
            BodyForm::Value(SExp::Atom(ldata.loc.clone(), name.to_vec())),
            make_list(
                ldata.loc.clone(),
                &[
                    cons_atom.clone(),
                    make_cons(ldata.loc.clone(), Rc::new(quote_atom), retrieve_left_env),
                    make_list(ldata.loc.clone(), &[cons_atom, compose_captures, whole_env]),
                ],
            ),
        ],
    );
    Ok(lambda_output)
}

pub fn handle_lambda(
    opts: Rc<dyn CompilerOpts>,
    kw_loc: Option<Srcloc>,
    v: &[SExp],
) -> Result<BodyForm, CompileErr> {
    if v.len() < 2 {
        return Err(CompileErr(
            v[0].loc(),
            "Must provide at least arguments and body to lambda".to_string(),
        ));
    }

    let found = find_and_compose_captures(opts.clone(), &v[0])?;

    // Requires captures
    let subparse = compile_bodyform(opts, Rc::new(v[1].clone()))?;

    Ok(BodyForm::Lambda(LambdaData {
        loc: v[0].loc(),
        kw: kw_loc,
        args: found.args.clone(),
        capture_args: found.capture_args.clone(),
        captures: found.captures,
        body: Rc::new(subparse),
    }))
}
