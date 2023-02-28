use std::borrow::Borrow;
use std::rc::Rc;

use num_bigint::ToBigInt;

use crate::compiler::clvm::truthy;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts, LambdaData, PrimaryCodegen};
use crate::compiler::evaluate::{make_operator1, make_operator2};
use crate::compiler::frontend::compile_bodyform;
use crate::compiler::sexp::{enlist, SExp};
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

fn find_and_compose_captures(
    opts: Rc<dyn CompilerOpts>,
    sexp: &SExp,
) -> Result<(Rc<SExp>, Rc<SExp>, Rc<BodyForm>), CompileErr> {
    let mut args = Rc::new(sexp.clone());
    let mut capture_args = Rc::new(SExp::Nil(sexp.loc()));
    let mut captures = Rc::new(BodyForm::Quoted(SExp::Nil(sexp.loc())));
    if let SExp::Cons(_, l, r) = sexp {
        if let SExp::Cons(_, head, rest) = l.borrow() {
            if let SExp::Atom(_, name) = head.borrow() {
                if name == b"&" {
                    args = r.clone();
                    capture_args = rest.clone();
                    captures = make_captures(opts, rest.clone())?;
                }
            }
        }
    }

    Ok((
        args,
        capture_args,
        captures,
    ))
}

fn make_call(loc: Srcloc, head: &str, args: &[BodyForm]) -> BodyForm {
    let mut use_vec: Vec<Rc<BodyForm>> = args.iter().cloned().map(Rc::new).collect();
    use_vec.insert(
        0,
        Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), head))),
    );
    BodyForm::Call(loc, use_vec)
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
pub fn lambda_codegen(opts: Rc<dyn CompilerOpts>, ldata: &LambdaData) -> Result<BodyForm, CompileErr> {
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

    let compose_captures = make_cons(ldata.loc.clone(), Rc::new(quote_atom.clone()), ldata.captures.clone());
    let quoted_code = make_cons(ldata.loc.clone(), Rc::new(quote_atom.clone()), ldata.body.clone());

    let lambda_output = make_call(
        ldata.loc.clone(),
        "list",
        &[
            apply_atom,
            quoted_code,
            make_call(
                ldata.loc.clone(),
                "list",
                &[
                    cons_atom.clone(),
                    make_cons(ldata.loc.clone(), Rc::new(quote_atom), retrieve_left_env),
                    make_call(
                        ldata.loc.clone(),
                        "list",
                        &[cons_atom, compose_captures, whole_env],
                    ),
                ],
            ),
        ],
    );
    Ok(lambda_output)
}

pub fn handle_lambda(opts: Rc<dyn CompilerOpts>, kw_loc: Option<Srcloc>, loc: Srcloc, v: &[SExp]) -> Result<BodyForm, CompileErr> {
    if v.len() < 2 {
        return Err(CompileErr(
            v[0].loc(),
            "Must provide at least arguments and body to lambda".to_string(),
        ));
    }

    let (args, capture_args, captures) = find_and_compose_captures(opts.clone(), &v[0])?;
    let combined_captures_and_args = Rc::new(SExp::Cons(args.loc(), capture_args.clone(), args.clone()));

    let rolled_elements_vec: Vec<Rc<SExp>> = v.iter().skip(1).map(|x| Rc::new(x.clone())).collect();
    let body_list = enlist(v[0].loc(), rolled_elements_vec);

    // Make the mod form
    let mod_form_data = Rc::new(SExp::Cons(
        v[0].loc(),
        Rc::new(SExp::atom_from_string(v[0].loc(), "mod+")),
        Rc::new(SExp::Cons(args.loc(), combined_captures_and_args.clone(), Rc::new(body_list))),
    ));

    // Requires captures
    let subparse = compile_bodyform(opts, mod_form_data)?;
    Ok(BodyForm::Lambda(LambdaData {
        loc: v[0].loc(),
        kw: kw_loc,
        args: args.clone(),
        capture_args: capture_args.clone(),
        captures: captures,
        body: Rc::new(subparse)
    }))
}
