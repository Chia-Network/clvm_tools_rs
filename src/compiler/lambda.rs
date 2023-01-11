use std::borrow::Borrow;
use std::rc::Rc;

use crate::compiler::clvm::truthy;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompilerOpts};
use crate::compiler::evaluate::make_operator2;
use crate::compiler::frontend::{compile_bodyform, frontend};
use crate::compiler::sexp::SExp;

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
) -> Result<(Rc<SExp>, Option<Rc<BodyForm>>), CompileErr> {
    if let SExp::Cons(cl, l, r) = sexp {
        if let SExp::Cons(_, head, rest) = l.borrow() {
            if let SExp::Atom(_, name) = head.borrow() {
                if name == b"&" {
                    let captures = make_captures(opts, rest.clone())?;
                    return Ok((
                        Rc::new(SExp::Cons(cl.clone(), rest.clone(), r.clone())),
                        Some(captures),
                    ));
                }
            }
        }
    }

    Ok((Rc::new(sexp.clone()), None))
}

//
// Lambda
//
// (lambda ((= captures) arguments)
//   (body)
//   )
//
// Yields:
//
// M = (mod ((captures) arguments) (body))
// (qq (a (unquote M) (c (unquote captures) @)))
pub fn handle_lambda(opts: Rc<dyn CompilerOpts>, v: &[SExp]) -> Result<BodyForm, CompileErr> {
    let (args, captures) = find_and_compose_captures(opts.clone(), &v[0])?;

    let mod_form_data = Rc::new(SExp::Cons(
        v[0].loc(),
        Rc::new(SExp::atom_from_string(v[0].loc(), "mod")),
        Rc::new(SExp::Cons(
            args.loc(),
            args.clone(),
            Rc::new(SExp::Cons(
                v[1].loc(),
                Rc::new(v[1].clone()),
                Rc::new(SExp::Nil(v[1].loc())),
            )),
        )),
    ));

    if let Some(captures) = &captures {
        // Requires captures
        let subparse = frontend(opts, &[mod_form_data])?;
        let module = BodyForm::Mod(v[0].loc(), subparse);

        let lambda_output = BodyForm::Call(
            v[0].loc(),
            vec![
                Rc::new(BodyForm::Value(SExp::atom_from_string(v[0].loc(), "list"))),
                Rc::new(BodyForm::Quoted(SExp::Atom(v[0].loc(), vec![2]))),
                Rc::new(make_operator2(
                    &v[0].loc(),
                    "c".to_string(),
                    Rc::new(BodyForm::Quoted(SExp::Atom(v[0].loc(), vec![1]))),
                    Rc::new(module),
                )),
                Rc::new(BodyForm::Call(
                    v[0].loc(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::atom_from_string(v[0].loc(), "list"))),
                        Rc::new(BodyForm::Quoted(SExp::Atom(v[0].loc(), vec![4]))),
                        Rc::new(make_operator2(
                            &v[0].loc(),
                            "c".to_string(),
                            Rc::new(BodyForm::Value(SExp::Atom(v[0].loc(), vec![1]))),
                            captures.clone(),
                        )),
                        Rc::new(BodyForm::Quoted(SExp::Atom(v[0].loc(), vec![1]))),
                    ],
                )),
            ],
        );

        Ok(lambda_output)
    } else {
        // No captures
        let subparse = frontend(opts, &[mod_form_data])?;
        Ok(BodyForm::Mod(v[0].loc(), subparse))
    }
}
