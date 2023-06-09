use std::borrow::Borrow;
use std::cmp::min;
use std::rc::Rc;

use crate::compiler::comptypes::{Binding, BodyForm, CompileForm, LambdaData, LetData};

// Rewriting and matching on bodyforms.
// Allows a convenient bodyform path description.

/// A path in a bodyform.  Allows us to find and potentially replace the bodyform
/// in a larger expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyformPathArc {
    LetBinding(usize),   // In (let ((a 1) (b 2)) LetBinding(1) points to 2
    CallArgument(usize), // in (x0 x1 x2 x3 x4 x5) CallArgument(3) points to x3
    BodyOf,              // In the body of a lambda, mod or let.
}

/// True if b is contained in a.
pub fn path_overlap_one_way(a: &[BodyformPathArc], b: &[BodyformPathArc]) -> bool {
    let a_len = a.len();
    let b_len = b.len();

    // a is longer than b, so b can't be in a.
    if a_len > b_len {
        return false;
    }

    let iter_until = min(a.len(), b.len());
    for idx in 0..iter_until {
        if a[idx] != b[idx] {
            // They diverged.
            return false;
        }
    }

    true
}

/// Determines whether a and b conflict (a is a superset of b or vice versa).
pub fn path_overlap(a: &[BodyformPathArc], b: &[BodyformPathArc]) -> bool {
    path_overlap_one_way(a, b) || path_overlap_one_way(b, a)
}

/// A single valid result from visit_detect_in_bodyform noting the path to the
/// bodyform, the form itself and the returned context from the visitor function.
#[derive(Clone)]
pub struct PathDetectVisitorResult<R> {
    pub path: Vec<BodyformPathArc>,
    pub subexp: BodyForm,
    pub context: R,
}

/// Visit over a bodyform offering the path, original and current bodyforms to the
/// visitor.  The vistor returns Ok(None) to just go on, Ok(Some(R)) to accept and
/// record the path and can return error to abort.
fn visit_detect_in_bodyform_inner<F, R, E>(
    path: &mut Vec<BodyformPathArc>,
    res: &mut Vec<PathDetectVisitorResult<R>>,
    f: &F,
    original: &BodyForm,
    bf: &BodyForm,
) -> Result<(), E>
where
    F: Fn(&[BodyformPathArc], &BodyForm, &BodyForm) -> Result<Option<R>, E>,
{
    let path_idx = path.len();
    match bf {
        BodyForm::Call(_l, args) => {
            for (i, a) in args.iter().enumerate() {
                path.push(BodyformPathArc::CallArgument(i));
                visit_detect_in_bodyform_inner(path, res, f, original, a)?;
                path.truncate(path_idx);
            }
        }
        BodyForm::Let(_k, b) => {
            for (i, a) in b.bindings.iter().enumerate() {
                path.push(BodyformPathArc::LetBinding(i));
                visit_detect_in_bodyform_inner(path, res, f, original, a.body.borrow())?;
                path.truncate(path_idx);
            }
            path.push(BodyformPathArc::BodyOf);
            visit_detect_in_bodyform_inner(path, res, f, original, b.body.borrow())?;
            path.truncate(path_idx);
        }
        BodyForm::Lambda(ldata) => {
            path.push(BodyformPathArc::BodyOf);
            visit_detect_in_bodyform_inner(path, res, f, original, ldata.body.borrow())?;
            path.truncate(path_idx);
        }
        BodyForm::Mod(_, form) => {
            path.push(BodyformPathArc::BodyOf);
            visit_detect_in_bodyform_inner(path, res, f, original, form.exp.borrow())?;
            path.truncate(path_idx);
        }
        _ => {}
    }

    // And for this node, call the visitor.
    if let Some(r) = f(path, original, bf)? {
        res.push(PathDetectVisitorResult {
            path: path.clone(),
            subexp: bf.clone(),
            context: r,
        });
    }

    Ok(())
}

pub fn visit_detect_in_bodyform<F, R, E>(
    f: &F,
    bf: &BodyForm,
) -> Result<Vec<PathDetectVisitorResult<R>>, E>
where
    F: Fn(&[BodyformPathArc], &BodyForm, &BodyForm) -> Result<Option<R>, E>,
{
    let mut path = vec![];
    let mut res = vec![];
    visit_detect_in_bodyform_inner(&mut path, &mut res, f, bf, bf)?;
    Ok(res)
}

#[allow(clippy::too_many_arguments)]
fn replace_in_bodyform_inner_list<'a, L, P, F, F1, G, H, R>(
    current_path: &mut Vec<BodyformPathArc>,
    replacements: &[PathDetectVisitorResult<R>],
    list_of: &'a [L],
    make_path_comp: &P,
    extract_body: &G,
    compose_wrap: &H,
    make_f: &F1,
    f: &F,
) -> BodyForm
where
    R: Clone,
    L: Clone + 'a,
    P: Fn(usize) -> BodyformPathArc,
    F1: Fn(Vec<L>) -> BodyForm,
    G: Fn(&'a L) -> &'a BodyForm,
    H: Fn(&'a L, BodyForm) -> L,
    F: Fn(&PathDetectVisitorResult<R>, &BodyForm) -> BodyForm,
{
    let mut collection = vec![];
    let path_idx = current_path.len();
    for (i, a) in list_of.iter().enumerate() {
        current_path.push(make_path_comp(i));

        // Continue only with potentially matching replacements.
        let pass_on_replacements: Vec<PathDetectVisitorResult<R>> = replacements
            .iter()
            .filter(|r| path_overlap(current_path, &r.path))
            .cloned()
            .collect();

        // No replacements down this argument.
        if pass_on_replacements.is_empty() {
            collection.push(a.clone());
            current_path.truncate(path_idx);
            continue;
        }

        collection.push(compose_wrap(
            a,
            replace_in_bodyform_subset(current_path, &pass_on_replacements, extract_body(a), f),
        ));
        current_path.truncate(path_idx);
    }
    make_f(collection)
}

fn replace_in_bodyform_inner_body<F, F1, R>(
    current_path: &mut Vec<BodyformPathArc>,
    replacements: &[PathDetectVisitorResult<R>],
    new_path_elt: BodyformPathArc,
    outer_body: &BodyForm,
    inner_body: &BodyForm,
    make_f: &F1,
    f: &F,
) -> BodyForm
where
    R: Clone,
    F1: Fn(BodyForm) -> BodyForm,
    F: Fn(&PathDetectVisitorResult<R>, &BodyForm) -> BodyForm,
{
    let path_idx = current_path.len();
    current_path.push(new_path_elt);
    let pass_on_replacements: Vec<PathDetectVisitorResult<R>> = replacements
        .iter()
        .filter(|r| path_overlap(current_path, &r.path))
        .cloned()
        .collect();

    if pass_on_replacements.is_empty() {
        current_path.truncate(path_idx);
        return outer_body.clone();
    }

    let new_binding_body =
        replace_in_bodyform_subset(current_path, &pass_on_replacements, inner_body, f);
    current_path.truncate(path_idx);
    make_f(new_binding_body)
}

/// For some partially matched subset of the replacement set at index idx in their
/// paths, do the child replacements.
fn replace_in_bodyform_subset<F, R>(
    current_path: &mut Vec<BodyformPathArc>,
    replacements: &[PathDetectVisitorResult<R>],
    bf: &BodyForm,
    f: &F,
) -> BodyForm
where
    R: Clone,
    F: Fn(&PathDetectVisitorResult<R>, &BodyForm) -> BodyForm,
{
    eprintln!("replace_in_bodyform_subset {}", bf.to_sexp());
    // We already checked for overlaps, so there'll be only one if any.
    let exact_match_replacements: Vec<PathDetectVisitorResult<R>> = replacements
        .iter()
        .filter(|r| &r.path == current_path)
        .cloned()
        .collect();

    if !exact_match_replacements.is_empty() {
        // Return the object
        return f(&exact_match_replacements[0], bf);
    }

    match bf {
        BodyForm::Call(l, args) => replace_in_bodyform_inner_list(
            current_path,
            replacements,
            args,
            &BodyformPathArc::CallArgument,
            &|e: &Rc<BodyForm>| e.borrow(),
            &|_w, b| Rc::new(b),
            &|args| BodyForm::Call(l.clone(), args),
            f,
        ),
        BodyForm::Let(k, b) => {
            let path_idx = current_path.len();
            current_path.push(BodyformPathArc::BodyOf);
            let pass_on_replacements: Vec<PathDetectVisitorResult<R>> = replacements
                .iter()
                .filter(|r| path_overlap(current_path, &r.path))
                .cloned()
                .collect();

            let new_lambda_body =
                replace_in_bodyform_subset(current_path, &pass_on_replacements, b.body.borrow(), f);

            current_path.truncate(path_idx);

            replace_in_bodyform_inner_list(
                current_path,
                replacements,
                &b.bindings,
                &BodyformPathArc::LetBinding,
                &|e: &Rc<Binding>| &e.body,
                &|w: &Rc<Binding>, b: BodyForm| {
                    let wb: &Binding = w.borrow();
                    Rc::new(Binding {
                        body: Rc::new(b),
                        ..wb.clone()
                    })
                },
                &|bindings| {
                    BodyForm::Let(
                        k.clone(),
                        Box::new(LetData {
                            bindings,
                            body: Rc::new(new_lambda_body.clone()),
                            ..*b.clone()
                        }),
                    )
                },
                f,
            )
        }
        BodyForm::Lambda(l) => replace_in_bodyform_inner_body(
            current_path,
            replacements,
            BodyformPathArc::BodyOf,
            bf,
            &l.body,
            &|b| {
                BodyForm::Lambda(Box::new(LambdaData {
                    body: Rc::new(b),
                    ..*l.clone()
                }))
            },
            f,
        ),
        BodyForm::Mod(l, m) => replace_in_bodyform_inner_body(
            current_path,
            replacements,
            BodyformPathArc::BodyOf,
            bf,
            &m.exp,
            &|b| {
                BodyForm::Mod(
                    l.clone(),
                    CompileForm {
                        exp: Rc::new(b),
                        ..m.clone()
                    },
                )
            },
            f,
        ),
        _ => bf.clone(),
    }
}

/// Replace subexpressions in a bodyform given a set of PathDetectVisitorResult<_>.
pub fn replace_in_bodyform<F, R>(
    replacements: &[PathDetectVisitorResult<R>],
    bf: &BodyForm,
    f: &F,
) -> Option<BodyForm>
where
    R: Clone,
    F: Fn(&PathDetectVisitorResult<R>, &BodyForm) -> BodyForm,
{
    if replacements.is_empty() {
        return Some(bf.clone());
    }

    // We should not have any overlapping paths... if we do, that seems like a
    // failure since a replacement would be lost.
    for (i, p) in replacements.iter().enumerate() {
        for q in replacements.iter().skip(i + 1) {
            if path_overlap(&p.path, &q.path) {
                return None; // An overlap
            }
        }
    }

    let mut current_path = vec![];
    // There are no overlaps, start replacing
    Some(replace_in_bodyform_subset(
        &mut current_path,
        replacements,
        bf,
        f,
    ))
}

/// Retrieve bodyform by path
pub fn retrieve_bodyform<F, R>(path: &[BodyformPathArc], mut found: &BodyForm, f: &F) -> Option<R>
where
    F: Fn(&BodyForm) -> R,
{
    for p in path.iter() {
        match p {
            BodyformPathArc::LetBinding(n) => {
                if let BodyForm::Let(_, l) = found {
                    if *n >= l.bindings.len() {
                        return None;
                    }
                    found = l.bindings[*n].body.borrow();
                } else {
                    return None;
                }
            }
            BodyformPathArc::CallArgument(n) => {
                if let BodyForm::Call(_, a) = found {
                    if *n >= a.len() {
                        return None;
                    }
                    found = a[*n].borrow();
                } else {
                    return None;
                }
            }
            BodyformPathArc::BodyOf => match found {
                BodyForm::Let(_, b) => {
                    found = b.body.borrow();
                }
                BodyForm::Lambda(l) => {
                    found = l.body.borrow();
                }
                BodyForm::Mod(_, m) => {
                    found = m.exp.borrow();
                }
                _ => {
                    return None;
                }
            },
        }
    }

    Some(f(found))
}
