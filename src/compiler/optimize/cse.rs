use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::compiler::clvm::sha256tree;
use crate::compiler::comptypes::{
    Binding, BindingPattern, BodyForm, CompileErr, DefunData, HelperForm, LetData,
    LetFormInlineHint, LetFormKind,
};
use crate::compiler::gensym::gensym;
use crate::compiler::optimize::bodyform::{
    path_overlap_one_way, replace_in_bodyform, retrieve_bodyform, visit_detect_in_bodyform,
    BodyformPathArc, PathDetectVisitorResult,
};
use crate::compiler::sexp::{decode_string, SExp};

// Common subexpression elimintation.
// catalog subexpressions of the given bodyform and
#[derive(Debug, Clone)]
pub struct CSEInstance {
    pub path: Vec<BodyformPathArc>,
}

#[derive(Debug, Clone)]
pub struct CSEDetection {
    pub hash: Vec<u8>,
    pub subexp: BodyForm,
    pub instances: Vec<CSEInstance>,
}

fn is_constant(bf: &BodyForm) -> bool {
    matches!(
        bf,
        BodyForm::Value(SExp::Nil(_))
            | BodyForm::Value(SExp::Integer(_, _))
            | BodyForm::Value(SExp::QuotedString(_, _, _))
            | BodyForm::Quoted(_)
    )
}

// A detection is fully dominated if every instance of it is used in the same
// other detection.
fn is_fully_dominated(cse: &CSEDetection, detections: &[CSEDetection]) -> bool {
    let mut host_set = HashSet::new();

    for i in cse.instances.iter() {
        for d in detections.iter() {
            if d.hash == cse.hash {
                continue;
            }
            for d_i in d.instances.iter() {
                if path_overlap_one_way(&d_i.path, &i.path) {
                    host_set.insert(d.hash.clone());
                }
            }
        }
    }

    // No overlaps means all uses are unique, otherwise it is fully dominated if
    // if all uses are in the same host.  If there are multiple hosts then it is
    // not fully dominated since we can still deduplicate it among other hosts
    // which are themselves going to be deduplicated.
    host_set.len() == 1
}

pub fn cse_detect(fe: Rc<BodyForm>) -> Result<Vec<CSEDetection>, CompileErr> {
    let found_exprs = visit_detect_in_bodyform(
        &|path, _original, form| {
            // The whole expression isn't a repeat.
            if path.is_empty() {
                return Ok(None);
            }

            // Skip the function name of a call.
            if path[path.len() - 1] == BodyformPathArc::CallArgument(0) {
                return Ok(None);
            }

            // Skip individual variable references.
            if let BodyForm::Value(SExp::Atom(_, _)) = form {
                return Ok(None);
            }

            // Skip cheap constants.
            if is_constant(form) {
                return Ok(None);
            }

            let hash_of = sha256tree(form.to_sexp());
            let res: Result<Option<Vec<u8>>, CompileErr> = Ok(Some(hash_of));
            res
        },
        fe.borrow(),
    )?;

    // Group them by hash since we've renamed variables.
    let mut by_hash: HashMap<Vec<u8>, Vec<PathDetectVisitorResult<Vec<u8>>>> = HashMap::new();
    for expr in found_exprs.iter() {
        if let Some(lst) = by_hash.get_mut(&expr.context) {
            lst.push(expr.clone());
        } else {
            by_hash.insert(expr.context.clone(), vec![expr.clone()]);
        }
    }

    let detections: Vec<CSEDetection> = by_hash
        .into_iter()
        .filter_map(|(k, v)| {
            if v.len() < 2 {
                return None;
            }

            let subexp = v[0].subexp.clone();

            let instances = v
                .into_iter()
                .map(|item| CSEInstance { path: item.path })
                .collect();

            Some(CSEDetection {
                hash: k,
                subexp,
                instances,
            })
        })
        .collect();

    let useful_detections = detections
        .iter()
        .filter(|d| !is_fully_dominated(d, &detections))
        .cloned()
        .collect();

    Ok(useful_detections)
}

// Number of other CSE detections this one depends on.
// We can't apply it until the ones it depends on are applied.
fn number_of_overlaps(detections: &[CSEDetection], cse: &CSEDetection) -> usize {
    cse.instances
        .iter()
        .map(|i: &CSEInstance| {
            detections
                .iter()
                .filter(|d| d.hash != cse.hash)
                .map(|d| {
                    d.instances
                        .iter()
                        .filter(|j: &&CSEInstance| path_overlap_one_way(&i.path, &j.path))
                        .count()
                })
                .sum::<usize>()
        })
        .sum()
}

fn sorted_cse_detections_by_applicability(
    cse_detections: &[CSEDetection],
) -> Vec<(usize, CSEDetection)> {
    let mut detections_with_dependencies: Vec<(usize, CSEDetection)> = cse_detections
        .iter()
        .map(|a| (number_of_overlaps(&cse_detections, a), a.clone()))
        .collect();
    detections_with_dependencies.sort_by(|(a, _), (b, _)| a.cmp(b));
    detections_with_dependencies
}

pub fn cse_optimize_bodyform(h: &HelperForm, d: &DefunData) -> Result<Rc<BodyForm>, CompileErr> {
    let cse_detections = cse_detect(d.body.clone())?;
    eprintln!("cse_detections {}", cse_detections.len());

    // While we have them, apply any detections that overlap no others.
    let mut detections_with_dependencies: Vec<(usize, CSEDetection)> =
        sorted_cse_detections_by_applicability(&cse_detections);

    let mut function_body = d.body.clone();
    let mut new_binding_stack = Vec::new();

    while !detections_with_dependencies.is_empty() {
        let detections_to_apply: Vec<CSEDetection> = detections_with_dependencies
            .iter()
            .take_while(|(c, _d)| *c == 0)
            .map(|(_c, d)| d.clone())
            .collect();
        let keep_detections: Vec<CSEDetection> = detections_with_dependencies
            .iter()
            .skip_while(|(c, _d)| *c == 0)
            .map(|(_c, d)| d.clone())
            .collect();

        // It's an error if applications are deadlocked.
        // I don't think it's possible but this will prevent infinite
        // looping.
        if detections_to_apply.is_empty() && !keep_detections.is_empty() {
            return Err(CompileErr(
                h.loc(),
                format!(
                    "CSE optimization failed in helper {}",
                    decode_string(h.name())
                ),
            ));
        }

        let mut binding_set = Vec::new();

        for d in detections_to_apply.iter() {
            // If for some reason there are none to apply, we can
            // skip it.  That should not be possible.
            if d.instances.is_empty() {
                break;
            }

            // All detections should have been transformed equally.
            // Therefore, we can pick one out and use its form.
            //
            // These might have changed from when they were detected
            // because other common subexpressions were substuted.
            let prototype_instance = if let Some(r) =
                retrieve_bodyform(&d.instances[0].path, &function_body, &|b: &BodyForm| {
                    b.clone()
                }) {
                r
            } else {
                return Err(CompileErr(
                    h.loc(),
                    format!(
                        "CSE Error in {}: could not find form to replace for path {:?}",
                        decode_string(h.name()),
                        d.instances[0].path
                    ),
                ));
            };

            // We'll assign a fresh variable for each of the detections
            // that are applicable now.
            let new_variable_name = gensym(b"cse".to_vec());
            let new_variable_bf = BodyForm::Value(SExp::Atom(
                prototype_instance.loc(),
                new_variable_name.clone(),
            ));

            let replacement_spec: Vec<PathDetectVisitorResult<()>> = d
                .instances
                .iter()
                .map(|i| PathDetectVisitorResult {
                    path: i.path.clone(),
                    subexp: new_variable_bf.clone(),
                    context: (),
                })
                .collect();

            if let Some(res) = replace_in_bodyform(
                &replacement_spec,
                function_body.borrow(),
                &|v: &PathDetectVisitorResult<()>, _b| v.subexp.clone(),
            ) {
                function_body = Rc::new(res);
            } else {
                return Err(CompileErr(
                    h.loc(),
                    format!(
                        "cse replacement failed in helper {}, which shouldn't be possible",
                        decode_string(h.name())
                    ),
                ));
            }

            // Put aside the definition in this binding set.
            binding_set.push((new_variable_name, prototype_instance));

            detections_with_dependencies = sorted_cse_detections_by_applicability(&keep_detections);
        }

        new_binding_stack.push(
            binding_set
                .iter()
                .map(|(name, body)| {
                    let name_atom = SExp::Atom(body.loc(), name.clone());
                    Rc::new(Binding {
                        loc: body.loc(),
                        nl: body.loc(),
                        pattern: BindingPattern::Complex(Rc::new(name_atom)),
                        body: Rc::new(body.clone()),
                    })
                })
                .collect(),
        );
    }

    // All CSE replacements are done.  We unwind the new bindings
    // into a stack of parallel let forms.
    for binding_list in new_binding_stack.into_iter() {
        function_body = Rc::new(BodyForm::Let(
            LetFormKind::Parallel,
            Box::new(LetData {
                loc: function_body.loc(),
                kw: None,
                inline_hint: Some(LetFormInlineHint::NonInline(h.loc())),
                bindings: binding_list,
                body: function_body,
            }),
        ));
    }

    Ok(function_body)
}
