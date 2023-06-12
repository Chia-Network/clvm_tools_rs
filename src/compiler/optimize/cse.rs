use std::borrow::Borrow;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::compiler::clvm::sha256tree;
use crate::compiler::comptypes::{
    Binding, BindingPattern, BodyForm, CompileErr, LetData, LetFormInlineHint, LetFormKind,
};
use crate::compiler::evaluate::{is_apply_atom, is_i_atom};
use crate::compiler::gensym::gensym;
use crate::compiler::optimize::bodyform::{
    path_overlap_one_way, replace_in_bodyform, retrieve_bodyform, visit_detect_in_bodyform,
    BodyformPathArc, PathDetectVisitorResult,
};
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;

// Common subexpression elimintation.
// catalog subexpressions of the given bodyform and
#[derive(Debug, Clone)]
pub struct CSEInstance {
    pub path: Vec<BodyformPathArc>,
}

#[derive(Debug, Clone)]
pub struct CSEDetectionWithoutConditions {
    pub hash: Vec<u8>,
    pub subexp: BodyForm,
    pub instances: Vec<CSEInstance>,
}

#[derive(Debug, Clone)]
pub struct CSEDetection {
    pub hash: Vec<u8>,
    pub root: Vec<BodyformPathArc>,
    pub saturated: bool,
    pub subexp: BodyForm,
    pub instances: Vec<CSEInstance>,
}

#[derive(Debug, Clone)]
pub struct CSECondition {
    pub path: Vec<BodyformPathArc>,
    pub canonical: bool,
}

// in a chain of conditions:
//
// (if a *b *c) // Can precompute.
//
// (if a *b (if c (if d *e *f) h)) // Can't precompute; might not be safe in h.
//
// The question we have to ask for each condition is:
// does every branch use the cse?
//
// If it is used in every branch of a condition, then it dominates that condition
// and it can be computed definitely above the condition.
//
// If it is missing from some downstream elements of a condition, then we must
// pass it on as a lambda that can be applied.
//
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
fn is_fully_dominated(cse: &CSEDetectionWithoutConditions, detections: &[CSEDetectionWithoutConditions]) -> bool {
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

pub fn cse_detect(fe: &BodyForm) -> Result<Vec<CSEDetectionWithoutConditions>, CompileErr> {
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

    let detections: Vec<CSEDetectionWithoutConditions> = by_hash
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

            Some(CSEDetectionWithoutConditions {
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
        .map(|a| (number_of_overlaps(cse_detections, a), a.clone()))
        .collect();
    detections_with_dependencies.sort_by(|(a, _), (b, _)| a.cmp(b));
    detections_with_dependencies
}

fn is_one_env_ref(bf: &BodyForm) -> bool {
    bf.to_sexp() == Rc::new(SExp::Atom(bf.loc(), vec![1]))
}

pub fn is_canonical_apply_parent(
    p: &[BodyformPathArc],
    root: &BodyForm,
) -> Result<bool, CompileErr> {
    if p.is_empty() {
        return Ok(false);
    }

    let last_idx = p.len() - 1;
    if p[last_idx] != BodyformPathArc::CallArgument(1) {
        return Ok(false); // Not the right position in the parent.
    }

    let path_to_parent: Vec<BodyformPathArc> = p.iter().take(last_idx).cloned().collect();
    let parent_exp =
        if let Some(parent) = retrieve_bodyform(
            &path_to_parent,
            &root,
            &|bf| bf.clone()
        ) {
            parent
        } else {
            return Err(CompileErr(root.loc(), "Impossible: could not retrieve parent of existing expression".to_string()));
        };

    if let BodyForm::Call(_, parts) = &parent_exp {
        if parts.len() != 3 {
            return Ok(false);
        }

        if !is_apply_atom(parts[0].to_sexp()) {
            return Ok(false);
        }

        Ok(is_one_env_ref(&parts[2]))
    } else {
        Ok(false)
    }
}

fn get_com_body(
    bf: &BodyForm
) -> Option<&BodyForm> {
    if let BodyForm::Call(_, parts) = bf {
        if parts.len() != 2 {
            return None;
        }

        if parts[0].to_sexp() != Rc::new(SExp::Atom(bf.loc(), b"com".to_vec())) {
            return None;
        }

        return Some(&parts[1]);
    }

    None
}

// Detect uses of the 'i' operator in chialisp code.
// When written (a (i x (com A) (com B)) 1)
// it is canonical.
pub fn detect_conditions(
    bf: &BodyForm,
) -> Result<Vec<CSECondition>, CompileErr> {
    let found_conditions = visit_detect_in_bodyform(
        &|path, root, form| -> Result<Option<bool>, CompileErr> {
            // Must have (a ... 1) surrounding it to be canonical.
            if !is_canonical_apply_parent(path, root)? {
                return Ok(None);
            }

            if let BodyForm::Call(_, parts) = form {
                if parts.len() != 4 {
                    return Ok(None);
                }

                if !is_i_atom(parts[0].to_sexp()) {
                    return Ok(None);
                }

                // We're expecting (com A) and (com B) for the last two
                // arguments.
                // XXX also recognize a tree of (i ...) forms whose leaves
                // are all (com X).
                let a_body = get_com_body(parts[2].borrow());
                let b_body = get_com_body(parts[3].borrow());
                if let (Some(_), Some(_)) = (a_body, b_body) {
                    return Ok(Some(true));
                }

                // It is a proper conditional expression, but not in the
                // canonical form.
                return Ok(Some(false));
            }

            Ok(None)
        },
        bf
    )?;

    let results = found_conditions.into_iter().map(|f| {
        CSECondition {
            path: f.path,
            canonical: f.context
        }
    }).collect();

    Ok(results)
}

// True if for some condition path c_path there are matching instance paths
// for either c_path + [CallArgument(1)] or both
// c_path + [CallArgument(2)] and c_path + [CallArgument(3)]
fn cse_is_covering(
    c_path: &[BodyformPathArc],
    instances: &[CSEInstance],
) -> bool {
    let mut target_paths = vec![c_path.to_vec(),c_path.to_vec(),c_path.to_vec()];
    target_paths[0].push(BodyformPathArc::CallArgument(1));
    target_paths[1].push(BodyformPathArc::CallArgument(2));
    target_paths[2].push(BodyformPathArc::CallArgument(3));

    let have_targets: Vec<bool> = target_paths.iter().map(|t| {
        instances.iter().any(|i| {
            path_overlap_one_way(t, &i.path)
        })
    }).collect();

    have_targets[0] || (have_targets[1] && have_targets[2])
}

pub fn cse_classify_by_conditions(
    conditions: &[CSECondition],
    detections: &[CSEDetectionWithoutConditions]
) -> Vec<CSEDetection> {
    detections.iter().filter_map(|d| {
        // Detect the common root of all instanceees.
        if d.instances.is_empty() {
            return None;
        }

        let mut path_limit = 0;
        let possible_root = d.instances[0].path.clone();
        for i in d.instances.iter().skip(1) {
            path_limit = min(path_limit, i.path.len());
            for idx in 0..path_limit {
                if i.path[idx] != possible_root[idx] {
                    path_limit = idx;
                    break;
                }
            }
        }

        // path_limit points to the common root of all instances of this
        // cse detection.
        //
        // now find conditions that are downstream of the cse root.
        let applicable_conditions: Vec<CSECondition> = conditions.iter().filter(|c| {
            path_overlap_one_way(&possible_root, &c.path)
        }).cloned().collect();

        // We don't need to delay the CSE if 1) all conditions below it
        // are canonical and 2) it appears downstream of all conditions
        // it encloses.
        let fully_canonical = applicable_conditions.iter().all(|c| {
            c.canonical && cse_is_covering(&c.path, &d.instances)
        });

        Some(CSEDetection {
            hash: d.hash.clone(),
            subexp: d.subexp.clone(),
            instances: d.instances.clone(),
            saturated: fully_canonical,
            root: possible_root,
        })
    }).collect()
}

pub fn cse_optimize_bodyform(
    loc: &Srcloc,
    name: &[u8],
    b: &BodyForm,
) -> Result<BodyForm, CompileErr> {
    let conditions = detect_conditions(b)?;
    let cse_raw_detections = cse_detect(b)?;
    let cse_detections = cse_classify_by_conditions(
        &conditions,
        &cse_raw_detections
    );
    eprintln!("cse_detections {}", cse_detections.len());

    // While we have them, apply any detections that overlap no others.
    let mut detections_with_dependencies: Vec<(usize, CSEDetection)> =
        sorted_cse_detections_by_applicability(&cse_detections);

    let mut function_body = b.clone();
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
                loc.clone(),
                format!("CSE optimization failed in helper {}", decode_string(name)),
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
                    loc.clone(),
                    format!(
                        "CSE Error in {}: could not find form to replace for path {:?}",
                        decode_string(name),
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
                function_body = res;
            } else {
                return Err(CompileErr(
                    loc.clone(),
                    format!(
                        "cse replacement failed in helper {}, which shouldn't be possible",
                        decode_string(name)
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
        function_body = BodyForm::Let(
            LetFormKind::Parallel,
            Box::new(LetData {
                loc: function_body.loc(),
                kw: None,
                inline_hint: Some(LetFormInlineHint::NonInline(loc.clone())),
                bindings: binding_list,
                body: Rc::new(function_body),
            }),
        );
    }

    Ok(function_body)
}
