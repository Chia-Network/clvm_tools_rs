use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::compiler::clvm::sha256tree;
use crate::compiler::comptypes::{BodyForm, CompileErr};
use crate::compiler::evaluate::is_apply_atom;
use crate::compiler::optimize::bodyform::{
    path_overlap_one_way, visit_detect_in_bodyform, BodyformPathArc, PathDetectVisitorResult,
};
use crate::compiler::sexp::SExp;

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

fn is_apply(bf: &BodyForm) -> bool {
    if let BodyForm::Call(_, parts) = bf {
        return parts.len() == 3 && is_apply_atom(parts[0].to_sexp());
    }

    false
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
        &|path, original, form| {
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
