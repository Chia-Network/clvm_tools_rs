use std::collections::{HashMap, HashSet, BTreeSet};
use std::rc::Rc;

use crate::compiler::{BasicCompileContext, CompileErr, CompileForm, CompilerOpts, HelperForm};
use crate::compiler::optimize::{SyntheticType, sexp_scale};
use crate::compiler::optimize::depgraph::{DepgraphKind, FunctionDependencyGraph};
use crate::compiler::codegen::codegen;
use crate::compiler::sexp::ToSExp;

// Find the roots for the given function.
fn find_roots(visited: &mut HashSet<Vec<u8>>, root_set: &mut BTreeSet<Vec<u8>>, depgraph: &FunctionDependencyGraph, function: &[u8]) {
    eprintln!("visited {} for function {}", visited.to_sexp(depgraph.loc.clone()), function.to_sexp(depgraph.loc.clone()));
    if visited.contains(function) {
        return;
    }

    visited.insert(function.to_vec());

    if let Some(parents) = depgraph.parents(function) {
        eprintln!("parents of {}: {}", function.to_sexp(depgraph.loc.clone()), parents.to_sexp(depgraph.loc.clone()));
        if parents.is_empty() {
            root_set.insert(function.to_vec());
            return;
        }

        if let Some(f) = depgraph.helpers.get(function) {
            if matches!(f.status, DepgraphKind::UserNonInline) {
                root_set.insert(function.to_vec());
                return;
            }
        }

        for p in parents.iter() {
            find_roots(visited, root_set, depgraph, &p);
        }
    }
}

// Should take a desugared program.
pub fn deinline_opt(
    context: &mut BasicCompileContext,
    opts: Rc<dyn CompilerOpts>,
    mut compileform: CompileForm,
) -> Result<CompileForm, CompileErr> {
    let depgraph = FunctionDependencyGraph::new(&compileform);

    let mut best_compileform = compileform.clone();
    let generated_program = codegen(context, opts.clone(), &best_compileform)?;
    let mut metric = sexp_scale(&generated_program);
    let flip_helper = |h: &mut HelperForm| {
        if let HelperForm::Defun(inline, defun) = h {
            if matches!(&defun.synthetic, Some(SyntheticType::NoInlinePreference)) {
                *h = HelperForm::Defun(!*inline, defun.clone());
                return true;
            }
        }

        false
    };

    // defun F -> Synthetic letbinding_$_1
    //            Synthetic letbinding_$_2 -> Synthetic letbinding_$_3
    //
    // defun H_inline ->
    //            Synthetic letbinding_$_4 -> Synthetic letbinding_$_5
    //                                        Synthetic letbinding_$_6
    //
    // defun G -> Synthetic letbinding_$_7 -> H_inline
    //
    // - Synthetic Roots -
    //
    // letbinding_$_1, letbinding_$_2, letbinding_$_7
    // letbinding_$_4 is not a root, because it's in H_inline, called from G.
    //
    // So for each synthetic function, we traverse functions that depend on
    // it as long as it's a synthetic function or a non-synthetic inline.
    // The functions we reach are the roots.
    //
    // If any two roots share dependencies, they must be merged.
    //
    // So we take the set of each root and every synthetic function reachable
    // from it and for each of those sets, we do the normal optimizataion loop.

    // Find leaf synthetic functions by first finding leaf functions, then
    // until we find a synthetic function, go up to each depended_on_by function
    // until we reach a root.
    //
    // Remember the root this function belongs to.
    let leaves = depgraph.leaves();

    let mut roots: HashMap<Vec<u8>, BTreeSet<Vec<u8>>> = HashMap::new();

    // For each leaf, find roots.
    for l in leaves.iter() {
        let mut visited = HashSet::new();
        let mut leaf_roots = BTreeSet::new();
        find_roots(&mut visited, &mut leaf_roots, &depgraph, l);
        roots.insert(l.to_vec(), leaf_roots);
    }

    let synthetic_functions: BTreeSet<Vec<u8>> = depgraph.helpers.iter().filter(|(k,f)| {
        matches!(f.status, DepgraphKind::Synthetic(_))
    }).map(|(k,f)| k.to_vec()).collect();

    // Make a set of root sets to coalesce them.
    let mut roots_set: HashSet<BTreeSet<Vec<u8>>> = HashSet::new();
    for (_, common_roots) in roots.iter() {
        roots_set.insert(common_roots.clone());
    }

    eprintln!("root sets: {}", roots_set.to_sexp(compileform.loc.clone()));

    loop {
        let start_metric = metric;

        for i in 0..compileform.helpers.len() {
            // Try flipped.
            let old_helper = compileform.helpers[i].clone();
            if !flip_helper(&mut compileform.helpers[i]) {
                continue;
            }

            let maybe_smaller_program = codegen(context, opts.clone(), &compileform)?;
            let new_metric = sexp_scale(&maybe_smaller_program);

            // Don't keep this change if it made things worse.
            if new_metric >= metric {
                compileform.helpers[i] = old_helper;
            } else {
                metric = new_metric;
                best_compileform = compileform.clone();
            }
        }

        if start_metric == metric {
            break;
        }
    }

    Ok(best_compileform)
}
