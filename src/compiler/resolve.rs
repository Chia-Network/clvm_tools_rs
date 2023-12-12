use std::borrow::Borrow;
use std::collections::{BTreeMap, HashSet};
use std::mem::swap;
use std::rc::Rc;

use crate::compiler::BasicCompileContext;
use crate::compiler::codegen::toposort_assign_bindings;
use crate::compiler::compiler::is_at_capture;
use crate::compiler::comptypes::{Binding, BindingPattern, BodyForm, CompileErr, CompileForm, CompilerOpts, DefconstData, DefunData, HelperForm, ImportLongName, LambdaData, LetData, LetFormKind, ModuleImportSpec, NamespaceData, map_m};
use crate::compiler::sexp::{decode_string, SExp};

fn capture_scope(in_scope: &mut HashSet<Vec<u8>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Cons(l, a, b) => {
            if let Some((parent, children)) = is_at_capture(a.clone(), b.clone()) {
                in_scope.insert(parent.clone());
                capture_scope(in_scope, children);
            } else {
                capture_scope(in_scope, a.clone());
                capture_scope(in_scope, b.clone());
            }
        }
        SExp::Atom(l, a) => {
            in_scope.insert(a.clone());
        }
        _ => { }
    }
}

pub struct FindNamespaceLookingAtHelpers<'a> {
    hlist: &'a [HelperForm],
    namespace: Option<&'a ImportLongName>,
    offset: usize
}

pub struct TourNamespaces<'a> {
    helpers: &'a [HelperForm],
    look_stack: Vec<FindNamespaceLookingAtHelpers<'a>>
}

pub struct FoundHelper<'a> {
    helpers: &'a [HelperForm],
    namespace: Option<&'a ImportLongName>,
    helper: &'a HelperForm
}

impl<'a> Iterator for TourNamespaces<'a> {
    type Item = FoundHelper<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.look_stack.is_empty() {
                return None;
            }

            let ls_at = self.look_stack.len()-1;
            let ls_len = self.look_stack[ls_at].hlist.len();

            if self.look_stack[ls_at].offset >= ls_len {
                self.look_stack.pop();
                continue;
            }

            let current_offset = self.look_stack[ls_at].offset;
            let current = &self.look_stack[ls_at].hlist[current_offset];
            self.look_stack[ls_at].offset += 1;

            if let HelperForm::Defnamespace(ns) = current {
                let combined_name = self.look_stack[ls_at].namespace.map(|p| {
                    p.combine(&ns.longname)
                });

                self.look_stack.push(FindNamespaceLookingAtHelpers {
                    hlist: &ns.helpers,
                    namespace: Some(&ns.longname),
                    offset: 0,
                });
                continue;
            }

            return Some(FoundHelper {
                helpers: self.helpers,
                namespace: self.look_stack[ls_at].namespace.clone(),
                helper: current
            });
        }
    }
}

fn namespace_helper(
    name: &ImportLongName,
    value: &HelperForm
) -> HelperForm {
    match value {
        HelperForm::Defun(inline,dd) => {
            HelperForm::Defun(*inline, DefunData {
                name: name.as_u8_vec(false),
                .. dd.clone()
            })
        }
        HelperForm::Defconstant(dc) => {
            HelperForm::Defconstant(DefconstData {
                name: name.as_u8_vec(false),
                .. dc.clone()
            })
        }
        _ => todo!()
    }
}

pub fn tour_helpers<'a>(
    helpers: &'a [HelperForm],
) -> TourNamespaces<'a> {
    TourNamespaces {
        helpers,
        look_stack: vec![FindNamespaceLookingAtHelpers {
            hlist: &helpers,
            namespace: None,
            offset: 0,
        }]
    }
}

fn find_helper_in_namespace<'a>(
    helpers: &'a [FoundHelper],
    parent: Option<&ImportLongName>,
    child: &[u8],
) -> Option<(ImportLongName, &'a HelperForm)> {
    let mut in_target = helpers.iter().filter(|found| {
        found.namespace == parent
    }).filter(|h| h.helper.name() == child);
    if let Some(t) = in_target.next() {
        let name = parent.map(|p| p.with_child(child)).unwrap_or_else(|| {
            let (_, parsed) = ImportLongName::parse(child);
            parsed
        });
        return Some((name, t.helper));
    }

    None
}

pub fn find_helper_target<'a>(
    opts: Rc<dyn CompilerOpts>,
    helpers: &'a [HelperForm],
    parent_ns: Option<&ImportLongName>,
    orig_name: &[u8],
    name: &ImportLongName
) -> Option<(ImportLongName, HelperForm)> {
    // XXX speed this up, remove iteration.
    // Decompose into parent and child.
    let (parent, child) = name.parent_and_name();

    // Get a list namespace refs from the namespace identified by parent_ns.
    let tour_helpers: Vec<FoundHelper> = tour_helpers(&helpers).collect();
    let home_ns: Vec<&FoundHelper> = tour_helpers.iter().filter(|found| {
        found.namespace == parent_ns
    }).collect();

    // check the matching namespace to the one specified to see if we can find the
    // target.
    for h in home_ns.iter() {
        if h.helper.name() == &child {
            let combined =
                if let Some(p) = parent_ns {
                    p.with_child(&child)
                } else {
                    let (_, p) = ImportLongName::parse(&child);
                    p
                };
            return Some((combined, h.helper.clone()));
        }
    }

    // Look at each import specification and construct a target namespace, then
    // try to find a helper in that namespace that matches the target name.

    for ns_spec in home_ns.iter().filter_map(|found| {
        if let HelperForm::Defnsref(nsref) = found.helper {
            Some(nsref.clone())
        } else {
            None
        }
    }) {
        eprintln!("try to find {} ({}) using import {} in namespace {}", decode_string(orig_name), decode_string(&name.as_u8_vec(false)), HelperForm::Defnsref(ns_spec.clone()).to_sexp(), display_namespace(parent_ns.clone()));
        match &ns_spec.specification {
            ModuleImportSpec::Qualified(q) => {
                if let Some(t) = &q.target {
                    // Qualified as [t.name] only matches when we look use the 'as' qualifier.
                    if Some(&t.name) == parent.as_ref() {
                        let target_name = ns_spec.longname.with_child(&child);
                        if let Some((name, helper)) = find_helper_target(
                            opts.clone(),
                            helpers,
                            Some(&ns_spec.longname),
                            orig_name,
                            &target_name,
                        ) {
                            return Some((target_name, helper.clone()));
                        }
                    }
                } else {
                    // Qualified namespace matches the canonical name
                    if parent.as_ref() == Some(&ns_spec.longname) {
                        let target_name = ns_spec.longname.with_child(&child);
                        if let Some((name, helper)) = find_helper_target(
                            opts.clone(),
                            helpers,
                            Some(&ns_spec.longname),
                            orig_name,
                            &target_name
                        ) {
                            return Some((target_name, helper.clone()));
                        }
                    }
                }
            }
            ModuleImportSpec::Exposing(_, x) => {
                if parent.is_some() {
                    continue;
                }

                for exposed in x.iter() {
                    if exposed.name == orig_name {
                        let target_name = ns_spec.longname.with_child(&child);
                        if let Some((name, helper)) = find_helper_target(
                            opts.clone(),
                            helpers,
                            Some(&ns_spec.longname),
                            orig_name,
                            &target_name,
                        ) {
                            return Some((target_name, helper.clone()));
                        }
                    }
                }
            }
            ModuleImportSpec::Hiding(_, h) => {
                eprintln!("check namespace {} for {}", decode_string(&ns_spec.longname.as_u8_vec(false)), decode_string(&orig_name));
                if parent.is_some() {
                    continue;
                }

                // Hiding means we don't match this name.
                if h.iter().filter(|h| h.name == orig_name).next().is_some() {
                    continue;
                }

                let target_name = ns_spec.longname.with_child(&child);
                if let Some((name, helper)) = find_helper_target(
                    opts.clone(),
                    &helpers,
                    Some(&ns_spec.longname),
                    orig_name,
                    &target_name,
                ) {
                    return Some((target_name, helper.clone()));
                }
            }
        }
    }

    None
}

fn display_namespace(parent_ns: Option<&ImportLongName>) -> String {
    if let Some(p) = parent_ns {
        format!("namespace {}", decode_string(&p.as_u8_vec(false)))
    } else {
        "the root module".to_string()
    }
}

fn is_compiler_builtin(name: &[u8]) -> bool {
    name == b"com" || name == b"@"
}

fn add_binding_names(bindings: &mut HashSet<Vec<u8>>, pattern: &BindingPattern) {
    match pattern {
        BindingPattern::Name(n) => {
            bindings.insert(n.clone());
        }
        BindingPattern::Complex(c) => {
            match c.borrow() {
                SExp::Cons(_, a, b) => {
                    add_binding_names(bindings, &BindingPattern::Complex(a.clone()));
                    add_binding_names(bindings, &BindingPattern::Complex(b.clone()));
                }
                SExp::Atom(_, a) => {
                    bindings.insert(a.clone());
                }
                _ => { }
            }
        }
    }
}

fn resolve_namespaces_in_expr(
    resolved_helpers: &mut BTreeMap<ImportLongName, HelperForm>,
    opts: Rc<dyn CompilerOpts>,
    program: &CompileForm,
    parent_ns: Option<&ImportLongName>,
    in_scope: &HashSet<Vec<u8>>,
    expr: Rc<BodyForm>
) -> Result<Rc<BodyForm>, CompileErr> {
    match expr.borrow() {
        BodyForm::Call(loc, args, tail) => {
            let new_tail =
                if let Some(t) = tail.as_ref() {
                    Some(resolve_namespaces_in_expr(
                        resolved_helpers,
                        opts.clone(),
                        program,
                        parent_ns,
                        in_scope,
                        t.clone()
                    )?)
                } else {
                    None
                };

            Ok(Rc::new(BodyForm::Call(
                loc.clone(),
                map_m(
                    |e: &Rc<BodyForm>| {
                        resolve_namespaces_in_expr(
                            resolved_helpers,
                            opts.clone(),
                            program,
                            parent_ns,
                            in_scope,
                            e.clone()
                        )
                    },
                    &args
                )?,
                new_tail
            )))
        }
        BodyForm::Value(SExp::Atom(nl, name)) => {
            // if the short name is in scope, we can just return it.
            if in_scope.contains(name) {
                return Ok(expr.clone());
            }

            let (_, parsed_name) = ImportLongName::parse(&name);
            let (parent, child) = parsed_name.parent_and_name();

            // If not namespaced, then it could be a primitive
            if parent.is_none() {
                let prim_map = opts.prim_map();
                if let Some(p) = prim_map.get(&child) {
                    return Ok(expr.clone());
                }

                let child_sexp = SExp::Atom(nl.clone(), name.clone());
                for (k, v) in prim_map.iter() {
                    let v_borrowed: &SExp = v.borrow();
                    if v_borrowed == &child_sexp {
                        return Ok(expr.clone());
                    }
                }
            }

            let (target_full_name, target_helper) =
                if let Some((target_full_name, target_helper)) = find_helper_target(
                    opts.clone(),
                    &program.helpers,
                    parent_ns,
                    &name,
                    &parsed_name
                ) {
                    (target_full_name, target_helper)
                } else if is_compiler_builtin(&name) {
                    return Ok(expr.clone());
                } else {
                    return Err(CompileErr(expr.loc(), format!("could not find helper {} in {}", decode_string(&name), display_namespace(parent_ns.clone()))));
                };

            resolved_helpers.insert(target_full_name.clone(), target_helper.clone());
            Ok(Rc::new(BodyForm::Value(SExp::Atom(nl.clone(), target_full_name.as_u8_vec(false)))))
        }
        BodyForm::Value(val) => Ok(expr.clone()),
        BodyForm::Quoted(val) => Ok(expr.clone()),
        BodyForm::Let(LetFormKind::Sequential, ld) => {
            let mut new_scope = in_scope.clone();
            let mut new_bindings = Vec::new();
            for b in ld.bindings.iter() {
                let b_borrowed: &Binding = b.borrow();
                let new_binding = Binding {
                    body: resolve_namespaces_in_expr(
                        resolved_helpers,
                        opts.clone(),
                        program,
                        parent_ns,
                        &new_scope,
                        b.body.clone()
                    )?,
                    .. b_borrowed.clone()
                };
                new_bindings.push(Rc::new(new_binding));
                add_binding_names(&mut new_scope, &b.pattern);
            }
            Ok(Rc::new(BodyForm::Let(LetFormKind::Sequential, Box::new(LetData {
                bindings: new_bindings,
                body: resolve_namespaces_in_expr(
                    resolved_helpers,
                    opts.clone(),
                    program,
                    parent_ns,
                    &new_scope,
                    ld.body.clone()
                )?,
                .. *ld.clone()
            }))))
        }
        BodyForm::Let(LetFormKind::Parallel, ld) => {
            let mut new_scope = in_scope.clone();
            let mut new_bindings = Vec::new();
            for b in ld.bindings.iter() {
                let b_borrowed: &Binding = b.borrow();
                let new_binding = Binding {
                    body: resolve_namespaces_in_expr(
                        resolved_helpers,
                        opts.clone(),
                        program,
                        parent_ns,
                        in_scope,
                        b.body.clone()
                    )?,
                    .. b_borrowed.clone()
                };
                new_bindings.push(Rc::new(new_binding));
                add_binding_names(&mut new_scope, &b.pattern);
            }
            Ok(Rc::new(BodyForm::Let(LetFormKind::Sequential, Box::new(LetData {
                bindings: new_bindings,
                body: resolve_namespaces_in_expr(
                    resolved_helpers,
                    opts.clone(),
                    program,
                    parent_ns,
                    &new_scope,
                    ld.body.clone()
                )?,
                .. *ld.clone()
            }))))
        }
        BodyForm::Let(LetFormKind::Assign, ld) => {
            let mut new_scope = in_scope.clone();
            let mut new_bindings = Vec::new();
            let sorted_bindings = toposort_assign_bindings(&expr.loc(), &ld.bindings)?;
            for b in sorted_bindings.iter() {
                let b_borrowed: &Binding = ld.bindings[b.index].borrow();
                let new_binding = Binding {
                    body: resolve_namespaces_in_expr(
                        resolved_helpers,
                        opts.clone(),
                        program,
                        parent_ns,
                        &new_scope,
                        b_borrowed.body.clone()
                    )?,
                    .. b_borrowed.clone()
                };
                new_bindings.push(Rc::new(new_binding));
                add_binding_names(&mut new_scope, &b_borrowed.pattern);
            }
            Ok(Rc::new(BodyForm::Let(LetFormKind::Assign, Box::new(LetData {
                bindings: new_bindings,
                body: resolve_namespaces_in_expr(
                    resolved_helpers,
                    opts.clone(),
                    program,
                    parent_ns,
                    &new_scope,
                    ld.body.clone()
                )?,
                .. *ld.clone()
            }))))
        }
        BodyForm::Mod(_, _) => Ok(expr.clone()),
        BodyForm::Lambda(ld) => {
            let new_captures = resolve_namespaces_in_expr(
                resolved_helpers,
                opts.clone(),
                program,
                parent_ns,
                in_scope,
                ld.captures.clone()
            )?;
            let mut scope_inside_lambda = in_scope.clone();
            capture_scope(&mut scope_inside_lambda, ld.capture_args.clone());
            capture_scope(&mut scope_inside_lambda, ld.args.clone());
            let new_body = resolve_namespaces_in_expr(
                resolved_helpers,
                opts.clone(),
                program,
                parent_ns,
                &scope_inside_lambda,
                ld.body.clone()
            )?;
            Ok(Rc::new(BodyForm::Lambda(Box::new(LambdaData {
                captures: new_captures,
                body: new_body,
                .. *ld.clone()
            }))))
        }
    }
}

fn resolve_namespaces_in_helper(
    resolved_helpers: &mut BTreeMap<ImportLongName, HelperForm>,
    opts: Rc<dyn CompilerOpts>,
    program: &CompileForm,
    parent_ns: Option<&ImportLongName>,
    helper: &HelperForm,
    root: bool
) -> Result<HelperForm, CompileErr> {
    match helper {
        HelperForm::Defnamespace(ns) => {
            let combined_ns =
                if let Some(p) = parent_ns {
                    p.combine(&ns.longname)
                } else {
                    ns.longname.clone()
                };

            Ok(HelperForm::Defnamespace(NamespaceData {
                helpers: map_m(
                    |h: &HelperForm| {
                        resolve_namespaces_in_helper(
                            resolved_helpers,
                            opts.clone(),
                            program,
                            Some(&combined_ns),
                            h,
                            false
                        )
                    },
                    &ns.helpers
                )?,
                .. ns.clone()
            }))
        }
        HelperForm::Defnsref(nsr) => Ok(helper.clone()),
        HelperForm::Defun(inline, dd) => {
            let mut in_scope = HashSet::new();
            capture_scope(&mut in_scope, dd.args.clone());
            let new_defun = HelperForm::Defun(*inline, DefunData {
                body: resolve_namespaces_in_expr(
                    resolved_helpers,
                    opts.clone(),
                    program,
                    parent_ns.clone(),
                    &in_scope,
                    dd.body.clone()
                )?,
                .. dd.clone()
            });
            Ok(new_defun)
        }
        HelperForm::Defconstant(dc) => {
            let mut in_scope = HashSet::new();
            let new_defconst = HelperForm::Defconstant(DefconstData {
                body: resolve_namespaces_in_expr(
                    resolved_helpers,
                    opts.clone(),
                    program,
                    parent_ns.clone(),
                    &in_scope,
                    dc.body.clone()
                )?,
                .. dc.clone()
            });
            Ok(new_defconst)
        }
        _ => {
            eprintln!("unhandled helper {}", helper.to_sexp());
            todo!()
        }
    }
}

pub fn resolve_namespaces(
    opts: Rc<dyn CompilerOpts>,
    program: &CompileForm
) -> Result<CompileForm, CompileErr> {
    let mut resolved_helpers = BTreeMap::new();
    let mut new_resolved_helpers = BTreeMap::new();

    // The main expression is in the scope of the program arguments.
    let mut program_scope = HashSet::new();
    capture_scope(&mut program_scope, program.args.clone());

    let new_expr = resolve_namespaces_in_expr(
        &mut new_resolved_helpers,
        opts.clone(),
        program,
        None,
        &program_scope,
        program.exp.clone()
    )?;

    // Since we're resolving names now ahead of compilation, take this opportunity
    // to do it definitely by visiting every reachable helper from the main
    // expression.
    while !new_resolved_helpers.is_empty() {
        let mut round_resolved_helpers = BTreeMap::new();
        for (name, helper) in new_resolved_helpers.iter() {
            let (parent, child) = name.parent_and_name();
            let renamed_helper = namespace_helper(&name, &helper);
            if !resolved_helpers.contains_key(name) {
                let rewritten_helper = resolve_namespaces_in_helper(
                    &mut round_resolved_helpers,
                    opts.clone(),
                    program,
                    parent.as_ref(),
                    &renamed_helper,
                    true
                )?;
                resolved_helpers.insert(name.clone(), rewritten_helper.clone());
            }
        }
        swap(&mut new_resolved_helpers, &mut round_resolved_helpers);
    }

    // The set of helpers is the set of helpers in resolved_helpers al
    Ok(CompileForm {
        helpers: resolved_helpers.values().cloned().collect(),
        .. program.clone()
    })
}