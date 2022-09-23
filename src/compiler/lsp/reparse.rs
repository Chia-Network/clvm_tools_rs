use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::compiler::clvm::sha256tree_from_atom;
use crate::compiler::comptypes::{BodyForm, CompileErr, CompileForm, CompilerOpts, HelperForm};
use crate::compiler::frontend::{compile_bodyform, compile_helperform};
use crate::compiler::lsp::completion::PRIM_NAMES;
use crate::compiler::lsp::parse::{grab_scope_doc_range, recover_scopes, ParseScope, ParsedDoc};
use crate::compiler::lsp::types::{DocPosition, DocRange};
use crate::compiler::sexp::{parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

lazy_static! {
    static ref END_TAG: Vec<u8> = b"__chia_end".to_vec();
}

#[derive(Debug, Clone)]
pub struct ReparsedHelper {
    pub hash: Vec<u8>,
    pub parsed: Result<HelperForm, CompileErr>,
}

#[derive(Debug, Clone)]
pub struct ReparsedExp {
    pub hash: Vec<u8>,
    pub parsed: Result<BodyForm, CompileErr>,
}

pub struct ReparsedModule {
    pub args: Rc<SExp>,
    pub helpers: HashMap<Vec<u8>, ReparsedHelper>,
    pub exp: Option<ReparsedExp>,
    pub unparsed: HashSet<Vec<u8>>,
    pub includes: HashMap<Vec<u8>, Vec<u8>>,
    pub errors: Vec<CompileErr>,
}

pub fn parse_include(
    _opts: Rc<dyn CompilerOpts>, // Needed to resolve new files when we do that.
    sexp: Rc<SExp>,
) -> Option<Vec<u8>> {
    sexp.proper_list().and_then(|l| {
        if l.len() != 2 {
            return None;
        }

        if let (SExp::Atom(_, incl), SExp::Atom(_, fname)) = (l[0].borrow(), l[1].borrow()) {
            if incl == b"include" {
                return Some(fname.clone());
            }
        }

        None
    })
}

pub fn reparse_subset(
    opts: Rc<dyn CompilerOpts>,
    doc: &[Rc<Vec<u8>>],
    uristring: &str,
    simple_ranges: &[DocRange],
    compiled: &CompileForm,
    prev_helpers: &HashMap<Vec<u8>, ReparsedHelper>,
) -> ReparsedModule {
    let mut result = ReparsedModule {
        args: compiled.args.clone(),
        helpers: HashMap::new(),
        exp: None,
        includes: HashMap::new(),
        unparsed: HashSet::new(),
        errors: Vec::new(),
    };

    // if it's a module, we can patch the prefix in, otherwise make a (mod ()
    // prefix for it.
    // We can take the last phrase and if it's not a helper, we can use it as
    // the end of the document.
    let mut took_args = false;
    let mut took_exp = false;
    let mut have_mod = false;

    if simple_ranges.is_empty() {
        // There's nothing to be gained by trying to do incremental.
        return result;
    }

    // Find out if there's a single atom before the first identified
    // expression.
    let docstart = Srcloc::start(uristring);
    let prefix_start = DocPosition {
        line: 0,
        character: 0,
    };
    let prefix_range = DocRange {
        start: prefix_start,
        end: simple_ranges[0].start.clone(),
    };
    let mut prefix_text = grab_scope_doc_range(doc, &prefix_range, false);
    // TODO hash prefix to prevent reparsing.
    prefix_text.push(b')');

    if let Some(prefix_parse) = parse_sexp(docstart, prefix_text.iter().copied())
        .ok()
        .and_then(|s| {
            if s.is_empty() {
                None
            } else {
                s[0].proper_list()
            }
        })
    {
        let mut form_error_start = 0;
        if !prefix_parse.is_empty() {
            if let SExp::Atom(_, m) = prefix_parse[0].borrow() {
                have_mod = m == b"mod";
                form_error_start = 2;
            }
            if have_mod && prefix_parse.len() == 2 {
                took_args = true;
                result.args = Rc::new(prefix_parse[prefix_parse.len() - 1].clone());
            }
        }

        for p in prefix_parse.iter().skip(form_error_start) {
            result
                .errors
                .push(CompileErr(p.loc(), "bad form".to_string()));
        }
    }

    // Find out of there's a single atom after the last identified atom.
    let suffix_start = simple_ranges[simple_ranges.len() - 1].end.clone();
    let doc_end = DocPosition {
        line: doc.len() as u32,
        character: 0,
    };
    let suffix_range = DocRange {
        start: suffix_start.clone(),
        end: doc_end.clone(),
    };
    let mut suffix_text = grab_scope_doc_range(doc, &suffix_range, false);

    let mut break_end = suffix_text.len();

    // Ensure we can parse to the right locations in the source file.
    // Since our parser can handle a list of parsed objects, remove the
    // final paren.

    // Find last )
    for (i, ch) in suffix_text.iter().enumerate() {
        if *ch == b')' {
            break_end = i;
            break;
        }
    }

    if break_end == suffix_text.len() {
        result.errors.push(CompileErr(
            DocRange {
                start: suffix_start.clone(),
                end: doc_end,
            }
            .to_srcloc(uristring),
            "Missing end paren for enclosing list form".to_string(),
        ));
    }

    suffix_text = suffix_text.iter().take(break_end).copied().collect();
    // Collect hash of prefix and suffix so we can reparse everything if
    // they change.
    let suffix_hash = sha256tree_from_atom(&suffix_text);

    if let Ok(suffix_parse) = parse_sexp(
        Srcloc::new(
            Rc::new(uristring.to_owned()),
            (suffix_start.line + 1) as usize,
            (suffix_start.character + 1) as usize,
        ),
        suffix_text.iter().copied(),
    ) {
        if !suffix_parse.is_empty() {
            took_exp = true;
            result.exp = Some(ReparsedExp {
                hash: suffix_hash,
                parsed: compile_bodyform(suffix_parse[suffix_parse.len() - 1].clone()),
            });
        }
    }

    // Capture the simple ranges, then check each one's hash
    // if the hash isn't present in the helpers we have, we need to run the
    // frontend on it.
    let start_parsing_forms = if took_args {
        0
    } else if have_mod {
        1
    } else {
        0
    };
    let parse_as_body = if have_mod && !took_exp {
        simple_ranges.len() - 1
    } else {
        simple_ranges.len()
    };

    for (i, r) in simple_ranges.iter().enumerate() {
        let text = grab_scope_doc_range(doc, r, false);
        let hash = sha256tree_from_atom(&text);

        // Always reparse the body for convenience.  It's one form so it won't
        // accumulate.
        if !prev_helpers.contains_key(&hash) || i == parse_as_body {
            let loc = Srcloc::new(
                Rc::new(uristring.to_owned()),
                (r.start.line + 1) as usize,
                (r.start.character + 1) as usize,
            );
            match parse_sexp(loc.clone(), text.iter().copied()) {
                Ok(parsed) => {
                    if i < start_parsing_forms {
                        result.args = parsed[0].clone();
                        continue;
                    } else if i == parse_as_body {
                        result.exp = Some(ReparsedExp {
                            hash,
                            parsed: compile_bodyform(parsed[0].clone()),
                        });
                        continue;
                    } else if let Some(include) = parse_include(opts.clone(), parsed[0].clone()) {
                        result.includes.insert(hash.clone(), include.clone());
                        continue;
                    }

                    result.helpers.insert(
                        hash.clone(),
                        ReparsedHelper {
                            hash,
                            parsed: compile_helperform(opts.clone(), parsed[0].clone()).and_then(
                                |mh| {
                                    if let Some(h) = mh {
                                        Ok(h)
                                    } else {
                                        Err(CompileErr(loc, "must be a helper form".to_string()))
                                    }
                                },
                            ),
                        },
                    );
                }
                Err((l, s)) => {
                    result.helpers.insert(
                        hash.clone(),
                        ReparsedHelper {
                            hash,
                            parsed: Err(CompileErr(l, s)),
                        },
                    );
                }
            }
        } else {
            result.unparsed.insert(hash);
        }
    }

    result
}

// Only the top scope is relevant for now.
fn find_function_in_scopes(prims: &[Vec<u8>], scopes: &ParseScope, name: &SExp) -> bool {
    if let SExp::Atom(_, a) = name {
        scopes.functions.contains(name) || prims.iter().any(|p| p == a)
    } else {
        false
    }
}

// Add errors for unrecognized calls.
pub fn check_live_helper_calls(
    prims: &[Vec<u8>],
    scopes: &ParseScope,
    exp: &BodyForm,
) -> Option<CompileErr> {
    match exp {
        BodyForm::Call(l, v) => {
            if v.is_empty() {
                return Some(CompileErr(l.clone(), "Empty function call".to_string()));
            }

            // Try to make sense of the list head
            if let BodyForm::Value(s) = v[0].borrow() {
                if !find_function_in_scopes(prims, scopes, s) {
                    return Some(CompileErr(
                        s.loc(),
                        format!("No such function found: {}", s),
                    ));
                }
            } else {
                return Some(CompileErr(
                    l.clone(),
                    "Inappropriate function name".to_string(),
                ));
            }

            for b in v.iter().skip(1) {
                if let Some(e) = check_live_helper_calls(prims, scopes, b) {
                    return Some(e);
                }
            }
        }
        BodyForm::Let(_l, _kind, _bindings, body) => {
            return check_live_helper_calls(prims, scopes, body.borrow());
        }
        _ => {}
    }

    None
}

pub fn combine_new_with_old_parse(
    uristring: &str,
    text: &[Rc<Vec<u8>>],
    parsed: &ParsedDoc,
    reparse: &ReparsedModule,
) -> ParsedDoc {
    let new_includes = reparse.includes.clone();
    let mut new_helpers = parsed.helpers.clone();
    let mut extracted_helpers = Vec::new();
    let mut to_remove = HashSet::new();
    let mut remove_names = HashSet::new();
    let mut hash_to_name = parsed.hash_to_name.clone();
    let mut out_errors = reparse.errors.clone();

    // Collect to-delete set.
    for (h, _) in new_helpers.iter() {
        if !reparse.unparsed.contains(h) && !reparse.helpers.contains_key(h) {
            if let Some(name) = parsed.hash_to_name.get(h) {
                remove_names.insert(name.clone());
            }
            to_remove.insert(h.clone());
        }
    }

    for h in to_remove.iter() {
        hash_to_name.remove(h);
        new_helpers.remove(h);
    }

    // Iterate new helpers.
    for (h, p) in reparse.helpers.iter() {
        match &p.parsed {
            Err(e) => {
                out_errors.push(e.clone());
            }
            Ok(parsed) => {
                hash_to_name.insert(h.clone(), parsed.name().clone());
                extracted_helpers.push(parsed.clone());
            }
        }
        new_helpers.insert(h.clone(), p.clone());
    }

    // For helpers that parsed, replace them in the compile.
    let mut new_compile = parsed.compiled.replace_helpers(&extracted_helpers);

    // Handle args and body, which are optional since the file can represent
    // a list (include file).
    new_compile.args = reparse.args.clone();
    let empty_body = BodyForm::Quoted(SExp::Nil(reparse.args.loc()));
    match &reparse.exp {
        None => {
            new_compile.exp = Rc::new(empty_body);
        }
        Some(exp) => match &exp.parsed {
            Ok(body) => {
                new_compile.exp = Rc::new(body.clone());
            }
            Err(e) => {
                new_compile.exp = Rc::new(empty_body);
                out_errors.push(e.clone());
            }
        },
    }

    let compile_with_dead_helpers_removed = new_compile.remove_helpers(&remove_names);
    let scopes = recover_scopes(uristring, text, &new_compile);

    for h in compile_with_dead_helpers_removed.helpers.iter() {
        if let HelperForm::Defun(_, d) = h {
            if let Some(error) = check_live_helper_calls(&PRIM_NAMES, &scopes, &d.body) {
                out_errors.push(error);
            }
        }
    }

    // Check whether functions called in exp are live
    if let Some(error) =
        check_live_helper_calls(&PRIM_NAMES, &scopes, &compile_with_dead_helpers_removed.exp)
    {
        out_errors.push(error);
    }

    ParsedDoc {
        compiled: compile_with_dead_helpers_removed,
        errors: out_errors,
        scopes,
        includes: new_includes,
        helpers: new_helpers,
        hash_to_name,
        exp: reparse.exp.clone(),
    }
}
