use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

/// Long name for an import.  Has at least one name, but has a prefix that
/// locates it in space.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ImportLongName {
    prefix_components: Vec<String>,
    last_component: String,
}

pub struct ImportLongNameIterator<'a> {
    target: &'a ImportLongName,
    idx: usize,
}

impl<'a> Iterator for ImportLongNameIterator<'a> {
    type Item = String;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx > self.target.prefix_components.len() {
            return None;
        }

        if self.idx == self.target.prefix_components.len() {
            self.idx += 1;
            return Some(self.target.last_component.clone());
        }

        let res = self.target.prefix_components[self.idx].clone();
        self.idx += 1;
        Some(res)
    }
}

impl ImportLongName {
    pub fn iter(&self) -> ImportLongNameIterator {
        ImportLongNameIterator { target: self, idx: 0 }
    }

    pub fn len(&self) -> usize {
        self.prefix_components.len() + 1
    }

    pub fn is_empty() -> bool {
        false
    }

    pub fn from_ident(loc: Srcloc, name: &[u8]) -> Result<Self, CompileErr> {
        let mut word = Vec::new();
        let mut words = Vec::new();
        for ch in name.iter() {
            if *ch == b'.' {
                if word.is_empty() {
                    return Err(CompileErr(loc, "long name atom had an empty component".to_string()));
                }

                words.push(word.clone());
                word.clear();
            } else {
                word.push(*ch);
            }
        }
        if word.is_empty() {
            return Err(CompileErr(loc, "long name atom didn't have a terminal word".to_string()));
        }

        Ok(ImportLongName {
            prefix_components: words.iter().map(|w| decode_string(w)).collect(),
            last_component: decode_string(&word),
        })
    }
}

#[test]
fn test_parse_import_name() {
    let loc = Srcloc::start("import-test.clsp");
    let parsed = ImportLongName::from_ident(loc, b"std.hashing.sha256tree").expect("should parse");
    let iterated: Vec<String> = parsed.iter().collect();
    assert_eq!(&iterated, &[
        "std".to_string(),
        "hashing".to_string(),
        "sha256tree".to_string()
    ]);
}

/// A specification of renaming for an imported module.
#[derive(Debug, Clone)]
pub struct ImportRenameSpec {
    pub loc: Srcloc,
    pub nl: Srcloc,

    pub target: ImportLongName,
    pub to_include: Vec<Vec<u8>>,
    pub to_exclude: Vec<Vec<u8>>,
    pub changed: HashMap<Vec<u8>, Vec<u8>>,
}

impl ImportRenameSpec {
    fn to_sexp(&self) -> Rc<SExp> {
        let mut result_list =
            if self.changed.is_empty() {
                vec![
                    Rc::new(SExp::Atom(self.loc.clone(), b"import".to_vec())),
                    Rc::new(SExp::Atom(self.nl.clone(), compose_fq_name(b'.', &self.target).as_bytes().to_vec())),
                ]
            } else {
                vec![
                    Rc::new(SExp::Atom(self.loc.clone(), b"from".to_vec())),
                    Rc::new(SExp::Atom(self.nl.clone(), compose_fq_name(b'.', &self.target).as_bytes().to_vec())),
                    Rc::new(SExp::Atom(self.loc.clone(), b"import".to_vec())),
                ]
            };

        for (n,v) in self.changed.iter() {
            result_list.push(Rc::new(SExp::Atom(self.loc.clone(), n.to_vec())));
            result_list.push(Rc::new(SExp::Atom(self.loc.clone(), b"as".to_vec())));
            result_list.push(Rc::new(SExp::Atom(self.loc.clone(), v.to_vec())));
        }

        if !self.to_exclude.is_empty() {
            result_list.push(Rc::new(SExp::Atom(self.loc.clone(), b"hiding".to_vec())));
            for e in self.to_exclude.iter() {
                result_list.push(Rc::new(SExp::Atom(self.loc.clone(), e.clone())));
            }
        }

        if !self.to_include.is_empty() {
            result_list.push(Rc::new(SExp::Atom(self.loc.clone(), b"exposing".to_vec())));
            for e in self.to_include.iter() {
                result_list.push(Rc::new(SExp::Atom(self.loc.clone(), e.clone())));
            }
        }

        Rc::new(enlist(self.loc.clone(), &result_list))
    }
}

/// An imported file after first parsing.
#[derive(Debug, Clone)]
pub struct ImportedFile {
    pub disk_name: String,
    pub import_long_name: ImportLongName,
    pub rename_specs: ImportRenameSpec,
    pub imports: Vec<Rc<ImportedFile>>,
    pub forms: Vec<Rc<SExp>>,
}

/// Recognized import directive.
#[derive(Debug, Clone)]
pub struct RecognizedImportDirective {
    source: ImportLongName,
    spec: ImportRenameSpec,
}

#[derive(Debug,Clone)]
enum ParseImportRenameClauseState {
    Empty,
    IndividuallyRenamingAs(Vec<u8>),
    IndividuallyRenamingTo(Vec<u8>),
    DoingExposingOrHiding(bool),
}

fn finish_import_directive(
    loc: Srcloc,
    source: &ImportLongName,
    relative: bool,
    lst: &[SExp],
    name_loc: Srcloc,
    name_atom: &[u8],
    index: usize
) -> Result<RecognizedImportDirective, CompileErr> {
    let exposing_atom = SExp::Atom(loc.clone(), b"exposing".to_vec());
    let relative_atom = SExp::Atom(loc.clone(), b"relative".to_vec());
    let hiding_atom = SExp::Atom(loc.clone(), b"hiding".to_vec());
    let as_atom = SExp::Atom(loc.clone(), b"as".to_vec());

    let mut state = ParseImportRenameClauseState::Empty;

    let target_name = ImportLongName::from_ident(loc.clone(), name_atom)?;
    let mut spec = ImportRenameSpec {
        loc: loc.clone(),
        nl: name_loc.clone(),
        target: target_name.clone(),

        changed: HashMap::new(),
        to_exclude: Vec::new(),
        to_include: Vec::new(),
    };

    let check_exposing_or_hiding = |elt: &SExp| {
        if elt == &exposing_atom {
            Some(ParseImportRenameClauseState::DoingExposingOrHiding(true))
        } else if elt == &hiding_atom {
            Some(ParseImportRenameClauseState::DoingExposingOrHiding(false))
        } else {
            None
        }
    };

    for elt in lst.iter().skip(index) {
        eprintln!("elt {elt} state {state:?}");
        match state {
            ParseImportRenameClauseState::Empty => {
                if let Some(res) = check_exposing_or_hiding(elt.borrow()) {
                    state = res;
                    continue;
                }

                if let SExp::Atom(_, name) = elt.borrow() {
                    state = ParseImportRenameClauseState::IndividuallyRenamingAs(name.to_vec());
                } else {
                    return Err(CompileErr(elt.loc(), "(import <mod-path> [renames ...] [exposing ...] [hiding ...]) or (from <mod-path> import [renames ...] [exposing ...] [hiding ...]) where each rename is [<exported-name> as <imported-name>]".to_string()));
                }
            }
            ParseImportRenameClauseState::IndividuallyRenamingAs(from) => {
                if elt.borrow() == &as_atom {
                    state = ParseImportRenameClauseState::IndividuallyRenamingTo(from.clone());
                } else {
                    return Err(CompileErr(elt.loc(), "individual renames are of the form: <a> as <b>".to_string()));
                }
            }
            ParseImportRenameClauseState::IndividuallyRenamingTo(from) => {
                if let SExp::Atom(_, name) = elt.borrow() {
                    state = ParseImportRenameClauseState::Empty;
                    spec.changed.insert(from.clone(), name.clone());
                } else {
                    return Err(CompileErr(elt.loc(), "individual renames are of the form: <a> as <b>".to_string()));
                }
            }
            ParseImportRenameClauseState::DoingExposingOrHiding(exposing) => {
                if let Some(res) = check_exposing_or_hiding(elt) {
                    state = res;
                    continue;
                }

                if let SExp::Atom(_, name) = elt.borrow() {
                    if exposing {
                        spec.to_include.push(name.clone());
                    } else {
                        spec.to_exclude.push(name.clone());
                    }
                } else {
                    return Err(CompileErr(elt.loc(), "Exposing and hiding clauses must be atoms".to_string()));
                }
            }
        }
    }

    Ok(RecognizedImportDirective {
        source: source.clone(),
        spec
    })
}

/// Try to recognize an import directive.
pub fn recognize_import_directive(
    address_from: &ImportLongName,
    form: Rc<SExp>,
) -> Result<Option<RecognizedImportDirective>, CompileErr> {
    let mut relative = false;

    let from_atom = SExp::Atom(form.loc(), b"from".to_vec());
    let import_atom = SExp::Atom(form.loc(), b"import".to_vec());
    let relative_atom = SExp::Atom(form.loc(), b"relative".to_vec());

    if let Some(lst) = form.proper_list() {
        if lst.is_empty() {
            return Ok(None);
        }

        if lst.len() > 0 && lst[0] != from_atom && lst[0] != import_atom {
            return Ok(None);
        }

        // from relative X import
        // from X import
        if lst.len() > 2 && lst[0] == from_atom {
            let (relative, name_idx, rest_idx) =
                if lst[1] == relative_atom {
                    (true, 2, 4)
                } else {
                    (false, 1, 3)
                };

            if name_idx >= lst.len() {
                return Err(CompileErr(form.loc(), "Not enough words to parse import".to_string()));
            }

            if lst[name_idx + 1] != import_atom {
                return Err(CompileErr(lst[name_idx + 1].loc(), "Expected import keyword".to_string()));
            }

            if let SExp::Atom(nl, name) = &lst[name_idx] {
                return finish_import_directive(
                    form.loc(), address_from, relative, &lst, nl.clone(), &name, rest_idx
                ).map(Some);
            }

            return Err(CompileErr(form.loc(), "Name wasn't an atom in import".to_string()));
        }

        // import relative X
        // import X
        if lst.len() > 1 && lst[0] == import_atom {
            let (relative, name_idx) =
                if lst[1] == relative_atom {
                    (true, 2)
                } else {
                    (false, 1)
                };

            if name_idx >= lst.len() {
                return Err(CompileErr(form.loc(), "Not enough words to parse import".to_string()));
            }

            if let SExp::Atom(nl, name) = &lst[name_idx] {
                return finish_import_directive(
                    form.loc(), address_from, relative, &lst, nl.clone(), &name, name_idx + 1
                ).map(Some);
            }

            return Err(CompileErr(form.loc(), "Name wasn't an atom in import".to_string()));
        }
    }

    Err(CompileErr(form.loc(), "Bad import form".to_string()))
}

#[test]
fn test_recognized_import_directive_0() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"()".iter().copied()).expect("should parse");
    assert!(recognize_import_directive(&address_from, parsed[0].clone()).expect("should work").is_none());
}

#[test]
fn test_recognized_import_directive_1() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(test1 test2 test3 test4)".iter().copied()).expect("should parse");
    assert!(recognize_import_directive(&address_from, parsed[0].clone()).expect("should work").is_none());
}

#[test]
fn test_recognized_import_directive_2() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(import)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone());
    assert!(res.is_err());
}

#[test]
fn test_recognized_import_directive_3() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(import relative)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone());
    assert!(res.is_err());
}

#[test]
fn test_recognized_import_directive_4() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(import std.hash)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone()).expect("should have worked").expect("should have an import directive");
    assert_eq!(res.spec.to_sexp().to_string(), "(import std.hash)");
}

#[test]
fn test_recognized_import_directive_5() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(from std.hash import foo as bar)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone()).expect("should have worked").expect("should have an import directive");
    assert_eq!(res.spec.to_sexp().to_string(), "(from std.hash import foo as bar)");
}

#[test]
fn test_recognized_import_directive_6() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(from std.hash import foo as bar exposing baz)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone()).expect("should have worked").expect("should have an import directive");
    assert_eq!(res.spec.to_sexp().to_string(), "(from std.hash import foo as bar exposing baz)");
}

#[test]
fn test_recognized_import_directive_7() {
    let loc = Srcloc::start("*test*");
    let address_from = ImportLongName::from_ident(loc.clone(), b"program").expect("Should parse");
    let parsed = parse_sexp(loc.clone(), b"(from std.hash import foo as bar exposing baz hiding yadda)".iter().copied()).expect("should parse");
    let res = recognize_import_directive(&address_from, parsed[0].clone()).expect("should have worked").expect("should have an import directive");
    assert_eq!(res.spec.to_sexp().to_string(), "(from std.hash import foo as bar hiding yadda exposing baz)");
}

fn compose_fully_qualified_name(source: &ImportLongName, target: &ImportLongName) -> ImportLongName {
    let mut segments: Vec<String> = source.iter().collect();
    segments.append(&mut target.prefix_components.clone());
    ImportLongName {
        prefix_components: segments,
        last_component: target.last_component.clone(),
    }
}

/// Rewrite names from qualified to path names so we can resolve them to filenames.
fn compose_fq_name(sep_char: u8, target: &ImportLongName) -> String {
    let mut composed_name: Vec<u8> = Vec::new();
    let mut sep = vec![];

    let with_separator = |sep: &mut Vec<u8>| {
        sep.clear();
        sep.push(sep_char);
    };

    for t in target.prefix_components.iter() {
        composed_name.append(&mut sep.clone());
        with_separator(&mut sep);
        composed_name.append(&mut t.bytes().collect());
    }

    composed_name.append(&mut sep.clone());
    with_separator(&mut sep);
    composed_name.append(&mut target.last_component.bytes().collect());

    // Stringify
    decode_string(&composed_name)
}

// impl ImportScanner {
//     pub fn new(opts: Rc<dyn CompilerOpts>) -> Self {
//         ImportScanner {
//             opts,
//             reachable_files: HashMap::default(),
//             seen_set: HashSet::new(),
//             visit_queue: Vec::new(),
//             forms_queue: Vec::new(),
//         }
//     }

//     fn scan_forms(&mut self, target: &ImportLongName, pre_forms: &[Rc<SExp>]) {
//         // Multiple forms...  we'll try to iterate them and collect what we can.
//         for form in pre_forms.iter() {
//             if let Some(parsed) = recognize_import_directive(target, form)? {
//                 // Now i have a RecognizedImportDirective.
//                 // It names a new target, which we'll store in our visit queue.
//                 if !seen_set.member(&parsed.target) {
//                     seen_set.insert(parsed.target.clone());
//                     visit_queue.push(parsed);
//                 }
//             } else {
//                 forms_queue.push(form);
//             }
//         }
//     }

//     fn visit_imported_file(&mut self, opts: Rc<dyn CompilerOpts>, recognized: &RecognizedImportDirective) -> Result<(), CompileErr> {
//         let fq_file_name_source =
//             if recognized.relative {
//                 compose_fully_qualified_name(
//                     &recognized.target,
//                     &recognized.source,
//                 )
//             } else {
//                 recognized.target.clone()
//             };

//         let target_file_suffix = compose_fq_file_name(fq_file_name_source, &recognized.target)?;
//         let read_file_data = opts.read_new_file(compose_qualified_name(&recognized.source), &target_file_suffix);
//         let parsed = parse_sexp(Srcloc::start(&target_file_suffix), read_file_data.iter())?;
//         // let scan_result = self.scan_imports_internal(
            
//         // )?;
//         todo!();
//     }

//     fn process_visit_queue_entry(&mut self) -> Result<bool, CompileErr> {
//         if let Some(res) = self.visit_queue.pop() {
//             self.visit_imported_file(res)?;
//         }

//         Ok(false)
//     }

//     fn scan_imports_internal(&mut self, target: &ImportLongName, pre_forms: &[Rc<SExp>]) -> Result<ImportScanResult, CompileErr> {
//         let mut result = ImportScanResult::default();
//         let mut seen_set = HashSet::new();
//         let mut visit_queue = Vec::new();
//         let mut forms_queue = Vec::new();

//         if pre_forms.len() == 1 {
//             if let Some(lst) = pre_forms[0].proper_list() {
//                 if let Ok(res) = self.scan_imports(&lst) {
//                     // It worked as a list containing imports.
//                     return Ok(res);
//                 }
//             }
//         }

//         self.scan_forms(target, pre_forms);

//         while self.process_visit_queue_entry()? { }
//     }

//     /// Simple import scanner
//     ///
//     /// Determines how the file is put together, returns an ImportScanResult which
//     /// contains ImportedFile objects and the built program as a (mod ...) form.
//     pub fn scan_imports(&mut self, pre_forms: &[Rc<SExp>]) -> Result<ImportScanResult, CompileErr> {
//         self.scan_imports_internal(&ImportLongName::default(), pre_forms)
//     }
// }
