use std::collections::HashMap;

use clvmr::allocator::{Allocator, NodePtr, SExp};

use crate::classic::clvm::sexp::proper_list;

use crate::compiler::sexp::decode_string;

/// Specifying how the language is spoken.
#[derive(Clone, Debug, Default)]
pub struct AcceptedDialect {
    pub stepping: Option<i32>,
    pub strict: bool,
}

/// A package containing the content we should insert when a dialect include is
/// used, plus the compilation flags.
#[derive(Clone, Debug)]
pub struct DialectDescription {
    pub accepted: AcceptedDialect,
    pub content: String
}

lazy_static! {
    pub static ref KNOWN_DIALECTS: HashMap<String, DialectDescription> = {
        let mut dialects: HashMap<String, DialectDescription> = HashMap::new();
        let dialect_list = [
            ("*standard-cl-21*", DialectDescription {
                accepted: AcceptedDialect {
                    stepping: Some(21),
                    .. Default::default()
                },
                content: indoc! {"(
                    (defconstant *chialisp-version* 21)
                )"}.to_string()
            }),
            ("*strict-cl-21*", DialectDescription {
                accepted: AcceptedDialect {
                    stepping: Some(21),
                    strict: true
                },
                content: indoc! {"(
                    (defconstant *chialisp-version* 22)
                )"}.to_string()
            }),
            ("*standard-cl-22*", DialectDescription {
                accepted: AcceptedDialect {
                    stepping: Some(22),
                    strict: false
                },
                content: indoc! {"(
                    (defconstant *chialisp-version* 22)
                )"}.to_string()
            }),
            ("*standard-cl-23*", DialectDescription {
                accepted: AcceptedDialect {
                    stepping: Some(23),
                    strict: true
                },
                content: indoc! {"(
                    (defconstant *chialisp-version* 23)
                )"}.to_string()
            }),
        ];
        for (n,v) in dialect_list.iter() {
            dialects.insert(n.to_string(), v.clone());
        }
        dialects
    };
}

fn include_dialect(
    allocator: &mut Allocator,
    e: &[NodePtr],
) -> Option<AcceptedDialect>
{
    if let (SExp::Atom(inc), SExp::Atom(name)) = (allocator.sexp(e[0]), allocator.sexp(e[1])) {
        if allocator.buf(&inc) == "include".as_bytes().to_vec() {
            if let Some(dialect) = KNOWN_DIALECTS.get(&decode_string(&allocator.buf(&name))) {
                return Some(dialect.accepted.clone());
            }
        }
    }

    None
}

pub fn detect_modern(allocator: &mut Allocator, sexp: NodePtr) -> AcceptedDialect {
    let mut result = Default::default();

    if let Some(l) = proper_list(allocator, sexp, true) {
        for elt in l.iter() {
            let detect_modern_result = detect_modern(allocator, *elt);
            if detect_modern_result.stepping.is_some() {
                result = detect_modern_result;
                break;
            }

            match proper_list(allocator, *elt, true) {
                None => {
                    continue;
                }

                Some(e) => {
                    if e.len() != 2 {
                        continue;
                    }

                    if let Some(dialect) = include_dialect(allocator, &e) {
                        result = dialect;
                        break;
                    }
                }
            }
        }
    }

    result
}