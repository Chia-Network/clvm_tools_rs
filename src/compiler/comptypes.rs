use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use serde::Serialize;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};

use crate::compiler::clvm::{sha256tree, truthy};
use crate::compiler::dialect::AcceptedDialect;
use crate::compiler::sexp::{decode_string, enlist, SExp};
use crate::compiler::srcloc::Srcloc;
use crate::compiler::typecheck::TheoryToSExp;
use crate::compiler::types::ast::{Polytype, TypeVar};
use crate::compiler::BasicCompileContext;
use crate::util::Number;

// Note: only used in tests, not normally dependencies.
#[cfg(test)]
use crate::compiler::compiler::DefaultCompilerOpts;
#[cfg(test)]
use crate::compiler::frontend::compile_bodyform;
#[cfg(test)]
use crate::compiler::sexp::parse_sexp;

/// The basic error type.  It contains a Srcloc identifying coordinates of the
/// error in the source file and a message.  It probably should be made even better
/// but this works ok.
#[derive(Clone, Debug)]
pub struct CompileErr(pub Srcloc, pub String);

impl From<(Srcloc, String)> for CompileErr {
    fn from(err: (Srcloc, String)) -> Self {
        CompileErr(err.0, err.1)
    }
}

/// A structure carrying a compilation result to give it a distinct type from
/// chialisp input.  It's used by codegen.
#[derive(Clone, Debug)]
pub struct CompiledCode(pub Srcloc, pub Rc<SExp>);

/// A description of an inlined function for use during inline expansion.
/// This is used only by PrimaryCodegen.
#[derive(Clone, Debug)]
pub struct InlineFunction {
    pub name: Vec<u8>,
    pub args: Rc<SExp>,
    pub body: Rc<BodyForm>,
}

impl InlineFunction {
    pub fn to_sexp(&self) -> Rc<SExp> {
        Rc::new(SExp::Cons(
            self.body.loc(),
            self.args.clone(),
            self.body.to_sexp(),
        ))
    }
}

/// Specifies the type of application that any form (X ...) invokes in an
/// expression position.
#[derive(Debug, Clone)]
pub enum Callable {
    /// The expression is a macro expansion (list, if etc.)
    CallMacro(Srcloc, SExp),
    /// The expression invokes an env defun.
    CallDefun(Srcloc, SExp),
    /// The expression expands and inline function.
    CallInline(Srcloc, InlineFunction),
    /// The expression addresses a clvm primitive (such as a, c, f, =)
    CallPrim(Srcloc, SExp),
    /// The expression is a (com ...) invokcation (normally used in macros).
    RunCompiler,
    /// The expression is an (@ n) form that directly references the environment.
    EnvPath,
}

/// Given a slice of SExp values, generate a proper list containing them.
pub fn list_to_cons(l: Srcloc, list: &[Rc<SExp>]) -> SExp {
    if list.is_empty() {
        return SExp::Nil(l);
    }

    let mut result = SExp::Nil(l);
    for i_reverse in 0..list.len() {
        let i = list.len() - i_reverse - 1;
        result = SExp::Cons(list[i].loc(), list[i].clone(), Rc::new(result));
    }

    result
}

/// Specifies the pattern that is destructured in let bindings.
#[derive(Clone, Debug, Serialize)]
pub enum BindingPattern {
    /// The whole expression is bound to this name.
    Name(Vec<u8>),
    /// Specifies a tree of atoms into which the value will be destructured.
    Complex(Rc<SExp>),
}

/// If present, states an intention for desugaring of this let form to favor
/// inlining or functions.
#[derive(Clone, Debug, Serialize)]
pub enum LetFormInlineHint {
    NoChoice,
    Inline(Srcloc),
    NonInline(Srcloc),
}

/// A binding from a (let ...) form.  Specifies the name of the bound variable
/// the location of the whole binding form, the location of the name atom (nl)
/// and the body as a BodyForm (which are chialisp expressions).
#[derive(Clone, Debug, Serialize)]
pub struct Binding {
    /// Overall location of the form.
    pub loc: Srcloc,
    /// Location of the name atom specifically.
    pub nl: Srcloc,
    /// Specifies the pattern which is extracted from the expression, which can
    /// be a Name (a single name names the whole subexpression) or Complex which
    /// can destructure and is used in code that extends cl21 past the definition
    /// of the language at that point.
    pub pattern: BindingPattern,
    /// The expression the binding refers to.
    pub body: Rc<BodyForm>,
}

/// Determines how a let binding is bound.  Parallel means that the bindings do
/// not depend on each other and aren't in scope for each other.  Sequential
/// is like lisp's let* form in that each binding has the previous ones in scope
/// for itself.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum LetFormKind {
    Parallel,
    Sequential,
    Assign,
}

/// Information about a let form.  Encapsulates everything except whether it's
/// parallel or sequential, which is left in the BodyForm itself.
#[derive(Clone, Debug, Serialize)]
pub struct LetData {
    /// The location of the form overall.
    pub loc: Srcloc,
    /// The location specifically of the let or let* keyword.
    pub kw: Option<Srcloc>,
    /// Inline hint.
    pub inline_hint: Option<LetFormInlineHint>,
    /// The bindings introduced.
    pub bindings: Vec<Rc<Binding>>,
    /// The expression evaluated in the context of all the bindings.
    pub body: Rc<BodyForm>,
}

/// Describes a lambda used in an expression.
#[derive(Clone, Debug, Serialize)]
pub struct LambdaData {
    pub loc: Srcloc,
    pub kw: Option<Srcloc>,
    pub capture_args: Rc<SExp>,
    pub captures: Rc<BodyForm>,
    pub args: Rc<SExp>,
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug, Serialize)]
pub enum BodyForm {
    /// A let or let* form (depending on LetFormKind).
    Let(LetFormKind, Box<LetData>),
    /// An explicitly quoted constant of some kind.
    Quoted(SExp),
    /// An undiferentiated "value" of some kind in the source language.
    /// If this refers to an atom, then it is a variable reference of some kind,
    /// otherwise it refers to a self-quoting value (like a quoted string or int).
    Value(SExp),
    /// An application of some kind, parsed from a proper list.
    /// This is a proper list because of the ambiguity of the final value in an
    /// improper list.  While it's possible to treat a final atom
    ///
    /// (x y . z)
    ///
    /// as an argument that matches a tail argument, there's no way to write
    ///
    /// (x y . (+ 1 z))
    ///
    /// So tail improper calls aren't allowed.  In real lisp, (apply ...) can
    /// generate them if needed.
    Call(Srcloc, Vec<Rc<BodyForm>>, Option<Rc<BodyForm>>),
    /// (mod ...) can be used in chialisp as an expression, in which it returns
    /// the compiled code.  Here, it contains a CompileForm, which represents
    /// the full significant input of a program (yielded by frontend()).
    Mod(Srcloc, CompileForm),
    /// A lambda form (lambda (...) ...)
    ///
    /// The lambda arguments are in two parts:
    ///
    /// (lambda ((& captures) real args) ...)
    ///
    /// Where the parts in captures are captured from the hosting environment.
    /// Captures are optional.
    /// The real args are given in the indicated shape when the lambda is applied
    /// with the 'a' operator.
    Lambda(Box<LambdaData>),
}

#[derive(Clone, Debug, Serialize)]
pub enum SyntheticType {
    NoInlinePreference,
    MaybeRecursive,
    WantInline,
    WantNonInline,
}

/// The information needed to know about a defun.  Whether it's inline is left in
/// the HelperForm.
#[derive(Clone, Debug, Serialize)]
pub struct DefunData {
    /// The location of the helper form.
    pub loc: Srcloc,
    /// The name of the defun.
    pub name: Vec<u8>,
    /// The location of the keyword used in the defun.
    pub kw: Option<Srcloc>,
    /// The location of the name of the defun.
    pub nl: Srcloc,
    /// The arguments as originally given by the user.
    pub orig_args: Rc<SExp>,
    /// The argument spec for the defun with any renaming.
    pub args: Rc<SExp>,
    /// The body expression of the defun.
    pub body: Rc<BodyForm>,
    /// Whether this defun was created during desugaring.
    pub synthetic: Option<SyntheticType>,
    /// Type annotation if given.
    pub ty: Option<Polytype>,
}

/// Specifies the information extracted from a macro definition allowing the
/// compiler to expand code using it.
#[derive(Clone, Debug, Serialize)]
pub struct DefmacData {
    /// The location of the macro.
    pub loc: Srcloc,
    /// The name of the macro.
    pub name: Vec<u8>,
    /// The locaton of the keyword used to define the macro.
    pub kw: Option<Srcloc>,
    /// The location of the macro's name.
    pub nl: Srcloc,
    /// The argument spec.
    pub args: Rc<SExp>,
    /// The program appearing in the macro definition.
    pub program: Rc<CompileForm>,
    /// Whether this is an an advanced macro.
    pub advanced: bool,
}

/// Information from a constant definition.
#[derive(Clone, Debug, Serialize)]
pub struct DefconstData {
    /// The location of the constant form.
    pub loc: Srcloc,
    /// Specifies whether the constant is a simple quoted sexp or is specified
    /// by an expression.  This allows us to delay constant evaluation until we
    /// have the whole program.
    pub kind: ConstantKind,
    /// The name of constant.
    pub name: Vec<u8>,
    /// The location of the keyword in the definition.
    pub kw: Option<Srcloc>,
    /// The location of the name in the definition.
    pub nl: Srcloc,
    /// The location of the body expression, whatever it is.
    pub body: Rc<BodyForm>,
    /// This constant should exist in the left env rather than be inlined.
    pub tabled: bool,
    /// Type annotation if given.
    pub ty: Option<Polytype>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StructMember {
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub path: Number,
    pub ty: Polytype,
}

#[derive(Clone, Debug, Serialize)]
pub struct StructDef {
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub vars: Vec<TypeVar>,
    pub members: Vec<StructMember>,
    pub proto: Rc<SExp>,
    pub ty: Polytype,
}

#[derive(Clone, Debug, Serialize)]
pub enum ChiaType {
    Abstract(Srcloc, Vec<u8>),
    Struct(StructDef),
}

#[derive(Clone, Debug)]
pub enum TypeAnnoKind {
    Colon(Polytype),
    Arrow(Polytype),
}

#[derive(Clone, Debug, Serialize)]
pub struct DeftypeData {
    pub kw: Srcloc,
    pub nl: Srcloc,
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub args: Vec<TypeVar>,
    pub parsed: ChiaType,
    pub ty: Option<Polytype>,
}

/// Specifies where a constant is the classic kind (unevaluated) or a proper
/// expression.
#[derive(Clone, Debug, Serialize)]
pub enum ConstantKind {
    Complex,
    Simple,
    /// Module toplevel constants have extra guarantees which need a different
    /// resolution style.
    Module,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct ImportLongName {
    pub components: Vec<Vec<u8>>,
}

#[derive(Debug, Clone)]
pub enum LongNameTranslation {
    Namespace,
    Filename(String),
}

impl ImportLongName {
    pub fn parse(name: &[u8]) -> (bool, Self) {
        let (relative, skip_words) = if name.starts_with(b".") {
            (true, 1)
        } else {
            (false, 0)
        };

        let components = name
            .split(|ch| *ch == b'.')
            .skip(skip_words)
            .map(|x| x.to_vec())
            .collect();
        (relative, ImportLongName { components })
    }

    pub fn as_u8_vec(&self, filename: LongNameTranslation) -> Vec<u8> {
        let mut result_vec = vec![];
        let sep = if matches!(filename, LongNameTranslation::Filename(_)) {
            b'/'
        } else {
            b'.'
        };
        for (i, c) in self.components.iter().enumerate() {
            if i != 0 {
                result_vec.push(sep);
            }
            result_vec.extend(c.clone());
        }
        if let LongNameTranslation::Filename(ext) = &filename {
            result_vec.extend(ext.as_bytes().to_vec());
        }
        result_vec
    }

    pub fn combine(&self, with: &ImportLongName) -> Self {
        let mut result = self.components.clone();
        result.extend(with.components.clone());
        ImportLongName { components: result }
    }

    /// True if parent namespace contains self.
    pub fn is_contained_by(&self, parent: &ImportLongName) -> bool {
        if self.components.len() < parent.components.len() {
            return false;
        }

        for (i, p) in parent.components.iter().enumerate() {
            if self.components[i] != *p {
                return false;
            }
        }

        true
    }

    pub fn with_child(&self, name: &[u8]) -> Self {
        let mut result = self.components.clone();
        result.push(name.to_vec());
        ImportLongName { components: result }
    }

    pub fn parent(&self) -> Option<Self> {
        if self.components.len() < 2 {
            return None;
        }

        Some(ImportLongName {
            components: self
                .components
                .iter()
                .take(self.components.len() - 1)
                .cloned()
                .collect(),
        })
    }

    pub fn parent_and_name(&self) -> (Option<Self>, Vec<u8>) {
        if self.components.is_empty() {
            return (None, vec![]);
        }

        if self.components.len() > 1 {
            return (
                Some(ImportLongName {
                    components: self
                        .components
                        .iter()
                        .take(self.components.len() - 1)
                        .cloned()
                        .collect(),
                }),
                self.components[self.components.len() - 1].clone(),
            );
        }

        (None, self.components[0].clone())
    }
}

/// If specified, info about the qualified module import target.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct QualifiedModuleInfoTarget {
    pub nl: Srcloc,
    pub kw: Srcloc,
    pub relative: bool,
    pub name: ImportLongName,
}

/// Import qualified information
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct QualifiedModuleInfo {
    pub loc: Srcloc,
    pub nl: Srcloc,
    pub kw: Srcloc,
    pub name: ImportLongName,
    pub target: Option<QualifiedModuleInfoTarget>,
}

/// Information about a name listed after hiding or exposing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ModuleImportListedName {
    pub nl: Srcloc,
    pub name: Vec<u8>,
    pub alias: Option<Vec<u8>>,
}

impl ModuleImportListedName {
    pub fn to_sexp(&self) -> Rc<SExp> {
        let as_atom = Rc::new(SExp::Atom(self.nl.clone(), b"as".to_vec()));
        let name_atom = Rc::new(SExp::Atom(self.nl.clone(), self.name.clone()));
        if let Some(alias) = self.alias.as_ref() {
            Rc::new(SExp::Cons(
                self.nl.clone(),
                name_atom,
                Rc::new(SExp::Cons(
                    self.nl.clone(),
                    as_atom.clone(),
                    Rc::new(SExp::Cons(
                        self.nl.clone(),
                        Rc::new(SExp::Atom(self.nl.clone(), alias.clone())),
                        Rc::new(SExp::Nil(self.nl.clone())),
                    )),
                )),
            ))
        } else {
            name_atom
        }
    }
}

/// Specification of how to name imported items from the target namespace.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ModuleImportSpec {
    /// As import qualified [as ...] in haskell.
    Qualified(Box<QualifiedModuleInfo>),
    /// The given names are in the toplevel namespace after the import.
    Exposing(Srcloc, Vec<ModuleImportListedName>),
    /// All but these names are in the toplevel namespace after the import.
    Hiding(Srcloc, Vec<ModuleImportListedName>),
}

pub fn match_as_named(lst: &[SExp], offset: usize) -> Option<(Srcloc, Vec<u8>, Option<Vec<u8>>)> {
    let name_offset = offset;
    let small = 1 + offset;
    let as_kw = 1 + offset;
    let as_name_offset = 2 + offset;
    let large = 3 + offset;

    if lst.len() != small && lst.len() != large {
        return None;
    }

    let export_name = if lst.len() == large {
        if let SExp::Atom(_, as_atom) = lst[as_kw].borrow() {
            // Not 'as'
            if as_atom != b"as" {
                return None;
            }
        } else {
            return None;
        }

        if let SExp::Atom(_, as_name) = lst[as_name_offset].borrow() {
            Some(as_name.clone())
        } else {
            return None;
        }
    } else {
        None
    };

    let from_name = if let SExp::Atom(_, from_name) = lst[name_offset].borrow() {
        from_name.clone()
    } else {
        return None;
    };

    Some((lst[name_offset].loc(), from_name, export_name))
}

impl ModuleImportSpec {
    pub fn name_loc(&self) -> Srcloc {
        match self {
            ModuleImportSpec::Qualified(q) => q.nl.clone(),
            ModuleImportSpec::Exposing(e, _) => e.clone(),
            ModuleImportSpec::Hiding(e, _) => e.clone(),
        }
    }

    pub fn parse(
        loc: Srcloc,
        kw: Srcloc,
        forms: &[SExp],
        mut skip: usize,
    ) -> Result<Self, CompileErr> {
        if skip >= forms.len() {
            return Ok(ModuleImportSpec::Hiding(loc, vec![]));
        }

        // Figure out whether it's "import qualified" or
        // "import qualified foo as bar"
        let (first_loc, first_atom) = if let SExp::Atom(first_loc, first) = &forms[skip] {
            (first_loc.clone(), first.clone())
        } else {
            return Err(CompileErr(
                forms[skip].loc(),
                "import must be followed by a name or 'qualified'".to_string(),
            ));
        };

        if first_atom == b"qualified" {
            if forms.len() < 3 {
                return Err(CompileErr(
                    loc.clone(),
                    "import qualified must be followed by a name".to_string(),
                ));
            }

            let (second_loc, second_atom) = if let SExp::Atom(second_loc, second) = &forms[2] {
                (second_loc.clone(), second.clone())
            } else {
                return Err(CompileErr(
                    forms[2].loc(),
                    "import qualified must be followed by a name".to_string(),
                ));
            };

            let (_, p) = ImportLongName::parse(&second_atom);

            if forms.len() == 5 {
                let qname = if let SExp::Atom(_, qname) = &forms[4] {
                    qname.clone()
                } else {
                    return Err(CompileErr(
                        forms[4].loc(),
                        "import qualified ... as qname must be a name".to_string(),
                    ));
                };

                let (relative_qual, import_name) = ImportLongName::parse(&qname);

                return Ok(ModuleImportSpec::Qualified(Box::new(QualifiedModuleInfo {
                    loc: loc.clone(),
                    kw: first_loc.clone(),
                    nl: second_loc.clone(),
                    name: p,
                    target: Some(QualifiedModuleInfoTarget {
                        kw: forms[3].loc(),
                        nl: forms[4].loc(),
                        relative: relative_qual,
                        name: import_name,
                    }),
                })));
            } else if forms.len() == 3 {
                return Ok(ModuleImportSpec::Qualified(Box::new(QualifiedModuleInfo {
                    loc: loc.clone(),
                    kw: kw.clone(),
                    nl: second_loc.clone(),
                    name: p,
                    target: None,
                })));
            }
        }

        skip += 1;

        if skip >= forms.len() {
            return Ok(ModuleImportSpec::Hiding(loc, vec![]));
        }

        if let SExp::Atom(kw_loc, kw) = &forms[skip] {
            let mut words = vec![];
            for atom in forms.iter().skip(skip + 1) {
                if let Some((import_name_loc, import_name, export_name)) =
                    atom.proper_list().and_then(|lst| match_as_named(&lst, 0))
                {
                    words.push(ModuleImportListedName {
                        nl: import_name_loc,
                        name: import_name,
                        alias: export_name,
                    });
                } else if let SExp::Atom(name_loc, name) = atom {
                    words.push(ModuleImportListedName {
                        nl: name_loc.clone(),
                        name: name.clone(),
                        alias: None,
                    });
                } else {
                    return Err(CompileErr(
                        atom.loc(),
                        "Exposed names must be atoms".to_string(),
                    ));
                }
            }
            if kw == b"exposing" {
                return Ok(ModuleImportSpec::Exposing(kw_loc.clone(), words));
            } else if kw == b"hiding" {
                return Ok(ModuleImportSpec::Hiding(loc, words));
            }
        }

        Err(CompileErr(
            forms[skip].loc(),
            format!("Bad keyword {} in import", forms[skip]),
        ))
    }

    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            ModuleImportSpec::Qualified(as_name) => {
                let mut result_vec = vec![
                    Rc::new(SExp::Atom(as_name.kw.clone(), b"qualified".to_vec())),
                    Rc::new(SExp::Atom(
                        as_name.nl.clone(),
                        as_name.name.as_u8_vec(LongNameTranslation::Namespace),
                    )),
                ];
                if let Some(target) = as_name.target.as_ref() {
                    result_vec.push(Rc::new(SExp::Atom(target.kw.clone(), b"as".to_vec())));
                    result_vec.push(Rc::new(SExp::Atom(
                        target.nl.clone(),
                        target.name.as_u8_vec(LongNameTranslation::Namespace),
                    )));
                }
                Rc::new(enlist(as_name.loc.clone(), &result_vec))
            }
            ModuleImportSpec::Exposing(kl, exposed_names) => {
                let mut result_vec = vec![Rc::new(SExp::Atom(kl.clone(), b"exposing".to_vec()))];
                result_vec.extend(
                    exposed_names
                        .iter()
                        .map(|e| e.to_sexp())
                        .collect::<Vec<Rc<SExp>>>(),
                );
                Rc::new(enlist(kl.clone(), &result_vec))
            }
            // All but these names are in the toplevel namespace after the import.
            ModuleImportSpec::Hiding(kl, hidden_names) => {
                if hidden_names.is_empty() {
                    return Rc::new(SExp::Nil(kl.clone()));
                }

                let mut result_vec = vec![Rc::new(SExp::Atom(kl.clone(), b"hiding".to_vec()))];
                result_vec.extend(
                    hidden_names
                        .iter()
                        .map(|e| Rc::new(SExp::Atom(e.nl.clone(), e.name.clone())))
                        .collect::<Vec<Rc<SExp>>>(),
                );
                Rc::new(enlist(kl.clone(), &result_vec))
            }
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct NamespaceData {
    pub loc: Srcloc,
    pub kw: Srcloc,
    pub nl: Srcloc,
    pub rendered_name: Vec<u8>,
    pub longname: ImportLongName,
    pub helpers: Vec<HelperForm>,
}

#[derive(Clone, Debug, Serialize)]
pub struct NamespaceRefData {
    pub loc: Srcloc,
    pub kw: Srcloc,
    pub nl: Srcloc,
    pub rendered_name: Vec<u8>,
    pub longname: ImportLongName,
    pub specification: ModuleImportSpec,
}

/// HelperForm is a toplevel binding of some kind.
/// Helpers are the (defconst ...) (defun ...) (defun-inline ...) (defmacro ...)
/// forms from the source code and "help" the program do its job.  They're
/// individually parsable and represent the atomic units of the program.
#[derive(Clone, Debug, Serialize)]
pub enum HelperForm {
    /// A type definition.
    Deftype(DeftypeData),
    /// A namespace collection.
    Defnamespace(NamespaceData),
    /// A namespace reference.
    Defnsref(Box<NamespaceRefData>),
    /// A constant definition (see DefconstData).
    Defconstant(DefconstData),
    /// A macro definition (see DefmacData).
    Defmacro(DefmacData),
    /// A function definition (see DefunData).
    Defun(bool, DefunData),
}

#[test]
fn test_helperform_import_qualified_0() {
    let srcloc = Srcloc::start("*test-import*");
    let (_, name) = ImportLongName::parse(b"foo.bar");
    assert_eq!(
        HelperForm::Defnsref(Box::new(NamespaceRefData {
            loc: srcloc.clone(),
            kw: srcloc.clone(),
            nl: srcloc.clone(),
            rendered_name: name.as_u8_vec(LongNameTranslation::Namespace),
            longname: name.clone(),
            specification: ModuleImportSpec::Qualified(Box::new(QualifiedModuleInfo {
                loc: srcloc.clone(),
                nl: srcloc.clone(),
                kw: srcloc.clone(),
                name: name,
                target: None,
            }))
        }))
        .to_sexp()
        .to_string(),
        "(import qualified foo.bar)"
    );
}

#[test]
fn test_helperform_import_qualified_1() {
    let srcloc = Srcloc::start("*test-import*");
    let (_, name) = ImportLongName::parse(b"foo.bar");
    let (relative, target) = ImportLongName::parse(b"FB");

    assert_eq!(
        HelperForm::Defnsref(Box::new(NamespaceRefData {
            loc: srcloc.clone(),
            kw: srcloc.clone(),
            nl: srcloc.clone(),
            rendered_name: name.as_u8_vec(LongNameTranslation::Namespace),
            longname: name.clone(),
            specification: ModuleImportSpec::Qualified(Box::new(QualifiedModuleInfo {
                loc: srcloc.clone(),
                nl: srcloc.clone(),
                kw: srcloc.clone(),
                name: name,
                target: Some(QualifiedModuleInfoTarget {
                    kw: srcloc.clone(),
                    nl: srcloc.clone(),
                    name: target,
                    relative
                })
            }))
        }))
        .to_sexp()
        .to_string(),
        "(import qualified foo.bar as FB)"
    );
}

/// To what purpose is the file included.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum IncludeProcessType {
    /// Include the bytes on disk as an atom.
    Bin,
    /// Parse the hex on disk and present it as a clvm value.
    Hex,
    /// Read clvm in s-expression form as a clvm value.
    SExpression,
    /// Compile a full program and return its representation.
    Compiled,
    /// Import as a module.
    Module(Box<ModuleImportSpec>),
}

/// A description of an include form.  Here, records the locations of the various
/// parts of the include so they can be marked in the language server and be
/// subject to other kind of reporting if desired.
#[derive(Clone, Debug, Serialize)]
pub struct IncludeDesc {
    /// Location of the keyword introducing this form.
    pub kw: Srcloc,
    /// Location of the name of the file.
    pub nl: Srcloc,
    /// The relative path to a target or a special directive name.
    pub name: Vec<u8>,
    /// Kind of inclusion.  Determines whether dependencies are recursed and
    /// what operation is performed on the retrieved clvm form.
    pub kind: Option<IncludeProcessType>,
}

impl IncludeDesc {
    pub fn to_sexp(&self) -> Rc<SExp> {
        if let Some(IncludeProcessType::Module(_spec)) = &self.kind {
            Rc::new(SExp::Cons(
                self.kw.clone(),
                Rc::new(SExp::Atom(self.kw.clone(), b"module".to_vec())),
                Rc::new(SExp::QuotedString(self.nl.clone(), b'"', self.name.clone())),
            ))
        } else {
            Rc::new(SExp::Cons(
                self.kw.clone(),
                Rc::new(SExp::Atom(self.kw.clone(), b"include".to_vec())),
                Rc::new(SExp::QuotedString(self.nl.clone(), b'"', self.name.clone())),
            ))
        }
    }
}

/// An encoding of a complete program.  This includes all the include forms
/// traversed (for marking in a language server), the argument spec of the program,
/// the list of helper declarations and the expression serving as the "main"
/// program.
#[derive(Clone, Debug, Serialize)]
pub struct CompileForm {
    /// Location of the form that was collected into this object.
    pub loc: Srcloc,
    /// List of include directives.
    pub include_forms: Vec<IncludeDesc>,
    /// Argument spec.
    pub args: Rc<SExp>,
    /// List of declared helpers encountered.  Unless the CompilerOpts is directed
    /// to preserve all helpers, helpers not used by a toplevel defun or the main
    /// expression (those needed by the finished code) are not included.  The
    /// set_frontend_check_live method of CompilerOpts allows this to be changed.
    pub helpers: Vec<HelperForm>,
    /// The expression the program evaluates, using the declared helpers.
    pub exp: Rc<BodyForm>,
    /// Type if specified.
    pub ty: Option<Polytype>,
}

/// Represents a call to a defun, used by code generation.
#[derive(Clone, Debug)]
pub struct DefunCall {
    pub required_env: Rc<SExp>,
    pub code: Rc<SExp>,
}

/// PrimaryCodegen is an object used by codegen to accumulate and use state needed
/// during code generation.  It's mostly used internally.
#[derive(Clone, Debug)]
pub struct PrimaryCodegen {
    pub prims: Rc<HashMap<Vec<u8>, Rc<SExp>>>,
    pub constants: HashMap<Vec<u8>, Rc<SExp>>,
    pub tabled_constants: HashMap<Vec<u8>, Rc<SExp>>,
    pub module_constants: HashMap<Vec<u8>, Rc<BodyForm>>,
    pub macros: HashMap<Vec<u8>, Rc<SExp>>,
    pub inlines: HashMap<Vec<u8>, InlineFunction>,
    pub defuns: HashMap<Vec<u8>, DefunCall>,
    pub parentfns: HashSet<Vec<u8>>,
    pub env: Rc<SExp>,
    pub to_process: Vec<HelperForm>,
    pub original_helpers: Vec<HelperForm>,
    pub final_expr: Rc<BodyForm>,
    pub final_env: Rc<SExp>,
    pub final_code: Option<CompiledCode>,
    pub function_symbols: HashMap<String, String>,
    pub left_env: bool,
}

/// The CompilerOpts specifies global options used during compilation.
/// CompilerOpts is used whenever interaction with the compilation infrastructure
/// is needed that has options or needs guidance.
pub trait CompilerOpts {
    /// The toplevel file begin compiled.
    fn filename(&self) -> String;
    /// A PrimaryCodegen that can be donated to downstream use.  It can be the
    /// case that the state of compilation needs to be passed down in a specific
    /// form, such as when a lambda is used (coming soon), when evaluating
    /// complex constants, and into (com ...) forms.  This allows the CompilerOpts
    /// to carry this info across boundaries into a new context.
    fn code_generator(&self) -> Option<PrimaryCodegen>;
    /// Get the dialect declared in the toplevel program.
    fn dialect(&self) -> AcceptedDialect;
    /// Disassembly version (for disassembly style serialization)
    fn disassembly_ver(&self) -> Option<usize>;
    /// Specifies whether code is being generated on behalf of an inner defun in
    /// the program.
    fn in_defun(&self) -> bool;
    /// Specifies whether the standard environment is injected (list, if etc).
    fn stdenv(&self) -> bool;
    /// Specifies whether certain basic optimizations are done during and after
    /// code generation.
    fn optimize(&self) -> bool;
    /// Specifies whether the frontend code is to be optimized before code
    /// generation.  This can simplify code from the user and decide on inlining
    /// of desugared forms.
    fn frontend_opt(&self) -> bool;
    /// Specifies whether forms not reachable at runtime are included in the
    /// resulting CompileForm.
    fn frontend_check_live(&self) -> bool;
    /// Specifies the shape of the environment to use.  This allows injection of
    /// the parent program's left environment when some form is compiled in the
    /// parent's context.
    fn start_env(&self) -> Option<Rc<SExp>>;
    /// Specifies the map of primitives provided during this compilation.
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>>;
    /// Specifies the search paths we're carrying.
    fn get_search_paths(&self) -> Vec<String>;

    /// Set main file, creating an opts that treats this file as its main file.
    fn set_filename(&self, new_file: &str) -> Rc<dyn CompilerOpts>;
    /// Set the dialect.
    fn set_dialect(&self, dialect: AcceptedDialect) -> Rc<dyn CompilerOpts>;
    /// Set search paths.
    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts>;
    /// Set disassembly version for.
    fn set_disassembly_ver(&self, ver: Option<usize>) -> Rc<dyn CompilerOpts>;
    /// Set whether we're compiling on behalf of a defun.
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts>;
    /// Set whether to inject the standard environment.
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts>;
    /// Set whether to run codegen optimization.
    fn set_optimize(&self, opt: bool) -> Rc<dyn CompilerOpts>;
    /// Set whether to run frontend optimization.
    fn set_frontend_opt(&self, opt: bool) -> Rc<dyn CompilerOpts>;
    /// Set whether to filter out each HelperForm that isn't reachable at
    /// run time.
    fn set_frontend_check_live(&self, check: bool) -> Rc<dyn CompilerOpts>;
    /// Set the codegen object to be used downstream.
    fn set_code_generator(&self, new_compiler: PrimaryCodegen) -> Rc<dyn CompilerOpts>;
    /// Set the environment shape to assume.
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts>;
    /// Set the primitive map in use so we can add custom primitives.
    fn set_prim_map(&self, new_map: Rc<HashMap<Vec<u8>, Rc<SExp>>>) -> Rc<dyn CompilerOpts>;

    /// Using the search paths list we have, try to read a file by name,
    /// Returning the expanded path to the file and its content.
    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, Vec<u8>), CompileErr>;

    /// Fully write a file to the filesystem.
    fn write_new_file(&self, target_path: &str, content: &[u8]) -> Result<(), CompileErr>;

    /// Given a parsed SExp, compile it as an independent program based on the
    /// settings given here.  The result is bare generated code.
    fn compile_program(
        &self,
        context: &mut BasicCompileContext,
        sexp: Rc<SExp>,
    ) -> Result<CompilerOutput, CompileErr>;
}

/// Frontend uses this to accumulate frontend forms, used internally.
#[derive(Debug, Clone)]
pub struct ModAccum {
    pub loc: Srcloc,
    pub includes: Vec<IncludeDesc>,
    pub helpers: Vec<HelperForm>,
    pub left_capture: bool,
    pub exp_form: Option<CompileForm>,
}

/// A specification of a function call including elements useful for evaluation.
#[derive(Debug, Clone)]
pub struct CallSpec<'a> {
    pub loc: Srcloc,
    pub name: &'a [u8],
    pub args: &'a [Rc<BodyForm>],
    pub tail: Option<Rc<BodyForm>>,
    pub original: Rc<BodyForm>,
}

/// Raw callspec for use in codegen.
#[derive(Debug, Clone)]
pub struct RawCallSpec<'a> {
    pub loc: Srcloc,
    pub args: &'a [Rc<BodyForm>],
    pub tail: Option<Rc<BodyForm>>,
    pub original: Rc<BodyForm>,
}

/// A pair of arguments and an optional tail for function calls.  The tail is
/// a function tail given by a final &rest argument.
#[derive(Debug, Default, Clone)]
pub struct ArgsAndTail {
    pub args: Vec<Rc<BodyForm>>,
    pub tail: Option<Rc<BodyForm>>,
}

impl ModAccum {
    pub fn set_final(&self, c: &CompileForm) -> Self {
        ModAccum {
            loc: self.loc.clone(),
            includes: self.includes.clone(),
            helpers: self.helpers.clone(),
            left_capture: self.left_capture,
            exp_form: Some(c.clone()),
        }
    }

    pub fn add_include(&self, i: IncludeDesc) -> Self {
        let mut new_includes = self.includes.clone();
        new_includes.push(i);
        ModAccum {
            loc: self.loc.clone(),
            includes: new_includes,
            helpers: self.helpers.clone(),
            left_capture: self.left_capture,
            exp_form: self.exp_form.clone(),
        }
    }

    pub fn add_helper(&self, h: HelperForm) -> Self {
        let mut hs = self.helpers.clone();
        hs.push(h);

        ModAccum {
            loc: self.loc.clone(),
            includes: self.includes.clone(),
            helpers: hs,
            left_capture: self.left_capture,
            exp_form: self.exp_form.clone(),
        }
    }

    pub fn new(loc: Srcloc, left_capture: bool) -> ModAccum {
        ModAccum {
            loc,
            includes: Vec::new(),
            helpers: Vec::new(),
            left_capture,
            exp_form: None,
        }
    }
}

impl CompileForm {
    /// Get the location of the compileform.
    pub fn loc(&self) -> Srcloc {
        self.loc.clone()
    }

    /// Express the contents as an SExp.  This SExp does not come with a keyword
    /// but starts at the arguments, since CompileForm objects are used in the
    /// encoding of several other types.
    pub fn to_sexp(&self) -> Rc<SExp> {
        let mut sexp_forms: Vec<Rc<SExp>> = self.helpers.iter().map(|x| x.to_sexp()).collect();
        sexp_forms.push(self.exp.to_sexp());

        Rc::new(SExp::Cons(
            self.loc.clone(),
            self.args.clone(),
            Rc::new(list_to_cons(self.loc.clone(), &sexp_forms)),
        ))
    }

    /// Given a set of helpers by name, remove them.
    pub fn remove_helpers(&self, names: &HashSet<Vec<u8>>) -> CompileForm {
        CompileForm {
            loc: self.loc.clone(),
            args: self.args.clone(),
            include_forms: self.include_forms.clone(),
            helpers: self
                .helpers
                .iter()
                .filter(|h| !names.contains(h.name()))
                .cloned()
                .collect(),
            exp: self.exp.clone(),
            ty: self.ty.clone(),
        }
    }

    /// Given a list of helpers, introduce them in this CompileForm, removing
    /// conflicting predecessors.
    pub fn replace_helpers(&self, helpers: &[HelperForm]) -> CompileForm {
        let mut new_names = HashSet::new();
        for h in helpers.iter() {
            new_names.insert(h.name());
        }
        let mut new_helpers: Vec<HelperForm> = self
            .helpers
            .iter()
            .filter(|h| !new_names.contains(h.name()))
            .cloned()
            .collect();
        new_helpers.append(&mut helpers.to_vec());

        CompileForm {
            loc: self.loc.clone(),
            include_forms: self.include_forms.clone(),
            args: self.args.clone(),
            helpers: new_helpers,
            exp: self.exp.clone(),
            ty: self.ty.clone(),
        }
    }
}

pub fn generate_defmacro_sexp(mac: &DefmacData) -> Rc<SExp> {
    if mac.advanced {
        Rc::new(SExp::Cons(
            mac.loc.clone(),
            Rc::new(SExp::atom_from_string(mac.loc.clone(), "defmac")),
            Rc::new(SExp::Cons(
                mac.loc.clone(),
                Rc::new(SExp::atom_from_vec(mac.nl.clone(), &mac.name)),
                Rc::new(SExp::Cons(
                    mac.loc.clone(),
                    mac.args.clone(),
                    Rc::new(SExp::Cons(
                        mac.loc.clone(),
                        mac.program.exp.to_sexp(),
                        Rc::new(SExp::Nil(mac.loc.clone())),
                    )),
                )),
            )),
        ))
    } else {
        Rc::new(SExp::Cons(
            mac.loc.clone(),
            Rc::new(SExp::atom_from_string(mac.loc.clone(), "defmacro")),
            Rc::new(SExp::Cons(
                mac.loc.clone(),
                Rc::new(SExp::atom_from_vec(mac.nl.clone(), &mac.name)),
                mac.program.to_sexp(),
            )),
        ))
    }
}

impl HelperForm {
    /// Get a reference to the HelperForm's name.
    pub fn name(&self) -> &Vec<u8> {
        match self {
            HelperForm::Deftype(deft) => &deft.name,
            HelperForm::Defnamespace(defn) => &defn.rendered_name,
            HelperForm::Defnsref(defr) => &defr.rendered_name,
            HelperForm::Defconstant(defc) => &defc.name,
            HelperForm::Defmacro(mac) => &mac.name,
            HelperForm::Defun(_, defun) => &defun.name,
        }
    }

    /// Get the location of the HelperForm's name.
    pub fn name_loc(&self) -> &Srcloc {
        match self {
            HelperForm::Deftype(deft) => &deft.nl,
            HelperForm::Defnamespace(defn) => &defn.nl,
            HelperForm::Defnsref(defr) => &defr.nl,
            HelperForm::Defconstant(defc) => &defc.nl,
            HelperForm::Defmacro(mac) => &mac.nl,
            HelperForm::Defun(_, defun) => &defun.nl,
        }
    }

    /// Return a general location for the whole HelperForm.
    pub fn loc(&self) -> Srcloc {
        match self {
            HelperForm::Deftype(deft) => deft.loc.clone(),
            HelperForm::Defnamespace(defn) => defn.loc.clone(),
            HelperForm::Defnsref(defr) => defr.loc.clone(),
            HelperForm::Defconstant(defc) => defc.loc.clone(),
            HelperForm::Defmacro(mac) => mac.loc.clone(),
            HelperForm::Defun(_, defun) => defun.loc.clone(),
        }
    }

    /// Convert the HelperForm to an SExp.  These render into a form that can
    /// be re-parsed if needed.
    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            HelperForm::Deftype(deft) => {
                let mut result_vec = vec![
                    Rc::new(SExp::atom_from_string(deft.loc.clone(), "deftype")),
                    Rc::new(SExp::Atom(deft.loc.clone(), deft.name.clone())),
                ];

                for a in deft.args.iter() {
                    result_vec.push(Rc::new(a.to_sexp()));
                }

                if let Some(ty) = &deft.ty {
                    result_vec.push(Rc::new(ty.to_sexp()));
                }

                Rc::new(list_to_cons(deft.loc.clone(), &result_vec))
            }
            HelperForm::Defnamespace(defn) => {
                let mut result_vec = vec![
                    Rc::new(SExp::atom_from_string(defn.kw.clone(), "namespace")),
                    Rc::new(SExp::Atom(defn.nl.clone(), defn.rendered_name.clone())),
                ];
                let helpers_vec: Vec<Rc<SExp>> = defn.helpers.iter().map(|h| h.to_sexp()).collect();
                result_vec.extend(helpers_vec);
                Rc::new(list_to_cons(defn.loc.clone(), &result_vec))
            }
            HelperForm::Defnsref(defr) => {
                let tail = match &defr.specification {
                    ModuleImportSpec::Qualified(_q) => defr.specification.to_sexp(),
                    _ => Rc::new(SExp::Cons(
                        defr.loc.clone(),
                        Rc::new(SExp::Atom(defr.nl.clone(), defr.rendered_name.clone())),
                        defr.specification.to_sexp(),
                    )),
                };
                Rc::new(SExp::Cons(
                    defr.loc.clone(),
                    Rc::new(SExp::Atom(defr.loc.clone(), b"import".to_vec())),
                    tail,
                ))
            }
            HelperForm::Defconstant(defc) => {
                let dc_kw = match defc.kind {
                    ConstantKind::Simple => "defconstant",
                    _ => "defconst",
                };

                Rc::new(list_to_cons(
                    defc.loc.clone(),
                    &[
                        Rc::new(SExp::atom_from_string(defc.loc.clone(), dc_kw)),
                        Rc::new(SExp::atom_from_vec(defc.loc.clone(), &defc.name)),
                        defc.body.to_sexp(),
                    ],
                ))
            }
            HelperForm::Defmacro(mac) => generate_defmacro_sexp(mac),
            HelperForm::Defun(inline, defun) => {
                let di_string = "defun-inline".to_string();
                let d_string = "defun".to_string();
                Rc::new(list_to_cons(
                    defun.loc.clone(),
                    &[
                        Rc::new(SExp::atom_from_string(
                            defun.loc.clone(),
                            if *inline { &di_string } else { &d_string },
                        )),
                        Rc::new(SExp::atom_from_vec(defun.nl.clone(), &defun.name)),
                        defun.args.clone(),
                        defun.body.to_sexp(),
                    ],
                ))
            }
        }
    }
}

fn compose_lambda_serialized_form(ldata: &LambdaData) -> Rc<SExp> {
    let lambda_kw = Rc::new(SExp::Atom(ldata.loc.clone(), b"lambda".to_vec()));
    let amp_kw = Rc::new(SExp::Atom(ldata.loc.clone(), b"&".to_vec()));
    let arguments = if truthy(ldata.capture_args.clone()) {
        Rc::new(SExp::Cons(
            ldata.loc.clone(),
            Rc::new(SExp::Cons(
                ldata.loc.clone(),
                amp_kw,
                ldata.capture_args.clone(),
            )),
            ldata.args.clone(),
        ))
    } else {
        ldata.args.clone()
    };
    let rest_of_body = Rc::new(SExp::Cons(
        ldata.loc.clone(),
        ldata.body.to_sexp(),
        Rc::new(SExp::Nil(ldata.loc.clone())),
    ));

    Rc::new(SExp::Cons(
        ldata.loc.clone(),
        lambda_kw,
        Rc::new(SExp::Cons(ldata.loc.clone(), arguments, rest_of_body)),
    ))
}

fn compose_let(marker: &[u8], letdata: &LetData) -> Rc<SExp> {
    let translated_bindings: Vec<Rc<SExp>> = letdata.bindings.iter().map(|x| x.to_sexp()).collect();
    let bindings_cons = list_to_cons(letdata.loc.clone(), &translated_bindings);
    let translated_body = letdata.body.to_sexp();
    let kw_loc = letdata.kw.clone().unwrap_or_else(|| letdata.loc.clone());
    Rc::new(SExp::Cons(
        letdata.loc.clone(),
        Rc::new(SExp::Atom(kw_loc, marker.to_vec())),
        Rc::new(SExp::Cons(
            letdata.loc.clone(),
            Rc::new(bindings_cons),
            Rc::new(SExp::Cons(
                letdata.loc.clone(),
                translated_body,
                Rc::new(SExp::Nil(letdata.loc.clone())),
            )),
        )),
    ))
}

fn compose_assign(letdata: &LetData) -> Rc<SExp> {
    let mut result = Vec::new();
    let kw_loc = letdata.kw.clone().unwrap_or_else(|| letdata.loc.clone());
    result.push(Rc::new(SExp::Atom(kw_loc, b"assign".to_vec())));
    for b in letdata.bindings.iter() {
        // Binding pattern
        match &b.pattern {
            BindingPattern::Name(v) => {
                result.push(Rc::new(SExp::Atom(b.nl.clone(), v.to_vec())));
            }
            BindingPattern::Complex(c) => {
                result.push(c.clone());
            }
        }

        // Binding body.
        result.push(b.body.to_sexp());
    }

    result.push(letdata.body.to_sexp());
    Rc::new(enlist(letdata.loc.clone(), &result))
}

fn get_let_marker_text(kind: &LetFormKind, letdata: &LetData) -> Vec<u8> {
    match (kind, letdata.inline_hint.as_ref()) {
        (LetFormKind::Sequential, _) => b"let*".to_vec(),
        (LetFormKind::Parallel, _) => b"let".to_vec(),
        (LetFormKind::Assign, Some(LetFormInlineHint::Inline(_))) => b"assign-inline".to_vec(),
        (LetFormKind::Assign, Some(LetFormInlineHint::NonInline(_))) => b"assign-lambda".to_vec(),
        (LetFormKind::Assign, _) => b"assign".to_vec(),
    }
}

impl BodyForm {
    /// Get the general location of the BodyForm.
    pub fn loc(&self) -> Srcloc {
        match self {
            BodyForm::Let(_, letdata) => letdata.loc.clone(),
            BodyForm::Quoted(a) => a.loc(),
            BodyForm::Call(loc, _, _) => loc.clone(),
            BodyForm::Value(a) => a.loc(),
            BodyForm::Mod(kl, program) => kl.ext(&program.loc),
            BodyForm::Lambda(ldata) => ldata.loc.ext(&ldata.body.loc()),
        }
    }

    /// Convert the expression to its SExp form.  These should be reparsable but
    /// may change when desugaring requires it if re-serialization is needed
    /// afterward.
    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            BodyForm::Let(LetFormKind::Assign, letdata) => compose_assign(letdata),
            BodyForm::Let(kind, letdata) => {
                let marker = get_let_marker_text(kind, letdata);
                compose_let(&marker, letdata)
            }
            BodyForm::Quoted(body) => Rc::new(SExp::Cons(
                body.loc(),
                Rc::new(SExp::atom_from_string(body.loc(), "q")),
                Rc::new(body.clone()),
            )),
            BodyForm::Value(body) => Rc::new(body.clone()),
            BodyForm::Call(loc, exprs, tail) => {
                let mut converted: Vec<Rc<SExp>> = exprs.iter().map(|x| x.to_sexp()).collect();
                if let Some(t) = tail.as_ref() {
                    converted.push(Rc::new(SExp::Atom(t.loc(), "&rest".as_bytes().to_vec())));
                    converted.push(t.to_sexp());
                }
                Rc::new(list_to_cons(loc.clone(), &converted))
            }
            BodyForm::Mod(loc, program) => Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc.clone(), b"mod".to_vec())),
                program.to_sexp(),
            )),
            BodyForm::Lambda(ldata) => compose_lambda_serialized_form(ldata),
        }
    }
}

// Note: in cfg(test), this will not be part of the finished binary.
// Also: not a test in itself, just named test so for at least some readers,
// its association with test infrastructure will be apparent.
#[cfg(test)]
fn test_parse_bodyform_to_frontend(bf: &str) {
    let name = "*test*";
    let loc = Srcloc::start(name);
    let opts = Rc::new(DefaultCompilerOpts::new(name));
    let parsed = parse_sexp(loc, bf.bytes()).expect("should parse");
    let bodyform = compile_bodyform(opts, parsed[0].clone()).expect("should compile");
    assert_eq!(bodyform.to_sexp(), parsed[0]);
}

// Inline unit tests for sexp serialization.
#[test]
fn test_mod_serialize_regular_mod() {
    test_parse_bodyform_to_frontend("(mod (X) (+ X 1))");
}

#[test]
fn test_mod_serialize_simple_lambda() {
    test_parse_bodyform_to_frontend("(lambda (X) (+ X 1))");
}

impl Binding {
    /// Express the binding as it would be used in a let form.
    pub fn to_sexp(&self) -> Rc<SExp> {
        let pat = match &self.pattern {
            BindingPattern::Name(name) => Rc::new(SExp::atom_from_vec(self.loc.clone(), name)),
            BindingPattern::Complex(sexp) => sexp.clone(),
        };
        Rc::new(SExp::Cons(
            self.loc.clone(),
            pat,
            Rc::new(SExp::Cons(
                self.loc.clone(),
                self.body.to_sexp(),
                Rc::new(SExp::Nil(self.loc.clone())),
            )),
        ))
    }

    /// Get the general location of the binding.
    pub fn loc(&self) -> Srcloc {
        self.loc.clone()
    }
}

impl CompiledCode {
    /// Get the general location the code was compiled from.
    pub fn loc(&self) -> Srcloc {
        self.0.clone()
    }
}

impl PrimaryCodegen {
    pub fn add_constant(&self, name: &[u8], value: Rc<SExp>) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.constants.insert(name.to_owned(), value);
        codegen_copy
    }

    pub fn add_tabled_constant(&self, name: &[u8], value: Rc<SExp>) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.tabled_constants.insert(name.to_owned(), value);
        codegen_copy
    }

    pub fn add_module_constant(&self, name: &[u8], value: Rc<BodyForm>) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy
            .tabled_constants
            .insert(name.to_owned(), Rc::new(SExp::Nil(value.loc())));
        codegen_copy.module_constants.insert(name.to_owned(), value);
        codegen_copy
    }

    pub fn add_macro(&self, name: &[u8], value: Rc<SExp>) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.macros.insert(name.to_owned(), value);
        codegen_copy
    }

    pub fn add_inline(&self, name: &[u8], value: &InlineFunction) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.inlines.insert(name.to_owned(), value.clone());
        codegen_copy
    }

    pub fn add_defun(&self, name: &[u8], args: Rc<SExp>, value: DefunCall, left_env: bool) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.defuns.insert(name.to_owned(), value.clone());
        let hash = sha256tree(value.code);
        let hash_str = Bytes::new(Some(BytesFromType::Raw(hash))).hex();
        let name = Bytes::new(Some(BytesFromType::Raw(name.to_owned()))).decode();
        codegen_copy.function_symbols.insert(hash_str.clone(), name);
        if left_env {
            codegen_copy
                .function_symbols
                .insert(format!("{hash_str}_left_env"), "1".to_string());
        }
        codegen_copy
            .function_symbols
            .insert(format!("{hash_str}_arguments"), args.to_string());
        codegen_copy
    }

    pub fn set_env(&self, env: Rc<SExp>) -> Self {
        let mut codegen_copy = self.clone();
        codegen_copy.env = env;
        codegen_copy
    }
}

pub fn with_heading(l: Srcloc, name: &str, body: Rc<SExp>) -> SExp {
    SExp::Cons(l.clone(), Rc::new(SExp::atom_from_string(l, name)), body)
}

#[derive(Debug, Clone, Serialize)]
pub struct CompileModuleComponent {
    pub shortname: Vec<u8>,
    pub filename: String,
    pub content: Rc<SExp>,
    pub hash: Vec<u8>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CompileModuleOutput {
    pub summary: Rc<SExp>,
    pub components: Vec<CompileModuleComponent>,
}

#[derive(Debug, Clone, Serialize)]
pub enum CompilerOutput {
    Program(SExp),
    Module(CompileModuleOutput),
}

impl CompilerOutput {
    pub fn to_sexp(&self) -> SExp {
        match self {
            CompilerOutput::Program(x) => x.clone(),
            CompilerOutput::Module(x) => {
                let borrowed: &SExp = x.summary.borrow();
                borrowed.clone()
            }
        }
    }

    pub fn loc(&self) -> Srcloc {
        match self {
            CompilerOutput::Program(x) => x.loc(),
            CompilerOutput::Module(x) => x.summary.loc(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum Export {
    MainProgram(Rc<SExp>, Rc<BodyForm>),
    Function(Vec<u8>, Option<Vec<u8>>),
}

#[derive(Debug, Clone, Serialize)]
pub enum FrontendOutput {
    CompileForm(CompileForm),
    Module(CompileForm, Vec<Export>),
}

impl FrontendOutput {
    pub fn compileform(&self) -> &CompileForm {
        match self {
            FrontendOutput::CompileForm(cf) => cf,
            FrontendOutput::Module(cf, _) => cf,
        }
    }
}

pub fn cons_of_string_map<X>(
    l: Srcloc,
    cvt_body: &dyn Fn(&X) -> Rc<SExp>,
    map: &HashMap<Vec<u8>, X>,
) -> SExp {
    // Thanks: https://users.rust-lang.org/t/sort-hashmap-data-by-keys/37095/3
    let mut v: Vec<_> = map.iter().collect();
    v.sort_by(|x, y| x.0.cmp(y.0));

    let sorted_converted: Vec<Rc<SExp>> = v
        .iter()
        .map(|x| {
            Rc::new(SExp::Cons(
                l.clone(),
                Rc::new(SExp::QuotedString(l.clone(), b'\"', x.0.to_vec())),
                Rc::new(SExp::Cons(
                    l.clone(),
                    cvt_body(x.1),
                    Rc::new(SExp::Nil(l.clone())),
                )),
            ))
        })
        .collect();

    list_to_cons(l, &sorted_converted)
}

pub fn map_m<T, U, E, F>(mut f: F, list: &[T]) -> Result<Vec<U>, E>
where
    F: FnMut(&T) -> Result<U, E>,
{
    let mut result = Vec::new();
    for e in list {
        let val = f(e)?;
        result.push(val);
    }
    Ok(result)
}

pub fn map_m_reverse<T, U, E, F>(mut f: F, list: &[T]) -> Result<Vec<U>, E>
where
    F: FnMut(&T) -> Result<U, E>,
{
    let mut result = Vec::new();
    for e in list {
        let val = f(e)?;
        result.push(val);
    }
    Ok(result.into_iter().rev().collect())
}

pub fn fold_m<R, T, E>(f: &dyn Fn(&R, &T) -> Result<R, E>, start: R, list: &[T]) -> Result<R, E> {
    let mut res: R = start;
    for elt in list.iter() {
        res = f(&res, elt)?;
    }
    Ok(res)
}

pub fn join_vecs_to_string(sep: Vec<u8>, vecs: &[Vec<u8>]) -> String {
    let mut s = Vec::new();
    let mut comma = Vec::new();

    for elt in vecs {
        s.append(&mut comma.clone());
        s.append(&mut elt.to_vec());
        if comma.is_empty() {
            comma = sep.clone();
        }
    }

    decode_string(&s)
}
