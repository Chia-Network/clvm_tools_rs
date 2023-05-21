use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use serde::Serialize;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::sha256tree;
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;

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

/// A binding from a (let ...) form.  Specifies the name of the bound variable
/// the location of the whole binding form, the location of the name atom (nl)
/// and the body as a BodyForm (which are chialisp expressions).
#[derive(Clone, Debug, Serialize)]
pub struct Binding {
    /// Overall location of the form.
    pub loc: Srcloc,
    /// Location of the name atom specifically.
    pub nl: Srcloc,
    /// The name.
    pub name: Vec<u8>,
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
}

/// Information about a let form.  Encapsulates everything except whether it's
/// parallel or sequential, which is left in the BodyForm itself.
#[derive(Clone, Debug, Serialize)]
pub struct LetData {
    /// The location of the form overall.
    pub loc: Srcloc,
    /// The location specifically of the let or let* keyword.
    pub kw: Option<Srcloc>,
    /// The bindings introduced.
    pub bindings: Vec<Rc<Binding>>,
    /// The expression evaluated in the context of all the bindings.
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug, Serialize)]
pub enum BodyForm {
    /// A let or let* form (depending on LetFormKind).
    Let(LetFormKind, LetData),
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
    Call(Srcloc, Vec<Rc<BodyForm>>),
    /// (mod ...) can be used in chialisp as an expression, in which it returns
    /// the compiled code.  Here, it contains a CompileForm, which represents
    /// the full significant input of a program (yielded by frontend()).
    Mod(Srcloc, CompileForm),
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
}

/// Specifies where a constant is the classic kind (unevaluated) or a proper
/// expression.
#[derive(Clone, Debug, Serialize)]
pub enum ConstantKind {
    Complex,
    Simple,
}

/// HelperForm is a toplevel binding of some kind.
/// Helpers are the (defconst ...) (defun ...) (defun-inline ...) (defmacro ...)
/// forms from the source code and "help" the program do its job.  They're
/// individually parsable and represent the atomic units of the program.
#[derive(Clone, Debug, Serialize)]
pub enum HelperForm {
    /// A constant definition (see DefconstData).
    Defconstant(DefconstData),
    /// A macro definition (see DefmacData).
    Defmacro(DefmacData),
    /// A function definition (see DefunData).
    Defun(bool, DefunData),
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
}

impl IncludeDesc {
    pub fn to_sexp(&self) -> Rc<SExp> {
        Rc::new(SExp::Cons(
            self.kw.clone(),
            Rc::new(SExp::Atom(self.kw.clone(), b"include".to_vec())),
            Rc::new(SExp::QuotedString(self.nl.clone(), b'"', self.name.clone())),
        ))
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
    pub macros: HashMap<Vec<u8>, Rc<SExp>>,
    pub inlines: HashMap<Vec<u8>, InlineFunction>,
    pub defuns: HashMap<Vec<u8>, DefunCall>,
    pub parentfns: HashSet<Vec<u8>>,
    pub env: Rc<SExp>,
    pub to_process: Vec<HelperForm>,
    pub original_helpers: Vec<HelperForm>,
    pub final_expr: Rc<BodyForm>,
    pub final_code: Option<CompiledCode>,
    pub function_symbols: HashMap<String, String>,
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

    /// Set search paths.
    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts>;
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

    /// Using the search paths list we have, try to read a file by name,
    /// Returning the expanded path to the file and its content.
    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, String), CompileErr>;

    /// Given a parsed SExp, compile it as an independent program based on the
    /// settings given here.  The result is bare generated code.
    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr>;
}

/// Frontend uses this to accumulate frontend forms, used internally.
#[derive(Debug)]
pub struct ModAccum {
    pub loc: Srcloc,
    pub includes: Vec<IncludeDesc>,
    pub helpers: Vec<HelperForm>,
    pub exp_form: Option<CompileForm>,
}

impl ModAccum {
    pub fn set_final(&self, c: &CompileForm) -> Self {
        ModAccum {
            loc: self.loc.clone(),
            includes: self.includes.clone(),
            helpers: self.helpers.clone(),
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
            exp_form: self.exp_form.clone(),
        }
    }

    pub fn new(loc: Srcloc) -> ModAccum {
        ModAccum {
            loc,
            includes: Vec::new(),
            helpers: Vec::new(),
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
        }
    }
}

impl HelperForm {
    /// Get a reference to the HelperForm's name.
    pub fn name(&self) -> &Vec<u8> {
        match self {
            HelperForm::Defconstant(defc) => &defc.name,
            HelperForm::Defmacro(mac) => &mac.name,
            HelperForm::Defun(_, defun) => &defun.name,
        }
    }

    /// Get the location of the HelperForm's name.
    pub fn name_loc(&self) -> &Srcloc {
        match self {
            HelperForm::Defconstant(defc) => &defc.nl,
            HelperForm::Defmacro(mac) => &mac.nl,
            HelperForm::Defun(_, defun) => &defun.nl,
        }
    }

    /// Return a general location for the whole HelperForm.
    pub fn loc(&self) -> Srcloc {
        match self {
            HelperForm::Defconstant(defc) => defc.loc.clone(),
            HelperForm::Defmacro(mac) => mac.loc.clone(),
            HelperForm::Defun(_, defun) => defun.loc.clone(),
        }
    }

    /// Convert the HelperForm to an SExp.  These render into a form that can
    /// be re-parsed if needed.
    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            HelperForm::Defconstant(defc) => match defc.kind {
                ConstantKind::Simple => Rc::new(list_to_cons(
                    defc.loc.clone(),
                    &[
                        Rc::new(SExp::atom_from_string(defc.loc.clone(), "defconstant")),
                        Rc::new(SExp::atom_from_vec(defc.loc.clone(), &defc.name)),
                        defc.body.to_sexp(),
                    ],
                )),
                ConstantKind::Complex => Rc::new(list_to_cons(
                    defc.loc.clone(),
                    &[
                        Rc::new(SExp::atom_from_string(defc.loc.clone(), "defconst")),
                        Rc::new(SExp::atom_from_vec(defc.loc.clone(), &defc.name)),
                        defc.body.to_sexp(),
                    ],
                )),
            },
            HelperForm::Defmacro(mac) => Rc::new(SExp::Cons(
                mac.loc.clone(),
                Rc::new(SExp::atom_from_string(mac.loc.clone(), "defmacro")),
                Rc::new(SExp::Cons(
                    mac.loc.clone(),
                    Rc::new(SExp::atom_from_vec(mac.nl.clone(), &mac.name)),
                    mac.program.to_sexp(),
                )),
            )),
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

impl BodyForm {
    /// Get the general location of the BodyForm.
    pub fn loc(&self) -> Srcloc {
        match self {
            BodyForm::Let(_, letdata) => letdata.loc.clone(),
            BodyForm::Quoted(a) => a.loc(),
            BodyForm::Call(loc, _) => loc.clone(),
            BodyForm::Value(a) => a.loc(),
            BodyForm::Mod(kl, program) => kl.ext(&program.loc),
        }
    }

    /// Convert the expression to its SExp form.  These should be reparsable but
    /// may change when desugaring requires it if re-serialization is needed
    /// afterward.
    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            BodyForm::Let(kind, letdata) => {
                let translated_bindings: Vec<Rc<SExp>> =
                    letdata.bindings.iter().map(|x| x.to_sexp()).collect();
                let bindings_cons = list_to_cons(letdata.loc.clone(), &translated_bindings);
                let translated_body = letdata.body.to_sexp();
                let marker = match kind {
                    LetFormKind::Parallel => "let",
                    LetFormKind::Sequential => "let*",
                };
                let kw_loc = letdata.kw.clone().unwrap_or_else(|| letdata.loc.clone());
                Rc::new(SExp::Cons(
                    letdata.loc.clone(),
                    Rc::new(SExp::atom_from_string(kw_loc, marker)),
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
            BodyForm::Quoted(body) => Rc::new(SExp::Cons(
                body.loc(),
                Rc::new(SExp::atom_from_string(body.loc(), "q")),
                Rc::new(body.clone()),
            )),
            BodyForm::Value(body) => Rc::new(body.clone()),
            BodyForm::Call(loc, exprs) => {
                let converted: Vec<Rc<SExp>> = exprs.iter().map(|x| x.to_sexp()).collect();
                Rc::new(list_to_cons(loc.clone(), &converted))
            }
            BodyForm::Mod(loc, program) => Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc.clone(), b"mod".to_vec())),
                program.to_sexp(),
            )),
        }
    }
}

impl Binding {
    /// Express the binding as it would be used in a let form.
    pub fn to_sexp(&self) -> Rc<SExp> {
        Rc::new(SExp::Cons(
            self.loc.clone(),
            Rc::new(SExp::atom_from_vec(self.loc.clone(), &self.name)),
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

pub fn map_m<T, U, E>(f: &dyn Fn(&T) -> Result<U, E>, list: &[T]) -> Result<Vec<U>, E> {
    let mut result = Vec::new();
    for e in list {
        let val = f(e)?;
        result.push(val);
    }
    Ok(result)
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
