use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use clvm_rs::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;

use crate::compiler::clvm::sha256tree;
use crate::compiler::sexp::{decode_string, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Clone, Debug)]
pub struct CompileErr(pub Srcloc, pub String);

#[derive(Clone, Debug)]
pub struct CompiledCode(pub Srcloc, pub Rc<SExp>);

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

pub enum Callable {
    CallMacro(Srcloc, SExp),
    CallDefun(Srcloc, SExp),
    CallInline(Srcloc, InlineFunction),
    CallPrim(Srcloc, SExp),
    RunCompiler,
    EnvPath,
}

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

#[derive(Clone, Debug)]
pub struct Binding {
    pub loc: Srcloc,
    pub nl: Srcloc,
    pub name: Vec<u8>,
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LetFormKind {
    Parallel,
    Sequential,
}

#[derive(Clone, Debug)]
pub struct LetData {
    pub loc: Srcloc,
    pub kw: Option<Srcloc>,
    pub bindings: Vec<Rc<Binding>>,
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug)]
pub enum BodyForm {
    Let(LetFormKind, LetData),
    Quoted(SExp),
    Value(SExp),
    Call(Srcloc, Vec<Rc<BodyForm>>),
    Mod(Srcloc, CompileForm),
}

#[derive(Clone, Debug)]
pub struct DefunData {
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub kw: Option<Srcloc>,
    pub nl: Srcloc,
    pub orig_args: Rc<SExp>,
    pub args: Rc<SExp>,
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug)]
pub struct DefmacData {
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub kw: Option<Srcloc>,
    pub nl: Srcloc,
    pub args: Rc<SExp>,
    pub program: Rc<CompileForm>,
}

#[derive(Clone, Debug)]
pub struct DefconstData {
    pub loc: Srcloc,
    pub name: Vec<u8>,
    pub kw: Option<Srcloc>,
    pub nl: Srcloc,
    pub body: Rc<BodyForm>,
}

#[derive(Clone, Debug)]
pub enum HelperForm {
    Defconstant(DefconstData),
    Defmacro(DefmacData),
    Defun(bool, DefunData),
}

// A description of an include form.
#[derive(Clone, Debug)]
pub struct IncludeDesc {
    pub kw: Srcloc,
    pub nl: Srcloc,
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

#[derive(Clone, Debug)]
pub struct CompileForm {
    pub loc: Srcloc,
    pub include_forms: Vec<IncludeDesc>,
    pub args: Rc<SExp>,
    pub helpers: Vec<HelperForm>,
    pub exp: Rc<BodyForm>,
}

#[derive(Clone, Debug)]
pub struct DefunCall {
    pub required_env: Rc<SExp>,
    pub code: Rc<SExp>,
}

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
    pub orig_help: Vec<HelperForm>,
    pub final_expr: Rc<BodyForm>,
    pub final_code: Option<CompiledCode>,
    pub function_symbols: HashMap<String, String>,
}

pub trait CompilerOpts {
    fn filename(&self) -> String;
    fn compiler(&self) -> Option<PrimaryCodegen>;
    fn in_defun(&self) -> bool;
    fn stdenv(&self) -> bool;
    fn optimize(&self) -> bool;
    fn frontend_opt(&self) -> bool;
    fn frontend_check_live(&self) -> bool;
    fn start_env(&self) -> Option<Rc<SExp>>;
    fn prim_map(&self) -> Rc<HashMap<Vec<u8>, Rc<SExp>>>;

    fn set_search_paths(&self, dirs: &[String]) -> Rc<dyn CompilerOpts>;
    fn set_in_defun(&self, new_in_defun: bool) -> Rc<dyn CompilerOpts>;
    fn set_stdenv(&self, new_stdenv: bool) -> Rc<dyn CompilerOpts>;
    fn set_optimize(&self, opt: bool) -> Rc<dyn CompilerOpts>;
    fn set_frontend_opt(&self, opt: bool) -> Rc<dyn CompilerOpts>;
    fn set_frontend_check_live(&self, check: bool) -> Rc<dyn CompilerOpts>;
    fn set_compiler(&self, new_compiler: PrimaryCodegen) -> Rc<dyn CompilerOpts>;
    fn set_start_env(&self, start_env: Option<Rc<SExp>>) -> Rc<dyn CompilerOpts>;

    fn read_new_file(
        &self,
        inc_from: String,
        filename: String,
    ) -> Result<(String, String), CompileErr>;
    fn compile_program(
        &self,
        allocator: &mut Allocator,
        runner: Rc<dyn TRunProgram>,
        sexp: Rc<SExp>,
        symbol_table: &mut HashMap<String, String>,
    ) -> Result<SExp, CompileErr>;
}

/* Frontend uses this to accumulate frontend forms */
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
    pub fn loc(&self) -> Srcloc {
        self.loc.clone()
    }

    pub fn to_sexp(&self) -> Rc<SExp> {
        let mut sexp_forms: Vec<Rc<SExp>> = self.helpers.iter().map(|x| x.to_sexp()).collect();
        sexp_forms.push(self.exp.to_sexp());

        Rc::new(SExp::Cons(
            self.loc.clone(),
            self.args.clone(),
            Rc::new(list_to_cons(self.loc.clone(), &sexp_forms)),
        ))
    }

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
    pub fn name(&self) -> &Vec<u8> {
        match self {
            HelperForm::Defconstant(defc) => &defc.name,
            HelperForm::Defmacro(mac) => &mac.name,
            HelperForm::Defun(_, defun) => &defun.name,
        }
    }

    pub fn name_loc(&self) -> &Srcloc {
        match self {
            HelperForm::Defconstant(defc) => &defc.nl,
            HelperForm::Defmacro(mac) => &mac.nl,
            HelperForm::Defun(_, defun) => &defun.nl,
        }
    }

    pub fn loc(&self) -> Srcloc {
        match self {
            HelperForm::Defconstant(defc) => defc.loc.clone(),
            HelperForm::Defmacro(mac) => mac.loc.clone(),
            HelperForm::Defun(_, defun) => defun.loc.clone(),
        }
    }

    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            HelperForm::Defconstant(defc) => Rc::new(list_to_cons(
                defc.loc.clone(),
                &[
                    Rc::new(SExp::atom_from_string(defc.loc.clone(), "defconstant")),
                    Rc::new(SExp::atom_from_vec(defc.loc.clone(), &defc.name)),
                    defc.body.to_sexp(),
                ],
            )),
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
    pub fn loc(&self) -> Srcloc {
        match self {
            BodyForm::Let(_, letdata) => letdata.loc.clone(),
            BodyForm::Quoted(a) => a.loc(),
            BodyForm::Call(loc, _) => loc.clone(),
            BodyForm::Value(a) => a.loc(),
            BodyForm::Mod(kl, program) => kl.ext(&program.loc),
        }
    }

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

    pub fn loc(&self) -> Srcloc {
        self.loc.clone()
    }
}

impl CompiledCode {
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
                .insert(format!("{}_left_env", hash_str), "1".to_string());
        }
        codegen_copy
            .function_symbols
            .insert(format!("{}_arguments", hash_str), args.to_string());
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
