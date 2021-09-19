use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler::sexp;
use crate::compiler::sexp::{
    SExp
};

use crate::compiler::srcloc;
use crate::compiler::srcloc::{
    Srcloc
};

pub struct CompileErr(Srcloc, String);
pub struct CompiledCode(Srcloc, Rc<SExp>);

pub enum Callable {
    CallMacro(Rc<SExp>),
    CallDefun(Rc<SExp>),
    CallPrim(Rc<SExp>)
}

fn list_to_cons(l: Srcloc, list: &Vec<Rc<SExp>>) -> SExp {
    if list.len() == 0 {
        return SExp::Nil(l.clone());
    }

    let mut result = SExp::Nil(l.clone());
    for i_reverse in 0..list.len() {
        let i = list.len() - i_reverse - 1;
        result = SExp::Cons(list[i].loc(), list[i].clone(), Rc::new(result));
    }

    return result;
}

pub struct Binding {
    loc: Srcloc,
    name: String,
    body: Rc<BodyForm>
}

pub enum BodyForm {
    Let(Srcloc, Vec<Rc<Binding>>, Rc<BodyForm>),
    Quoted(Rc<SExp>),
    Value(Rc<SExp>),
    Call(Srcloc, Vec<Rc<BodyForm>>)
}

pub enum HelperForm {
    Defconstant(Srcloc, String, Rc<BodyForm>),
    Defmacro(Srcloc, String, Rc<CompileForm>),
    Defun(Srcloc, String, bool, Rc<SExp>, Rc<BodyForm>)
}

pub struct CompileForm {
    loc: Srcloc,
    args: Rc<SExp>,
    helpers: Vec<Rc<HelperForm>>,
    exp: Rc<SExp>
}

#[derive(Clone)]
pub struct DefunCall {
    pub required_env: Rc<SExp>,
    pub code: Rc<SExp>
}

pub struct PrimaryCodegen {
    pub prims: HashMap<Vec<u8>, Rc<SExp>>,
    pub constants: HashMap<Vec<u8>, Rc<SExp>>,
    pub macros: HashMap<Vec<u8>, Rc<SExp>>,
    pub defuns: HashMap<Vec<u8>, Rc<SExp>>,
    pub parentfns: HashMap<Vec<u8>, Rc<SExp>>,
    pub env: Rc<SExp>,
    pub to_process: Rc<HelperForm>,
    pub final_expr: Rc<BodyForm>,
    pub final_code: Option<CompiledCode>
}

pub struct DefaultCompilerOpts {
    pub include_dirs: Vec<String>,
    pub filename: String,
    pub compiler: Option<Rc<PrimaryCodegen>>,
    pub in_defun: bool,
    pub assemble: bool,
    pub stdenv: bool,
    pub start_env: Option<Rc<SExp>>
}

trait CompilerOpts {
    fn filename(&self) -> String;
    fn compiler(&self) -> Option<Rc<PrimaryCodegen>>;
    fn in_defun(&self) -> bool;
    fn assemble(&self) -> bool;
    fn stdenv(&self) -> bool;
    fn start_env(&self) -> Option<Rc<SExp>>;

    fn set_in_defun(self, new_in_defun: bool) -> Self;
    fn set_compiler(self, new_compiler: Rc<PrimaryCodegen>) -> Self;

    fn read_new_file(&mut self, inc_from: String, filename: String) -> Result<(String,String), CompileErr>;
    fn compile_program(&mut self, sexp: Rc<SExp>) -> Result<SExp, CompileErr>;
}

/* Frontend uses this to accumulate frontend forms */
// type ('arg, 'body) modAccumulator
//     = ModAccum of
//     (Srcloc.t * (('arg, 'body) helperForm list -> ('arg, 'body) helperForm list))
//     | ModFinal of (('arg, 'body) compileForm)

impl CompileForm {
    pub fn loc(&self) -> Srcloc {
        return self.loc.clone();
    }

    pub fn to_sexp(&self) -> Rc<SExp> {
        let mut sexp_forms: Vec<Rc<SExp>> =
            self.helpers.iter().map(|x| x.to_sexp()).collect();
        sexp_forms.push(self.exp.clone());

        Rc::new(SExp::Cons(
            self.loc.clone(),
            self.args.clone(),
            Rc::new(list_to_cons(self.loc.clone(), &sexp_forms))
        ))
    }
}

impl HelperForm {
    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            HelperForm::Defconstant(loc,name,body) => {
                Rc::new(list_to_cons(
                    loc.clone(),
                    &vec!(
                        Rc::new(SExp::atom_from_string(loc.clone(), &"defconstant".to_string())),
                        Rc::new(SExp::atom_from_string(loc.clone(), &name.to_string())),
                        body.to_sexp(),
                    )
                ))
            },
            HelperForm::Defmacro(loc,name,body) => {
                Rc::new(list_to_cons(
                    loc.clone(),
                    &vec!(
                        Rc::new(SExp::atom_from_string(loc.clone(), &"defmacro".to_string())),
                        Rc::new(SExp::atom_from_string(loc.clone(), &name.to_string())),
                        body.to_sexp()
                    )
                ))
            },
            HelperForm::Defun(loc,name,inline,arg,body) => {
                let di_string = "defun-inline".to_string();
                let d_string = "defun".to_string();
                Rc::new(list_to_cons(
                    loc.clone(),
                    &vec!(
                        Rc::new(SExp::atom_from_string(
                            loc.clone(),
                            if *inline {
                                &di_string
                            } else {
                                &d_string
                            }
                        )),
                        Rc::new(SExp::atom_from_string(loc.clone(), &name.to_string())),
                        arg.clone(),
                        body.to_sexp()
                    )
                ))
            }
        }
    }
}

impl BodyForm {
    pub fn loc(&self) -> Srcloc {
        match self {
            BodyForm::Let(loc,_,_) => loc.clone(),
            BodyForm::Quoted(a) => a.loc(),
            BodyForm::Call(loc,_) => loc.clone(),
            BodyForm::Value(a) => a.loc()
        }
    }

    pub fn to_sexp(&self) -> Rc<SExp> {
        match self {
            BodyForm::Let(loc,bindings,body) => {
                let translated_bindings: Vec<Rc<SExp>> = bindings.iter().map(|x| x.to_sexp()).collect();
                let bindings_cons = list_to_cons(loc.clone(), &translated_bindings);
                let translated_body = body.to_sexp();
                Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &"let".to_string())),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(bindings_cons),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            translated_body,
                            Rc::new(SExp::Nil(loc.clone()))
                        ))
                    ))
                ))
            },
            BodyForm::Quoted(body) => {
                Rc::new(SExp::Cons(
                    body.loc(),
                    Rc::new(SExp::atom_from_string(body.loc(), &"q".to_string())),
                    body.clone()
                ))
            },
            BodyForm::Value(body) => body.clone(),
            BodyForm::Call(loc,exprs) => {
                let converted: Vec<Rc<SExp>> = exprs.iter().map(|x| x.to_sexp()).collect();
                Rc::new(list_to_cons(loc.clone(), &converted))
            }
        }
    }
}

impl Binding {
    pub fn to_sexp(&self) -> Rc<SExp> {
        Rc::new(SExp::Cons(
            self.loc.clone(),
            Rc::new(SExp::atom_from_string(self.loc.clone(), &self.name)),
            Rc::new(SExp::Cons(
                self.loc.clone(),
                self.body.to_sexp(),
                Rc::new(SExp::Nil(self.loc.clone()))
            ))
        ))
    }

    pub fn loc(&self) -> Srcloc {
        self.loc.clone()
    }
}

impl CompiledCode {
    pub fn loc(&self) -> Srcloc {
        return self.0.clone();
    }
}

fn with_heading(l: Srcloc, name: &String, body: Rc<SExp>) -> SExp {
    SExp::Cons(
        l.clone(),
        Rc::new(SExp::atom_from_string(l.clone(), &name.to_string())),
        body.clone()
    )
}

fn cons_of_string_map<X>(
    l: Srcloc,
    cvt_body: &dyn Fn(&X) -> Rc<SExp>,
    map: &HashMap<Vec<u8>, X>
) -> SExp {
    // Thanks: https://users.rust-lang.org/t/sort-hashmap-data-by-keys/37095/3
    let mut v: Vec<_> = map.into_iter().collect();
    v.sort_by(|x,y| x.0.cmp(&y.0));

    let sorted_converted: Vec<Rc<SExp>> = v.iter().map(|x| {
        Rc::new(SExp::Cons(
            l.clone(),
            Rc::new(SExp::QuotedString(l.clone(), '\"' as u8, x.0.to_vec())),
            Rc::new(SExp::Cons(
                l.clone(),
                cvt_body(x.1.clone()),
                Rc::new(SExp::Nil(l.clone()))
            ))
        ))
    }).collect();

    list_to_cons(l.clone(), &sorted_converted)
}
