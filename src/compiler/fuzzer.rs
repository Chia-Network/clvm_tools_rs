use num_bigint::{BigInt, ToBigInt};

use rand::distributions::Standard;
use rand::prelude::*;
use rand::Rng;
use std::borrow::Borrow;
use std::cmp::max;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::clvm::truthy;
use crate::compiler::codegen::create_name_lookup_;
use crate::compiler::comptypes::{
    Binding, BodyForm, CompileForm, DefconstData, DefmacData, DefunData, HelperForm, LetData,
    LetFormKind,
};
use crate::compiler::sexp::{enlist, SExp};

use crate::compiler::sexp::{random_atom_name, random_sexp};

use crate::classic::clvm::__type_compatibility__::{sha256, Bytes, BytesFromType, Stream};
use crate::classic::clvm::casts::bigint_to_bytes_clvm;
use crate::compiler::runtypes::RunFailure;
use crate::compiler::srcloc::Srcloc;

use crate::util::Number;

const MIN_ARGLIST: usize = 3;
const MAX_STEPS: usize = 1000;
pub const MAX_LIST_BOUND: usize = 3;
const CURRENT_DIALECT: u32 = 21;
const BINDING_NAME_MIN: usize = 3;
const MAX_FORMS_CPS: usize = 512;
const MAX_HELPER_KIND_CPS: u16 = 3;

#[derive(Debug, Clone)]
pub struct FuzzBinding {
    pub name: Vec<u8>,
    pub expr: FuzzOperation,
}

/*
 * Bitstream randomness ->
 *
 * Our goal is to devise a format where adding one to the stream yields a
 * usefully different program.
 *
 * That means that at the left end of the we want more consequential information
 * followed by less and less consequential information.
 *
 * The last bits should be constants, next to last select among alternative
 * objects of the same time first the program structure, then more details.
 *
 * It'd be nice to have the stream start with the number of objects of each
 * type but that'd make simple increments make big changes.  I think it's better
 * to have each new object be introduced via an increment on the right most byte.
 *
 * So we read the data as messages, where we accept a message if its priority is
 * the current or lower priority, and end if it's higher.
 *
 * So we must read a set of messages:
 *
 * Structures (helper) -> Structure (body) -> Arguments -> Selectors -> Constants
 * Where Structures contains
 * (Constant | Function | Macro | Main)
 * (quote | arg | if | mult  | sub | sha256 | let | call)
 * Arguments -> (cons | @ form | atom | nil)
 * Selectors -> choose nth
 * Constants -> (cons | hex+ | int | nil)
 *
 * Each 16 bits is a message.
 *
 * The low 3 bits of each word defines the message type, with types 6 and 7
 * currently ignored.
 * For each, the other 13 bits are taken as the payload.
 */

#[derive(Clone, Debug, Default)]
pub struct CollectProgramStructure {
    helper_structures: Vec<u16>,
    body_forms: Vec<u16>,
    arguments: Vec<u16>,
    selectors: Vec<u16>,
    constants: Vec<u16>,
    choice: usize,
    main: u16,
}

fn arg_identifiers(in_scope: &mut Vec<Vec<u8>>, args: Rc<SExp>) {
    match args.borrow() {
        SExp::Cons(_, a, b) => {
            arg_identifiers(in_scope, a.clone());
            arg_identifiers(in_scope, b.clone());
        }
        SExp::Atom(_, n) => {
            if n != b"@" {
                in_scope.push(n.clone());
            }
        }
        _ => {}
    }
}

fn rewrite_identifiers_bodyform(in_scope: &Vec<Vec<u8>>, body_form: &BodyForm) -> BodyForm {
    match body_form {
        BodyForm::Let(LetFormKind::Sequential, data) => {
            let mut new_bindings = Vec::new();
            let mut newly_bound = in_scope.clone();
            for b in data.bindings.iter() {
                let new_binding_body = rewrite_identifiers_bodyform(&newly_bound, b.body.borrow());
                newly_bound.push(b.name.clone());
                let new_binding_data_borrowed: &Binding = b.borrow();
                let mut new_binding_data_cloned = new_binding_data_borrowed.clone();
                new_binding_data_cloned.body = Rc::new(new_binding_body);
                new_bindings.push(Rc::new(new_binding_data_cloned));
            }
            let mut new_data = data.clone();
            new_data.bindings = new_bindings;

            let new_body = rewrite_identifiers_bodyform(&newly_bound, data.body.borrow());
            new_data.body = Rc::new(new_body);

            BodyForm::Let(LetFormKind::Sequential, new_data)
        }
        BodyForm::Let(LetFormKind::Parallel, data) => {
            let new_bindings: Vec<Rc<Binding>> = data
                .bindings
                .iter()
                .map(|b| {
                    let b_borrowed: &Binding = b.borrow();
                    let mut b_clone = b_borrowed.clone();
                    b_clone.body = Rc::new(rewrite_identifiers_bodyform(in_scope, b.body.borrow()));
                    Rc::new(b_clone)
                })
                .collect();
            let mut new_scope = in_scope.clone();
            for b in new_bindings.iter() {
                new_scope.push(b.name.clone());
            }
            let mut new_data = data.clone();
            new_data.bindings = new_bindings;
            new_data.body = Rc::new(rewrite_identifiers_bodyform(&new_scope, data.body.borrow()));
            BodyForm::Let(LetFormKind::Parallel, new_data)
        }
        BodyForm::Value(SExp::Atom(l, n)) => {
            if !in_scope.contains(&n) {
                let idnum = n[0] as usize;
                if in_scope.is_empty() {
                    BodyForm::Quoted(SExp::Nil(l.clone()))
                } else {
                    let selection = in_scope[idnum % in_scope.len()].clone();
                    BodyForm::Value(SExp::Atom(l.clone(), selection))
                }
            } else {
                BodyForm::Value(SExp::Atom(l.clone(), n.clone()))
            }
        }
        BodyForm::Call(l, args) => {
            let new_args = args
                .iter()
                .enumerate()
                .map(|(i, a)| {
                    if i == 0 {
                        a.clone()
                    } else {
                        Rc::new(rewrite_identifiers_bodyform(in_scope, a.borrow()))
                    }
                })
                .collect();
            BodyForm::Call(l.clone(), new_args)
        }
        _ => body_form.clone(),
    }
}

// Rewrite identifiers to match those in scope for the helper and the
// let forms.
fn rewrite_identifiers(args: Rc<SExp>, body: &BodyForm) -> BodyForm {
    let mut in_scope = Vec::new();
    arg_identifiers(&mut in_scope, args.clone());
    rewrite_identifiers_bodyform(&in_scope, body)
}

impl CollectProgramStructure {
    fn choose_with_default<T>(&self, lst: &[T], choice: u16, default: T) -> T
    where
        T: Clone,
    {
        if lst.is_empty() {
            return default;
        }

        lst[(choice as usize) % lst.len()].clone()
    }

    fn get_choice(&mut self) -> u16 {
        if self.selectors.is_empty() {
            0
        } else {
            let res = self.selectors[self.choice % self.selectors.len()];
            self.choice += 1;
            res
        }
    }

    fn new_constant(&mut self, c: u16, constants: &[Rc<SExp>]) -> Rc<SExp> {
        let loc = Srcloc::start("*rng*");
        let nil = Rc::new(SExp::Nil(loc.clone()));
        match c & 3 {
            0..1 => {
                let raw_number = c & 0x3fff;
                let bigint = (raw_number - 0x2000).to_bigint().unwrap();
                Rc::new(SExp::Integer(loc.clone(), bigint))
            }
            2 => {
                // Hex+
                // If the last item is also a number, this number concatenates
                // them.
                let new_byte = ((c >> 2) & 0xff) as u8;
                if !constants.is_empty() {
                    if let SExp::Atom(l, n) = constants[constants.len() - 1].borrow() {
                        let mut new_atom_content = n.to_vec();
                        new_atom_content.push(new_byte);
                        return Rc::new(SExp::Atom(l.clone(), new_atom_content));
                    }
                }
                Rc::new(SExp::Atom(loc.clone(), vec![new_byte]))
            }
            _ => {
                // Cons.
                let choice_of_a = c >> 2;
                let choice_of_b: u16 = self.get_choice();
                let a = self.choose_with_default(&constants, choice_of_a, nil.clone());
                let b = self.choose_with_default(&constants, choice_of_b, nil.clone());
                Rc::new(SExp::Cons(loc.clone(), a, b))
            }
        }
    }

    fn new_argument(
        &mut self,
        arg: u16,
        atom_identifiers: &[Vec<u8>],
        arguments: &[Rc<SExp>],
    ) -> Rc<SExp> {
        let loc = Srcloc::start("*rng*");
        let nil = Rc::new(SExp::Nil(loc.clone()));
        match arg & 1 {
            0 => {
                // Use 1 selector, this number is for the @ binding.
                let letters = arg >> 2;
                let ident = atom_identifiers[letters as usize % atom_identifiers.len()].clone();
                let choice: u16 = self.get_choice();
                let bind_also = self.choose_with_default(&arguments, choice, nil.clone());
                Rc::new(SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), "@")),
                    Rc::new(SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::Atom(loc.clone(), ident)),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            bind_also,
                            Rc::new(SExp::Nil(loc.clone())),
                        )),
                    )),
                ))
            }
            _ => {
                let choice_of_a = arg >> 2;
                let choice_of_b: u16 = self.get_choice();
                let a = self.choose_with_default(&arguments, choice_of_a, nil.clone());
                let b = self.choose_with_default(&arguments, choice_of_b, nil.clone());
                Rc::new(SExp::Cons(loc.clone(), a, b))
            }
        }
    }

    fn isolate_arg_sites(&self, arg_sites: &mut Vec<Rc<SExp>>, args: Rc<SExp>) {
        if let SExp::Cons(_, f, r) = args.borrow() {
            arg_sites.push(f.clone());
            self.isolate_arg_sites(arg_sites, r.clone());
        } else {
            arg_sites.push(args.clone());
        }
    }

    fn new_bodyform(
        &mut self,
        b: u16,
        atom_identifiers: &[Vec<u8>],
        constants: &[Rc<SExp>],
        arguments: &[Rc<SExp>],
        body_forms: &[Rc<BodyForm>],
    ) -> Rc<BodyForm> {
        let loc = Srcloc::start("*rng*");
        let nil = Rc::new(SExp::Nil(loc.clone()));
        let body_nil = Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone())));
        // (quote | arg | if | mult  | sub | sha256 | let | call)
        match b & 15 {
            0 => {
                let choice_of_const = b >> 4;
                let constant = self.choose_with_default(&constants, choice_of_const, nil.clone());
                let constant_borrowed: &SExp = constant.borrow();
                Rc::new(BodyForm::Quoted(constant_borrowed.clone()))
            }
            1..6 => {
                let choice_of_arg = b >> 3;
                let arg = self.choose_with_default(&atom_identifiers, choice_of_arg, vec![b'X']);
                Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), arg)))
            }
            7 => {
                let choice_of_cond = b >> 3;
                let choice_of_then: u16 = self.get_choice();
                let choice_of_else: u16 = self.get_choice();
                let use_cond =
                    self.choose_with_default(&body_forms, choice_of_cond, body_nil.clone());
                let use_then =
                    self.choose_with_default(&body_forms, choice_of_then, body_nil.clone());
                let use_else =
                    self.choose_with_default(&body_forms, choice_of_else, body_nil.clone());
                Rc::new(BodyForm::Call(
                    loc.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), "if"))),
                        use_cond,
                        use_then,
                        use_else,
                    ],
                ))
            }
            8 => {
                let choice_of_a = b >> 3;
                let choice_of_b: u16 = self.get_choice();
                let use_a = self.choose_with_default(&body_forms, choice_of_a, body_nil.clone());
                let use_b = self.choose_with_default(&body_forms, choice_of_b, body_nil.clone());
                Rc::new(BodyForm::Call(
                    loc.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), vec![18]))),
                        use_a,
                        use_b,
                    ],
                ))
            }
            9 => {
                let choice_of_a = b >> 3;
                let choice_of_b: u16 = self.get_choice();
                let use_a = self.choose_with_default(&body_forms, choice_of_a, body_nil.clone());
                let use_b = self.choose_with_default(&body_forms, choice_of_b, body_nil.clone());
                Rc::new(BodyForm::Call(
                    loc.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), vec![17]))),
                        use_a,
                        use_b,
                    ],
                ))
            }
            10 => {
                let choice_of_a = b >> 3;
                let choice_of_b: u16 = self.get_choice();
                let use_a = self.choose_with_default(&body_forms, choice_of_a, body_nil.clone());
                let use_b = self.choose_with_default(&body_forms, choice_of_b, body_nil.clone());
                Rc::new(BodyForm::Call(
                    loc.clone(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), vec![11]))),
                        use_a,
                        use_b,
                    ],
                ))
            }
            11 => {
                // Synthesize a let form.
                let num_bindings = (b >> 3) & 3;
                let kind = if (b >> 5) != 0 {
                    LetFormKind::Parallel
                } else {
                    LetFormKind::Sequential
                };
                let mut collected_names = Vec::new();
                let mut collected_bindings = Vec::new();
                for _ in 0..=num_bindings {
                    let choice_of_name: u16 = self.get_choice();
                    let choice_of_body = b >> 6;
                    let arg_atom =
                        atom_identifiers[choice_of_name as usize % atom_identifiers.len()].clone();
                    if collected_names.contains(&arg_atom) {
                        break;
                    }

                    let body =
                        self.choose_with_default(&body_forms, choice_of_body, body_nil.clone());

                    collected_names.push(arg_atom.clone());
                    collected_bindings.push(Rc::new(Binding {
                        loc: loc.clone(),
                        nl: loc.clone(),
                        name: arg_atom,
                        body: body,
                    }));
                }

                let body = self.choose_with_default(&body_forms, b >> 5, body_nil.clone());

                Rc::new(BodyForm::Let(
                    kind,
                    LetData {
                        loc: loc.clone(),
                        kw: None,
                        bindings: collected_bindings,
                        body: body,
                    },
                ))
            }
            _ => {
                // Call
                if self.helper_structures.is_empty() {
                    return body_nil.clone();
                }

                let choice_of_helper = (b >> 3) as usize % self.helper_structures.len();
                let helper_spec = self.helper_structures
                    [choice_of_helper as usize % self.helper_structures.len()];
                let choice_of_arg = helper_spec >> 3;
                let call_args = self.choose_with_default(&arguments, choice_of_arg, nil.clone());
                let mut arg_sites = Vec::new();
                self.isolate_arg_sites(&mut arg_sites, call_args);
                let helper_name = format!("helper_{}", choice_of_helper);
                if helper_spec & 3 == 0 {
                    // Reference constant
                    return Rc::new(BodyForm::Value(SExp::atom_from_string(
                        loc.clone(),
                        &helper_name,
                    )));
                }

                // Reference callable
                let mut call_args: Vec<Rc<BodyForm>> = arg_sites
                    .iter()
                    .map(|_| {
                        let choice_of_expr: u16 = self.get_choice();
                        self.choose_with_default(&body_forms, choice_of_expr, body_nil.clone())
                    })
                    .collect();
                call_args.insert(
                    0,
                    Rc::new(BodyForm::Value(SExp::atom_from_string(
                        loc.clone(),
                        &helper_name,
                    ))),
                );
                Rc::new(BodyForm::Call(loc.clone(), call_args))
            }
        }
    }

    fn new_helper(
        &mut self,
        i: usize,
        h: u16,
        arguments: &[Rc<SExp>],
        body_forms: &[Rc<BodyForm>],
        helper_forms: &[HelperForm],
    ) -> HelperForm {
        let loc = Srcloc::start("*rng*");
        let nil = Rc::new(SExp::Nil(loc.clone()));
        let body_nil = Rc::new(BodyForm::Quoted(SExp::Nil(loc.clone())));

        let is_inline = ((h >> 2) & 1) == 1;
        let choice_of_args = h >> 3;
        let choice_of_body: u16 = self.get_choice();
        let arguments = self.choose_with_default(&arguments, choice_of_args, nil.clone());
        let body = Rc::new(rewrite_identifiers(
            arguments.clone(),
            self.choose_with_default(&body_forms, choice_of_body, body_nil.clone())
                .borrow(),
        ));
        let helper_name = format!("helper_{}", i).as_bytes().to_vec();
        match h & 3 {
            0 => HelperForm::Defconstant(DefconstData {
                loc: loc.clone(),
                name: helper_name,
                kw: None,
                nl: loc.clone(),
                body: body,
            }),
            1 => HelperForm::Defun(
                is_inline,
                DefunData {
                    loc: loc.clone(),
                    name: helper_name,
                    kw: None,
                    nl: loc.clone(),
                    args: arguments,
                    body,
                },
            ),
            _ => {
                let program = CompileForm {
                    loc: loc.clone(),
                    include_forms: Vec::new(),
                    args: arguments.clone(),
                    helpers: helper_forms.to_vec(),
                    exp: body,
                };
                HelperForm::Defmacro(DefmacData {
                    loc: loc.clone(),
                    name: helper_name,
                    kw: None,
                    nl: loc.clone(),
                    args: arguments,
                    program: Rc::new(program),
                })
            }
        }
    }

    pub fn to_program(&mut self) -> CompileForm {
        // Build constants...
        let loc = Srcloc::start("*rng*");
        let nil = Rc::new(SExp::Nil(loc.clone()));

        let mut constants = vec![nil.clone(), Rc::new(SExp::Integer(loc.clone(), bi_one()))];
        let constant_vals = self.constants.clone();
        for c in constant_vals.iter() {
            let new_const = self.new_constant(*c, &constants);
            constants.push(new_const);
        }

        let mut atom_identifiers = vec![
            b"A".to_vec(),
            b"B".to_vec(),
            b"C".to_vec(),
            b"D".to_vec(),
            b"E".to_vec(),
        ];
        let mut arguments: Vec<Rc<SExp>> = atom_identifiers
            .iter()
            .map(|n| Rc::new(SExp::Atom(loc.clone(), n.clone())))
            .collect();

        let argument_vals = self.arguments.clone();
        for arg in argument_vals.iter() {
            let new_arg = self.new_argument(*arg, &atom_identifiers, &arguments);
            if let SExp::Atom(_, n) = new_arg.borrow() {
                atom_identifiers.push(n.clone());
            }
            arguments.push(new_arg);
        }

        let mut body_forms = Vec::new();

        let body_vals = self.body_forms.clone();
        for b in body_vals.iter() {
            let new_form =
                self.new_bodyform(*b, &atom_identifiers, &constants, &arguments, &body_forms);
            body_forms.push(new_form);
        }

        let mut helper_forms = Vec::new();
        let helper_vals = self.helper_structures.clone();
        for (i, h) in helper_vals.iter().enumerate() {
            let new_helper = self.new_helper(i, *h, &arguments, &body_forms, &helper_forms);
            helper_forms.push(new_helper);
        }

        let body = self.new_bodyform(
            self.main,
            &atom_identifiers,
            &constants,
            &arguments,
            &body_forms,
        );

        let use_arguments: u16 = self.get_choice();
        let arguments = self.choose_with_default(&arguments, use_arguments, nil.clone());

        CompileForm {
            loc: loc.clone(),
            include_forms: Vec::new(),
            args: arguments.clone(),
            helpers: helper_forms,
            exp: Rc::new(rewrite_identifiers(arguments, body.borrow())),
        }
    }
}

impl Distribution<CollectProgramStructure> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> CollectProgramStructure {
        let mut iters = 0;
        let mut cps: CollectProgramStructure = Default::default();
        let mut have_body = false;
        loop {
            let input_32: u32 = rng.gen();

            // Stop if zero.
            if input_32 == 0 {
                break;
            }

            iters += 1;
            if iters > MAX_FORMS_CPS {
                break;
            }

            let inputs = &[(input_32 >> 16) as u16, (input_32 & 0xffff) as u16];
            for input in inputs.iter() {
                let input_type = input & 15;
                let input_val = input >> 4;

                // A new message type advances out of the prev phase.
                match input_type {
                    0 => {
                        let new_helper_kind = input_val & 3;
                        if new_helper_kind > MAX_HELPER_KIND_CPS {
                            cps.selectors.push(input_val);
                            continue;
                        }

                        if new_helper_kind == 0 {
                            have_body = true;
                            cps.main = input_val;
                            continue;
                        }

                        cps.helper_structures.push(input_val);
                    }
                    1..7 => cps.body_forms.push(input_val),
                    8..10 => cps.arguments.push(input_val),
                    11 => cps.constants.push(input_val),
                    _ => cps.selectors.push(input_val),
                }
            }
        }

        if !have_body {
            // Populate with call to 0th function.
            cps.main = 7;
        }

        cps
    }
}

// We don't actually need all operators here, just a good selection with
// semantics that are distinguishable.
#[derive(Debug, Clone)]
pub enum FuzzOperation {
    Argref(usize),
    Quote(SExp),
    If(Rc<FuzzOperation>, Rc<FuzzOperation>, Rc<FuzzOperation>),
    Multiply(Rc<FuzzOperation>, Rc<FuzzOperation>),
    Sub(Rc<FuzzOperation>, Rc<FuzzOperation>),
    Sha256(Vec<FuzzOperation>),
    Let(Vec<FuzzBinding>, Rc<FuzzOperation>),
    Call(u8, Vec<FuzzOperation>),
}

#[derive(Debug, Clone)]
pub enum ArgListType {
    ProperList(u8),
    Structure(SExp),
}

#[derive(Debug, Clone)]
pub struct FuzzFunction {
    pub inline: bool,
    pub number: u8,
    pub args: ArgListType,
    pub body: FuzzOperation,
}

#[derive(Debug, Clone)]
pub struct FuzzProgram {
    pub args: ArgListType,
    pub functions: Vec<FuzzFunction>,
    pub body: FuzzOperation,
}

#[derive(Debug, Clone)]
pub struct FuzzOldProgram {
    pub program: FuzzProgram,
}

fn atom_list(sexp: &SExp) -> Vec<Vec<u8>> {
    match sexp {
        SExp::Nil(_) => vec![],
        SExp::Atom(_, v) => {
            if v.is_empty() {
                vec![]
            } else {
                vec![v.clone()]
            }
        }
        SExp::QuotedString(_, _, _) => vec![],
        SExp::Integer(_, _) => vec![],
        SExp::Cons(_, a, b) => {
            let mut a_vec = atom_list(a.borrow());
            let b_vec = atom_list(b.borrow());
            for b_item in b_vec.iter() {
                a_vec.push(b_item.clone());
            }
            a_vec
        }
    }
}

fn select_argument(
    num: usize,
    fun: &FuzzProgram,
    bindings: &[Vec<FuzzBinding>],
) -> (SExp, Option<FuzzOperation>) {
    let args_sexp = fun.args.to_sexp();
    let select_group = (num >> 8) % (bindings.len() + 1);
    if select_group == bindings.len() {
        // Select from arguments
        let arg_list = atom_list(&args_sexp);
        let nil = SExp::Nil(args_sexp.loc());
        if arg_list.is_empty() {
            (nil.clone(), Some(FuzzOperation::Quote(nil)))
        } else {
            let selected_arg = arg_list[num & 0xff % arg_list.len()].clone();
            (SExp::Atom(args_sexp.loc(), selected_arg), None)
        }
    } else {
        // Select a binding group using the second byte,
        let group = &bindings[select_group];
        let select_binding = (num & 0xff) % group.len();
        let selected_binding = &group[select_binding];
        // Select a binding using the first byte.
        (
            SExp::Atom(args_sexp.loc(), selected_binding.name.clone()),
            Some(selected_binding.expr.clone()),
        )
    }
}

fn select_call(num: u8, prog: &FuzzProgram) -> (String, FuzzFunction) {
    if prog.functions.len() == 0 {
        panic!("we make programs with at least one function");
    }
    let selected_num = num % prog.functions.len() as u8;
    let selected = &prog.functions[selected_num as usize];
    (format!("fun_{}", selected_num), selected.clone())
}

fn make_operator(op: String, args: Vec<SExp>) -> SExp {
    let loc = Srcloc::start(&"*rng*".to_string());
    let mut result = SExp::Nil(loc.clone());

    for i_reverse in 0..args.len() {
        let i = args.len() - i_reverse - 1;
        result = SExp::Cons(loc.clone(), Rc::new(args[i].clone()), Rc::new(result));
    }

    SExp::Cons(
        loc.clone(),
        Rc::new(SExp::atom_from_string(loc.clone(), &op)),
        Rc::new(result),
    )
}

fn distribute_args(
    a: ArgListType,
    fun: &FuzzProgram,
    bindings: &[Vec<FuzzBinding>],
    arginputs: &Vec<SExp>,
    spine: bool,
    argn: u8,
) -> (u8, SExp) {
    let loc = Srcloc::start(&"*rng*".to_string());
    match a {
        ArgListType::ProperList(0) => (argn, SExp::Nil(loc.clone())),
        ArgListType::ProperList(n) => {
            let rest_result = distribute_args(
                ArgListType::ProperList(n - 1),
                fun,
                bindings,
                arginputs,
                spine,
                argn + 1,
            );
            (
                rest_result.0,
                SExp::Cons(
                    loc.clone(),
                    Rc::new(arginputs[argn as usize].clone()),
                    Rc::new(rest_result.1),
                ),
            )
        }
        ArgListType::Structure(SExp::Nil(l)) => (argn, SExp::Nil(l.clone())),
        ArgListType::Structure(SExp::Cons(l, a, b)) => {
            let a_borrow: &SExp = a.borrow();
            let b_borrow: &SExp = b.borrow();
            let first_res = distribute_args(
                ArgListType::Structure(a_borrow.clone()),
                fun,
                bindings,
                arginputs,
                false,
                argn,
            );
            let rest_res = distribute_args(
                ArgListType::Structure(b_borrow.clone()),
                fun,
                bindings,
                arginputs,
                spine,
                argn + first_res.0,
            );
            let res = if spine {
                SExp::Cons(l.clone(), Rc::new(first_res.1), Rc::new(rest_res.1))
            } else {
                make_operator("c".to_string(), vec![first_res.1, rest_res.1])
            };
            (rest_res.0, res)
        }
        ArgListType::Structure(_) => {
            if spine {
                distribute_args(
                    ArgListType::ProperList(1),
                    fun,
                    bindings,
                    arginputs,
                    spine,
                    argn,
                )
            } else {
                (argn + 1_u8, arginputs[argn as usize].clone())
            }
        }
    }
}

fn random_args<R: Rng + ?Sized>(rng: &mut R, loc: Srcloc, a: ArgListType) -> SExp {
    match a {
        ArgListType::ProperList(0) => SExp::Nil(loc.clone()),
        ArgListType::ProperList(n) => {
            let loc = Srcloc::start("*rng*");
            enlist(loc, (0..n).map(|_| Rc::new(rng.gen())).collect())
        }
        ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
        ArgListType::Structure(SExp::Cons(_, a, b)) => {
            let borrowed_a: &SExp = a.borrow();
            let borrowed_b: &SExp = b.borrow();
            SExp::Cons(
                loc.clone(),
                Rc::new(random_args(
                    rng,
                    loc.clone(),
                    ArgListType::Structure(borrowed_a.clone()),
                )),
                Rc::new(random_args(
                    rng,
                    loc.clone(),
                    ArgListType::Structure(borrowed_b.clone()),
                )),
            )
        }
        ArgListType::Structure(_) => {
            let random_64: u64 = rng.gen();
            SExp::Integer(loc.clone(), random_64.to_bigint().unwrap())
        }
    }
}

impl FuzzOperation {
    pub fn to_sexp(&self, fun: &FuzzProgram, bindings: &[Vec<FuzzBinding>]) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            FuzzOperation::Argref(argument_num) => {
                let argument = select_argument(*argument_num as usize, fun, &bindings);
                argument.0
            }
            FuzzOperation::Quote(s) => SExp::Cons(
                loc.clone(),
                Rc::new(SExp::atom_from_string(loc.clone(), &"q".to_string())),
                Rc::new(s.clone()),
            ),
            FuzzOperation::If(cond, ct, cf) => make_operator(
                "if".to_string(),
                vec![
                    cond.to_sexp(fun, bindings),
                    ct.to_sexp(fun, bindings),
                    cf.to_sexp(fun, bindings),
                ],
            ),
            FuzzOperation::Multiply(a, b) => make_operator(
                "*".to_string(),
                vec![a.to_sexp(fun, bindings), b.to_sexp(fun, bindings)],
            ),
            FuzzOperation::Sub(a, b) => make_operator(
                "-".to_string(),
                vec![a.to_sexp(fun, bindings), b.to_sexp(fun, bindings)],
            ),
            FuzzOperation::Sha256(ents) => make_operator(
                "sha256".to_string(),
                ents.iter().map(|x| x.to_sexp(fun, bindings)).collect(),
            ),
            FuzzOperation::Let(our_bindings, body) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let mut bindings_done = SExp::Nil(loc.clone());

                for b in our_bindings.iter().rev() {
                    bindings_done = SExp::Cons(
                        loc.clone(),
                        Rc::new(SExp::Cons(
                            loc.clone(),
                            Rc::new(SExp::Atom(loc.clone(), b.name.clone())),
                            Rc::new(SExp::Cons(
                                loc.clone(),
                                Rc::new(b.expr.to_sexp(fun, bindings)),
                                Rc::new(SExp::Nil(loc.clone())),
                            )),
                        )),
                        Rc::new(bindings_done),
                    );
                }

                let mut inner_bindings = bindings.to_vec();
                inner_bindings.push(our_bindings.clone());

                make_operator(
                    "let".to_string(),
                    vec![bindings_done, body.to_sexp(fun, &inner_bindings)],
                )
            }
            FuzzOperation::Call(selection, args) => {
                let loc = Srcloc::start(&"*rng*".to_string());
                let called_fun = select_call(*selection, fun);
                let mut reified_args = Vec::new();
                for a in args.iter() {
                    reified_args.push(a.to_sexp(fun, bindings));
                }
                let args = distribute_args(
                    called_fun.1.args.clone(),
                    fun,
                    bindings,
                    &reified_args,
                    true,
                    0,
                );
                SExp::Cons(
                    loc.clone(),
                    Rc::new(SExp::atom_from_string(loc.clone(), &called_fun.0)),
                    Rc::new(args.1),
                )
            }
        }
    }
}

fn make_random_call<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzOperation {
    FuzzOperation::Call(
        rng.gen(),
        (0..=255)
            .map(|_| random_operation(rng, dialect, remaining - 1))
            .collect(),
    )
}

// FuzzOperation is potentially infinite so we'll limit the depth to something
// sensible.
fn random_operation<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzOperation {
    if remaining < 2 {
        FuzzOperation::Quote(random_sexp(rng, remaining))
    } else {
        let op_bound = if dialect >= 21 { 7 } else { 6 };
        let alternative: usize = rng.gen_range(0..=op_bound);
        match alternative {
            0 => FuzzOperation::Argref(rng.gen()),
            1 => FuzzOperation::If(
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            2 => FuzzOperation::Multiply(
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            3 => FuzzOperation::Sub(
                Rc::new(random_operation(rng, dialect, remaining - 1)),
                Rc::new(random_operation(rng, dialect, remaining - 1)),
            ),
            4 => {
                let bound: usize = rng.gen_range(0..=MAX_LIST_BOUND);
                FuzzOperation::Sha256(
                    (0..=bound)
                        .map(|_| random_operation(rng, dialect, remaining - 1))
                        .collect(),
                )
            }
            5 => make_random_call(rng, dialect, remaining - 1),
            6 => FuzzOperation::Quote(random_sexp(rng, remaining)),
            _ => {
                let bound: usize = rng.gen_range(1..=5);
                let new_bindings: Vec<FuzzBinding> = (1..=bound)
                    .map(|_| FuzzBinding {
                        name: random_atom_name(rng, BINDING_NAME_MIN),
                        expr: random_operation(rng, dialect, remaining - 1),
                    })
                    .collect();
                FuzzOperation::Let(
                    new_bindings,
                    Rc::new(random_operation(rng, dialect, remaining - 1)),
                )
            }
        }
    }
}

impl Distribution<FuzzOperation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOperation {
        random_operation(rng, 22, MAX_LIST_BOUND)
    }
}

fn min_arglist(remaining: usize) -> usize {
    max(remaining, MIN_ARGLIST)
}

fn random_arglist_cons<R: Rng + ?Sized>(rng: &mut R, loc: &Srcloc, remaining: usize) -> SExp {
    if rng.gen() || remaining < 1 {
        SExp::Atom(loc.clone(), random_atom_name(rng, 2))
    } else {
        let left = random_arglist_cons(rng, loc, remaining - 1);
        let right = random_arglist_cons(rng, loc, remaining - 1);
        SExp::Cons(loc.clone(), Rc::new(left), Rc::new(right))
    }
}

fn random_arglist<R: Rng + ?Sized>(rng: &mut R, remaining: usize) -> ArgListType {
    let loc = Srcloc::start("*arglist*");
    let truncated_len = (remaining % 255) as u8;
    if rng.gen() {
        ArgListType::ProperList(rng.gen_range(0..=truncated_len))
    } else {
        let mut structure = SExp::Nil(loc.clone());
        for _ in 0..=min_arglist(truncated_len as usize) {
            structure = SExp::Cons(
                loc.clone(),
                Rc::new(random_arglist_cons(rng, &loc, remaining - 1)),
                Rc::new(structure),
            );
        }

        ArgListType::Structure(structure)
    }
}

impl Distribution<ArgListType> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> ArgListType {
        random_arglist(rng, MAX_LIST_BOUND)
    }
}

impl ArgListType {
    pub fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for _ in 0..*n {
                    let random_bytes: Vec<u8> = (0..=MAX_LIST_BOUND).map(|_| rng.gen()).collect();
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_vec(loc.clone(), &random_bytes)),
                        Rc::new(args.clone()),
                    );
                }
                args
            }
            ArgListType::Structure(SExp::Nil(l)) => SExp::Nil(l.clone()),
            ArgListType::Structure(SExp::Cons(l, a, b)) => {
                let aborrow: &SExp = a.borrow();
                let bborrow: &SExp = b.borrow();
                let aclone = aborrow.clone();
                let bclone = bborrow.clone();
                let arg_a = ArgListType::Structure(aclone).random_args(rng);
                let arg_b = ArgListType::Structure(bclone).random_args(rng);
                SExp::Cons(l.clone(), Rc::new(arg_a), Rc::new(arg_b))
            }
            ArgListType::Structure(_) => rng.gen(),
        }
    }

    fn to_sexp(&self) -> SExp {
        let loc = Srcloc::start(&"*rng*".to_string());
        match self {
            ArgListType::ProperList(n) => {
                let mut args = SExp::Nil(loc.clone());
                for i_reverse in 0..*n {
                    let i = n - i_reverse;
                    args = SExp::Cons(
                        args.loc(),
                        Rc::new(SExp::atom_from_string(loc.clone(), &format!("arg_{}", i))),
                        Rc::new(args.clone()),
                    );
                }
                args
            }
            ArgListType::Structure(s) => s.clone(),
        }
    }
}

fn random_function<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzFunction {
    FuzzFunction {
        inline: rng.gen(),
        number: 0,
        args: random_arglist(rng, remaining - 1),
        body: random_operation(rng, dialect, remaining - 1),
    }
}

impl Distribution<FuzzFunction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzFunction {
        random_function(rng, CURRENT_DIALECT, MAX_LIST_BOUND)
    }
}

impl FuzzFunction {
    fn to_sexp(&self, fun: &FuzzProgram) -> SExp {
        let fuzzloc = Srcloc::start(&"*fuzz*".to_string());
        let initial_atom = if self.inline {
            SExp::atom_from_string(fuzzloc.clone(), &"defun-inline".to_string())
        } else {
            SExp::atom_from_string(fuzzloc.clone(), &"defun".to_string())
        };
        let name_atom = SExp::atom_from_string(fuzzloc.clone(), &format!("fun_{}", self.number));
        let args_sexp = self.args.to_sexp();
        let body_sexp = self.body.to_sexp(&self.to_program(fun), &Vec::new());
        SExp::Cons(
            fuzzloc.clone(),
            Rc::new(initial_atom),
            Rc::new(SExp::Cons(
                fuzzloc.clone(),
                Rc::new(name_atom),
                Rc::new(SExp::Cons(
                    fuzzloc.clone(),
                    Rc::new(args_sexp),
                    Rc::new(SExp::Cons(
                        fuzzloc.clone(),
                        Rc::new(body_sexp),
                        Rc::new(SExp::Nil(fuzzloc.clone())),
                    )),
                )),
            )),
        )
    }

    fn to_program(&self, parent: &FuzzProgram) -> FuzzProgram {
        FuzzProgram {
            args: self.args.clone(),
            functions: parent.functions.clone(),
            body: self.body.clone(),
        }
    }
}

/*
 * Produce chialisp frontend code with an expected result
 */
fn random_program<R: Rng + ?Sized>(rng: &mut R, dialect: u32, remaining: usize) -> FuzzProgram {
    let num_funs = rng.gen_range(1..=MAX_LIST_BOUND);
    let funs: Vec<FuzzFunction> = (1..=num_funs)
        .map(|_| random_function(rng, dialect, remaining - 1))
        .enumerate()
        .map(|(i, f): (usize, FuzzFunction)| {
            let mut fcopy = f.clone();
            fcopy.number = i as u8;
            fcopy
        })
        .collect();
    FuzzProgram {
        args: random_arglist(rng, remaining),
        functions: funs,
        body: random_operation(rng, dialect, remaining),
    }
}

impl Distribution<FuzzProgram> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzProgram {
        random_program(rng, CURRENT_DIALECT, MAX_LIST_BOUND)
    }
}

fn evaluate_to_numbers(
    prog: &FuzzProgram,
    args: &SExp,
    bindings: &[Vec<FuzzBinding>],
    a: &FuzzOperation,
    b: &FuzzOperation,
    steps: usize,
) -> Result<(BigInt, BigInt), RunFailure> {
    let a_val = interpret_program(prog, args, bindings, a, steps - 1)?;
    let b_val = interpret_program(prog, args, bindings, b, steps - 1)?;
    match (&a_val, &b_val) {
        (SExp::Integer(_, a), SExp::Integer(_, b)) => Ok((a.clone(), b.clone())),
        (SExp::Cons(l, _, _), _) => Err(RunFailure::RunErr(
            l.clone(),
            format!("*: expected atom got {}", a_val.to_string()),
        )),
        (_, SExp::Cons(l, _, _)) => Err(RunFailure::RunErr(
            l.clone(),
            format!("*: expected atom got {}", b_val.to_string()),
        )),
        (a, b) => {
            let num_a = a
                .get_number()
                .map_err(|e| RunFailure::RunErr(a.loc(), e.1))?;
            let num_b = b
                .get_number()
                .map_err(|e| RunFailure::RunErr(b.loc(), e.1))?;
            Ok((num_a, num_b))
        }
    }
}

fn byte_vec_of_sexp(val: &SExp) -> Result<Vec<u8>, RunFailure> {
    match val {
        SExp::Nil(_) => Ok(Vec::new()),
        SExp::Atom(_, a) => Ok(a.clone()),
        SExp::QuotedString(_, _, s) => Ok(s.clone()),
        SExp::Integer(_, i) => Ok(bigint_to_bytes_clvm(i).data().clone()),
        _ => Err(RunFailure::RunErr(
            val.loc(),
            format!("attempt to convert {} to bytes", val.to_string()),
        )),
    }
}

fn choose_path(path: Number, args: Rc<SExp>) -> Result<Rc<SExp>, RunFailure> {
    if path == bi_one() {
        Ok(args)
    } else {
        match args.borrow() {
            SExp::Cons(_, a, b) => {
                let odd = bi_one() & path.clone();
                if odd != bi_zero() {
                    choose_path(path >> 1, b.clone())
                } else {
                    choose_path(path >> 1, a.clone())
                }
            }
            _ => Err(RunFailure::RunErr(args.loc(), "path into atom".to_string())),
        }
    }
}

fn interpret_program(
    prog: &FuzzProgram,
    args: &SExp,
    bindings: &[Vec<FuzzBinding>],
    expr: &FuzzOperation,
    steps: usize,
) -> Result<SExp, RunFailure> {
    if steps < 1 {
        return Err(RunFailure::RunErr(
            args.loc(),
            "too many steps taken".to_string(),
        ));
    }
    let loc = Srcloc::start(&"*interp*".to_string());
    match &expr {
        FuzzOperation::Argref(n) => {
            let (argname, run_expression) = select_argument(*n as usize, prog, bindings);
            if let Some(to_run) = run_expression {
                // Run binding code selected.
                interpret_program(prog, args, bindings, &to_run, steps - 1)
            } else {
                // Select argument from env.
                let argpath = create_name_lookup_(
                    args.loc(),
                    &argname.to_string().as_bytes(),
                    Rc::new(prog.args.to_sexp()),
                    Rc::new(prog.args.to_sexp()),
                )
                .map_err(|e| RunFailure::RunErr(e.0.clone(), e.1.clone()))?;
                let argval = choose_path(argpath.to_bigint().unwrap(), Rc::new(args.clone()))?;
                let argval_borrow: &SExp = argval.borrow();
                interpret_program(
                    prog,
                    args,
                    bindings,
                    &FuzzOperation::Quote(argval_borrow.clone()),
                    steps - 1,
                )
            }
        }
        FuzzOperation::Quote(exp) => Ok(exp.clone()),
        FuzzOperation::If(cond, iftrue, iffalse) => {
            let borrowed_cond: &FuzzOperation = cond.borrow();
            interpret_program(prog, args, bindings, borrowed_cond, steps - 1)
                .map(|cond_res| truthy(Rc::new(cond_res)))
                .and_then(|cond_res| {
                    if cond_res {
                        let borrowed_iftrue: &FuzzOperation = iftrue.borrow();
                        interpret_program(prog, args, bindings, borrowed_iftrue, steps - 1)
                    } else {
                        let borrowed_iffalse: &FuzzOperation = iffalse.borrow();
                        interpret_program(prog, args, bindings, borrowed_iffalse, steps - 1)
                    }
                })
        }
        FuzzOperation::Multiply(a, b) => {
            let (a_val, b_val) =
                evaluate_to_numbers(prog, args, bindings, a.borrow(), b.borrow(), steps - 1)?;
            Ok(SExp::Integer(loc, a_val * b_val))
        }
        FuzzOperation::Sub(a, b) => {
            let (a_val, b_val) =
                evaluate_to_numbers(prog, args, bindings, a.borrow(), b.borrow(), steps - 1)?;
            Ok(SExp::Integer(loc, a_val - b_val))
        }
        FuzzOperation::Sha256(lst) => {
            let loc = Srcloc::start(&"*sha256*".to_string());
            let mut bytes_stream = Stream::new(None);
            for elt in lst.iter() {
                let output = interpret_program(prog, args, bindings, &elt, steps - 1)?;
                let output_bytes = byte_vec_of_sexp(&output)?;
                bytes_stream.write(Bytes::new(Some(BytesFromType::Raw(output_bytes))));
            }
            Ok(SExp::Atom(
                loc,
                sha256(bytes_stream.get_value()).data().clone(),
            ))
        }
        FuzzOperation::Let(new_bindings, body) => {
            let mut total_bindings = bindings.to_vec();
            total_bindings.push(new_bindings.clone());
            interpret_program(prog, args, &total_bindings, body.borrow(), steps - 1)
        }
        FuzzOperation::Call(fun, call_args) => {
            let called_fun = select_call(*fun, prog);
            let mut reified_args = Vec::new();

            // Interpret all arguments.
            for a in call_args.iter() {
                reified_args.push(interpret_program(prog, args, bindings, a, steps - 1)?);
            }

            // Use reified arguments since we're assuming they're sexp.
            let distributed_args = distribute_args(
                called_fun.1.args.clone(),
                prog,
                bindings,
                &reified_args,
                true,
                0,
            );
            interpret_program(
                &called_fun.1.to_program(prog),
                &distributed_args.1,
                &Vec::new(),
                &called_fun.1.body.clone(),
                steps - 1,
            )
        }
    }
}

impl FuzzProgram {
    pub fn to_sexp(&self) -> SExp {
        let mut body_vec = Vec::new();
        body_vec.push(self.args.to_sexp());
        for f in &self.functions {
            body_vec.push(f.to_sexp(self))
        }
        body_vec.push(self.body.to_sexp(self, &Vec::new()));
        make_operator("mod".to_string(), body_vec)
    }

    pub fn random_args<R: Rng + ?Sized>(&self, rng: &mut R) -> SExp {
        let srcloc = Srcloc::start(&"*args*".to_string());
        random_args(rng, srcloc, self.args.clone())
    }

    pub fn interpret(&self, args: SExp) -> Result<SExp, RunFailure> {
        interpret_program(self, &args, &Vec::new(), &self.body, MAX_STEPS)
    }
}

fn random_old_program<R: Rng + ?Sized>(rng: &mut R, remaining: usize) -> FuzzOldProgram {
    FuzzOldProgram {
        program: random_program(rng, 0, remaining),
    }
}

impl Distribution<FuzzOldProgram> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FuzzOldProgram {
        random_old_program(rng, MAX_LIST_BOUND)
    }
}
