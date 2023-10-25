use num_bigint::ToBigInt;

use rand::distributions::Standard;
use rand::prelude::*;
use rand::Rng;
use std::borrow::Borrow;
use std::rc::Rc;

use crate::classic::clvm::__type_compatibility__::bi_one;
use crate::compiler::comptypes::{
    Binding, BindingPattern, BodyForm, CompileForm, ConstantKind, DefconstData, DefmacData, DefunData, HelperForm,
    LetData, LetFormKind, SyntheticType,
};
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

pub const MAX_LIST_BOUND: usize = 3;
const MAX_FORMS_CPS: usize = 512;
const MAX_HELPER_KIND_CPS: u16 = 3;

//
// Bitstream based randomness ->
//
// Our goal is to devise a format where adding one to the stream yields a
// usefully different program.
//
// That means that at the left end of the we want more consequential information
// followed by less and less consequential information.
//
// The last bits should be constants, next to last select among alternative
// objects of the same time first the program structure, then more details.
//
// It'd be nice to have the stream start with the number of objects of each
// type but that'd make simple increments make big changes.  I think it's better
// to have each new object be introduced via an increment on the right most byte.
//
// So we must read a set of messages.  Each message is 32 bits as a pair of
// 16 bit values.  If the whole message is 0, then we stop reading.
//
// This is useful for scenarios like fuzzing where a specific, limited pattern
// is provided and we generate only based on that pattern.  The messages are
// ordered lowest to highest in complexity and each message adds one piece of
// information.  Since each type of form is generated separately, a correct
// program can be synthesized from any number (even 0) of accumulated messages.
//
// Each 16 bit value goes into one of 5 bins:
//
// Structures (helper) -> Structure (body) -> Arguments -> Constants -> Choices
//
// The payload of each is used to contain one of the choices needed downstream
// but others are teken from the choices bin, which is treated as a circular list
// of choice values we can use.
//
// Other than the helpers and choices, each of the structure types builds as an
// acyclic graph on its own list, accumulating larger structures as it goes, which
// are available as choices elsewhere.
//
// With constants generated, it generates body forms and with arguments generated
// it generates helpers and the whole program.
//
#[derive(Clone, Debug, Default)]
pub struct CollectProgramStructure {
    // defmacro, defun, defconstant etc
    helper_structures: Vec<u16>,
    // if (- ...) (sha256 ...) (let ...) etc
    body_forms: Vec<u16>,
    // defining the argument shape for functions
    arguments: Vec<u16>,
    // constructs constants.
    constants: Vec<u16>,
    // store of choices for filling out trees
    selectors: Vec<u16>,
    // current selector
    choice: usize,
    // message representing the main expression
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
                if let BindingPattern::Name(n) = &b.pattern {
                    newly_bound.push(n.clone());
                    let new_binding_data_borrowed: &Binding = b.borrow();
                    let mut new_binding_data_cloned = new_binding_data_borrowed.clone();
                    new_binding_data_cloned.body = Rc::new(new_binding_body);
                    new_bindings.push(Rc::new(new_binding_data_cloned));
                } else {
                    todo!();
                }
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
            let mut new_data = data.clone();
            for b in new_bindings.iter() {
                if let BindingPattern::Name(n) = &b.pattern {
                    new_scope.push(n.clone());
                } else {
                    todo!();
                }
            }
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
        BodyForm::Call(l, args, tail) => {
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
            let new_tail = tail
                .as_ref()
                .map(|t| Rc::new(rewrite_identifiers_bodyform(in_scope, t.borrow())));
            BodyForm::Call(l.clone(), new_args, new_tail)
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
        if c < 2 {
            let raw_number = c & 0x3fff;
            let bigint = ((raw_number as i32) - 0x2000).to_bigint().unwrap();
            Rc::new(SExp::Integer(loc.clone(), bigint))
        } else if c == 2 {
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
        } else {
            // Cons.
            let choice_of_a = c >> 2;
            let choice_of_b: u16 = self.get_choice();
            let a = self.choose_with_default(&constants, choice_of_a, nil.clone());
            let b = self.choose_with_default(&constants, choice_of_b, nil.clone());
            Rc::new(SExp::Cons(loc.clone(), a, b))
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
        let selector = b & 15;
        if selector == 0 {
            let choice_of_const = b >> 4;
            let constant = self.choose_with_default(&constants, choice_of_const, nil.clone());
            let constant_borrowed: &SExp = constant.borrow();
            Rc::new(BodyForm::Quoted(constant_borrowed.clone()))
        } else if selector < 7 {
            let choice_of_arg = b >> 3;
            let arg = self.choose_with_default(&atom_identifiers, choice_of_arg, vec![b'X']);
            Rc::new(BodyForm::Value(SExp::Atom(loc.clone(), arg)))
        } else if selector == 7 {
            let choice_of_cond = b >> 3;
            let choice_of_then: u16 = self.get_choice();
            let choice_of_else: u16 = self.get_choice();
            let use_cond = self.choose_with_default(&body_forms, choice_of_cond, body_nil.clone());
            let use_then = self.choose_with_default(&body_forms, choice_of_then, body_nil.clone());
            let use_else = self.choose_with_default(&body_forms, choice_of_else, body_nil.clone());
            Rc::new(BodyForm::Call(
                loc.clone(),
                vec![
                    Rc::new(BodyForm::Value(SExp::atom_from_string(loc.clone(), "if"))),
                    use_cond,
                    use_then,
                    use_else,
                ],
                None,
            ))
        } else if selector == 8 {
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
                None,
            ))
        } else if selector == 9 {
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
                None,
            ))
        } else if selector == 10 {
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
                None,
            ))
        } else if selector == 11 {
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

                let body = self.choose_with_default(&body_forms, choice_of_body, body_nil.clone());

                collected_names.push(arg_atom.clone());
                collected_bindings.push(Rc::new(Binding {
                    loc: loc.clone(),
                    nl: loc.clone(),
                    pattern: BindingPattern::Name(arg_atom),
                    body: body,
                }));
            }

            let body = self.choose_with_default(&body_forms, b >> 5, body_nil.clone());

            Rc::new(BodyForm::Let(
                kind,
                Box::new(LetData {
                    loc: loc.clone(),
                    kw: None,
                    bindings: collected_bindings,
                    body: body,
                    inline_hint: None, // todo: generate all kinds of inline hints
                }),
            ))
        } else {
            // Call
            if self.helper_structures.is_empty() {
                return body_nil.clone();
            }

            let choice_of_helper = (b >> 3) as usize % self.helper_structures.len();
            let helper_spec =
                self.helper_structures[choice_of_helper as usize % self.helper_structures.len()];
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
            Rc::new(BodyForm::Call(loc.clone(), call_args, None))
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
                kind: ConstantKind::Simple,
                kw: None,
                nl: loc.clone(),
                body: body,
            }),
            1 => HelperForm::Defun(
                is_inline,
                Box::new(DefunData {
                    loc: loc.clone(),
                    name: helper_name,
                    kw: None,
                    nl: loc.clone(),
                    orig_args: arguments.clone(),
                    args: arguments,
                    synthetic: Some(SyntheticType::NoInlinePreference),
                    body,
                }),
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
                    advanced: true,
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

// CollectProgramStructure becomes populated by a constrained set of bits.
// Use to_program to generate a CompileForm.
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
                if input_type == 0 {
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
                } else if input_type < 8 {
                    cps.body_forms.push(input_val);
                } else if input_type < 11 {
                    cps.arguments.push(input_val);
                } else if input_type < 12 {
                    cps.constants.push(input_val);
                } else {
                    cps.selectors.push(input_val);
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
