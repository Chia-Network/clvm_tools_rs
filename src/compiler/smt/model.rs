use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::ToBigInt;

use clvmr::allocator::Allocator;

use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm::__type_compatibility__::{bi_zero, bi_one};

use crate::compiler::clvm::sha256tree;
use crate::compiler::codegen::codegen;
use crate::compiler::comptypes::BodyForm;
use crate::compiler::comptypes::CompilerOpts;
use crate::compiler::comptypes::CompileForm;
use crate::compiler::comptypes::CompileErr;
use crate::compiler::sexp::decode_string;
use crate::compiler::sexp::enlist;
use crate::compiler::sexp::parse_sexp;
use crate::compiler::sexp::SExp;
use crate::compiler::srcloc::Srcloc;

#[derive(Debug, Clone)]
pub struct Model {
}

fn hash_to_hex(program_hash: &[u8]) -> String {
    Bytes::new(Some(BytesFromType::Raw(program_hash.to_vec()))).hex()
}

fn make_constant(name: &str, body: &SExp) -> SExp {
    enlist(
        body.loc(),
        vec![
            Rc::new(SExp::atom_from_string(body.loc(), "define-fun")),
            Rc::new(SExp::atom_from_string(body.loc(), name)),
            Rc::new(SExp::Nil(body.loc())),
            Rc::new(SExp::atom_from_string(body.loc(), "Value")),
            Rc::new(body.clone())
        ]
    )
}

fn compose_atom(l: &Srcloc, n: usize, v: &[u8]) -> SExp {
    if n >= v.len() {
        SExp::atom_from_string(l.clone(), "Nil")
    } else {
        let rest = compose_atom(l, n + 1, v);
        enlist(
            l.clone(),
            vec![
                Rc::new(SExp::atom_from_string(l.clone(), "compose-atom")),
                Rc::new(SExp::Integer(l.clone(), v[n].to_bigint().unwrap())),
                Rc::new(rest)
            ]
        )
    }
}

impl Model {
    // We'll do something cheap:
    // take any function called test_fail_... and verify that it returning a value
    // is unsatisfiable.
    //
    // take any function called test_... and verify that it returning nil is
    // unsatisfiable.

    pub fn new() -> Model { Model { } }

    pub fn smt_prelude(&self) -> Vec<Rc<SExp>> {
        // The prelude we'll use
        parse_sexp(Srcloc::start("*smt-prelude*"), indoc!{"
            (declare-datatype Value ( (Nil) (Atom (atom-head Int) (atom-tail Value)) (Cons (first Value) (rest Value)) (Exception (expr Value)) (Error (code Value) ) ) )

            ;; Nil
            (define-fun is-nil ((v Value)) Bool (= v Nil))

            ;; Test is-nil
            (push 1)
              (assert (not (is-nil Nil)))
              (want-unsat)
            (pop 1)

            ;; Variables to be used later
            (declare-fun any-int () Int)
            (declare-fun any-value () Value)
            (declare-fun any-value2 () Value)
            (declare-fun any-value3 () Value)

            (define-fun make-exception ((v Value)) Value (Exception v))
            (define-fun make-error ((v Value)) Value (Error v))

            (define-fun is-error ((v Value)) Bool
              (match v (
                ((Error v) true)
                ((Exception v) true)
                (_ false)
              ))
              )

            (push 1)
              (assert (is-error Nil))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (not (is-error (make-error Nil))))
              (want-unsat)
            (pop 1)

            ;; Atom builder.
            (define-fun make-number-atom ((n Int)) Value (ite (= n (- 1 1)) Nil (Atom n Nil)))
            (push 1)
              (assert (not (is-nil (make-number-atom (- 1 1)))))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (is-nil (make-number-atom 1)))
              (want-unsat)
            (pop 1)

            ;; Cons
            (define-fun prim-c ((v1 Value) (v2 Value)) Value (Cons v1 v2))
            (push 1)
              (assert (is-nil (prim-c Nil Nil)))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (not (is-error (make-error Nil))))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (is-error Nil))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (not (match Nil ( ((Nil) true) (_ false)) )))
              (want-unsat)
            (pop 1)

            (push 1)
              (assert (not (match (Atom 1 Nil) ( ((Atom n o) (= n 1)) (_ false)  ) )))
              (want-unsat)
            (pop 1)

            (define-fun prim-odd ((n Int)) Bool (not (= n (* 2 (div n 2)))))

            (push 1)
              (assert (not (prim-odd 1)))
              (want-unsat)
            (pop 1)

            (define-fun first-of ((v Value)) Value
              (match v (
                ((Cons f _) f)
                ((Nil) (make-error v))
                ((Atom _ _) (make-error v))
                ((Error _) v)
                ((Exception _) v)
              ))
              )

            (push 1)
              (assert (not (is-error (first-of Nil))))
              (want-unsat)
            (pop 1)

            (push 1)
               (assert (not (= (first-of (prim-c (make-number-atom 3) (make-number-atom 5))) (make-number-atom 3))))
               (want-unsat)
            (pop 1)

            (define-fun rest-of ((v Value)) Value
              (match v (
                ((Cons _ r) r)
                ((Nil) (make-error v))
                ((Atom _ _) (make-error v))
                ((Error _) v)
                ((Exception _) v)
              ))
              )

            (push 1)
               (assert (not (= (rest-of (prim-c (make-number-atom 3) (make-number-atom 5))) (make-number-atom 5))))
               (want-unsat)
            (pop 1)

            (define-fun-rec choose-env ((n Int) (v Value)) Value
              (ite (= n (- 1 1))
                Nil
                (ite (= n 1)
                  v
                  (ite (prim-odd n)
                    (choose-env (div n 2) (rest-of v))
                    (choose-env (div n 2) (first-of v))
                    )
                  )
                )
              )

            (push 1)
              (assert (not (= (choose-env 5 (prim-c (make-number-atom 5) (prim-c (make-number-atom 7) Nil))) (make-number-atom 7))))
              (want-unsat)
            (pop 1)
        "}.bytes()).expect("should parse")
    }

    pub fn describe_program(
        &self,
        result: &mut Vec<Rc<SExp>>,
        serialized_parts: &mut HashMap<Vec<u8>, Rc<SExp>>,
        program: Rc<SExp>
    ) -> Vec<u8> {
        let program_hash = sha256tree(program.clone());
        if !serialized_parts.contains_key(&program_hash) {
            let target_program_hex = hash_to_hex(&program_hash);
            let target_program_name =
                format!("prog_{}", target_program_hex);

            match program.borrow() {
                SExp::Cons(l,a,b) => {
                    let part_b =
                        self.describe_program(result, serialized_parts, a.clone());
                    let part_a =
                        self.describe_program(result, serialized_parts, b.clone());
                    result.push(Rc::new(make_constant(
                        &target_program_name,
                        &enlist(
                            l.clone(),
                            vec![
                                Rc::new(SExp::atom_from_string(l.clone(), "prim-c")),
                                Rc::new(SExp::atom_from_string(l.clone(), &format!("prog_{}", hash_to_hex(&part_a)))),
                                Rc::new(SExp::atom_from_string(l.clone(), &format!("prog_{}", hash_to_hex(&part_b))))
                            ]
                        )
                    )));
                    serialized_parts.insert(program_hash.clone(), program.clone());
                }
                SExp::Nil(l) => {
                    result.push(Rc::new(make_constant(
                        &target_program_name,
                        &SExp::atom_from_string(l.clone(), "Nil")
                    )));
                    serialized_parts.insert(program_hash.clone(), program.clone());
                }
                SExp::Integer(l,i) => {
                    if i == &bi_zero() {
                        result.push(Rc::new(make_constant(
                            &target_program_name,
                            &SExp::atom_from_string(l.clone(), "Nil")
                        )));
                    } else {
                        result.push(Rc::new(make_constant(
                            &target_program_name,
                            &enlist(
                                l.clone(),
                                vec![
                                    Rc::new(SExp::atom_from_string(l.clone(), "make-number-atom")),
                                    Rc::new(SExp::Integer(l.clone(), i.clone()))
                                ]
                            )
                        )));
                    }
                    serialized_parts.insert(program_hash.clone(), program.clone());
                }
                SExp::QuotedString(_,_,s) => {
                    todo!();
                }
                SExp::Atom(l,x) => {
                    result.push(Rc::new(make_constant(
                        &target_program_name,
                        &compose_atom(&l, 0, x)
                    )));
                    serialized_parts.insert(program_hash.clone(), program.clone());
                }
            }
        }

        program_hash
    }

    pub fn smt_program(
        &self,
        runner: Rc<dyn TRunProgram>,
        opts: Rc<dyn CompilerOpts>,
        program: &CompileForm
    ) -> Result<Vec<Rc<SExp>>, CompileErr> {
        let mut result = Vec::new();
        let mut serialized = HashMap::new();

        for f in program.helpers.iter() {
            eprintln!("helper {}", decode_string(f.name()));
            if decode_string(f.name()).starts_with("test_") {
                // Encode test program.
                let mut compileform = program.clone();
                compileform.exp = Rc::new(BodyForm::Call(
                    f.loc(),
                    vec![
                        Rc::new(BodyForm::Value(SExp::Atom(f.loc(), f.name().to_vec())))
                    ]
                ));
                let mut symbols = HashMap::new();
                let mut allocator = Allocator::new();
                let program = codegen(
                    &mut allocator,
                    runner.clone(),
                    opts.clone(),
                    &compileform,
                    &mut symbols
                )?;
                let program_hash = self.describe_program(
                    &mut result,
                    &mut serialized,
                    Rc::new(program.clone())
                );
                let program_name = format!("prog_{}", hash_to_hex(&program_hash));
                result.push(Rc::new(enlist(
                    program.loc(),
                    vec![
                        Rc::new(SExp::atom_from_string(program.loc(), "push")),
                        Rc::new(SExp::Integer(program.loc(), bi_one()))
                    ]
                )));
                result.push(Rc::new(enlist(
                    program.loc(),
                    vec![
                        Rc::new(SExp::atom_from_string(program.loc(), "assert")),
                        Rc::new(enlist(
                            program.loc(),
                            vec![
                                Rc::new(SExp::atom_from_string(program.loc(), "is-nil")),
                                Rc::new(enlist(
                                    program.loc(),
                                    vec![
                                        Rc::new(SExp::atom_from_string(program.loc(), "execute")),
                                        Rc::new(SExp::atom_from_string(program.loc(), &program_name)),
                                        Rc::new(SExp::atom_from_string(program.loc(), "Nil"))
                                    ]
                                ))
                            ]
                        ))
                    ]
                )));
                result.push(Rc::new(enlist(
                    program.loc(),
                    vec![
                        Rc::new(SExp::atom_from_string(program.loc(), "want-unsat"))
                    ]
                )));
                result.push(Rc::new(enlist(
                    program.loc(),
                    vec![
                        Rc::new(SExp::atom_from_string(program.loc(), "pop")),
                        Rc::new(SExp::Integer(program.loc(), bi_one()))
                    ]
                )));
            }
        }

        Ok(result)
    }
}
