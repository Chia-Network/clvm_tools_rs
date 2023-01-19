use std::collections::HashMap;
use std::io::Write;
use std::rc::Rc;

use rsmt2::{Logic, Solver};
use rsmt2::errors::{Error, ErrorKind, SmtRes};
use rsmt2::print::{AdtDecl, AdtVariant, AdtVariantField, Sort2Smt, Sym2Smt};

use crate::classic::clvm::__type_compatibility__::{bi_one, bi_zero};
use crate::compiler::sexp::{decode_string, SExp};
use crate::util::Number;

lazy_static! {
    pub static ref LOGICS: HashMap<String, Logic> = {
        let mut res = HashMap::new();
        // Quantifier-free uninterpreted functions.
        res.insert("QF_UF".to_string(), Logic::QF_UF);

        // Quantifier-free linear integer arithmetic.
        res.insert("QF_LIA".to_string(), Logic::QF_LIA);

        // Quantifier-free non-linear integer arithmetic.
        res.insert("QF_NIA".to_string(), Logic::QF_NIA);

        // Quantifier-free linear real arithmetic.
        res.insert("QF_LRA".to_string(), Logic::QF_LRA);

        // Quantifier-free arrays, uninterpreted functions, linear integer arithmetic.
        res.insert("QF_AUFLIA".to_string(), Logic::QF_AUFLIA);

        // Arrays, uninterpreted functions, linear integer arithmetic.
        res.insert("AUFLIA".to_string(), Logic::AUFLIA);

        // Arrays, uninterpreted functions, linear integer/real arithmetic.
        res.insert("AUFLIRA".to_string(), Logic::AUFLIRA);

        // arrays, uninterpreted functions, non-linear integer/real arithmetic.
        res.insert("AUFNIRA".to_string(), Logic::AUFNIRA);

        // Linear real arithmetic.
        res.insert("LRA".to_string(), Logic::LRA);

        // Quantifier-free fixed-size bitvectors.
        res.insert("QF_BV".to_string(), Logic::QF_BV);

        // Quantifier-free uninterpreted functions, fixed-size bitvectors.
        res.insert("QF_UFBV".to_string(), Logic::QF_UFBV);

        // Quantifier-free arrays, fixed-size bitvectors.
        res.insert("QF_ABV".to_string(), Logic::QF_ABV);

        // Quantifier-free arrays, uninterpreted functions, fixed-size bitvectors.
        res.insert("QF_AUFBV".to_string(), Logic::QF_AUFBV);

        res
    };
}

pub struct SMTOutput {
}

pub struct SMTSolver {
    solver: Solver<()>
}

fn to_u8(i: &Number) -> u8 {
    let (_, d) = i.to_u32_digits();
    if d.is_empty() {
        0
    } else {
        d[d.len()-1] as u8
    }
}

fn integerize(stmt: &SExp, s: &SExp) -> SmtRes<SExp> {
    match s {
        SExp::Nil(l) => Ok(SExp::Integer(l.clone(), bi_zero())),
        SExp::Integer(_, _) => Ok(s.clone()),
        _ => {
            Err(Error::from_kind(
                ErrorKind::ParseError(
                    stmt.to_string(),
                    format!("argument {} must be an integer in {}", s, stmt)
                )
            ))
        }
    }
}

#[derive(Clone, Debug)]
pub struct GenericAdtString {
    s: String
}

impl GenericAdtString {
    fn new(s: String) -> Self {
        GenericAdtString { s }
    }
}

impl Sym2Smt for GenericAdtString {
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, i: ()) -> Result<(), rsmt2::prelude::Error> where Writer: Write {
        writer.write(self.s.as_bytes()).map(|_| ()).map_err(|_| {
            Error::from_kind(
                ErrorKind::ParseError(
                    self.s.clone(),
                    "failed to convert string".to_string()
                )
            )
        })
    }
}

impl Sort2Smt for GenericAdtString {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> Result<(), rsmt2::prelude::Error> where Writer: Write {
        writer.write(self.s.as_bytes()).map(|_| ()).map_err(|_| {
            Error::from_kind(
                ErrorKind::ParseError(
                    self.s.clone(),
                    "failed to convert string".to_string()
                )
            )
        })
    }
}

pub struct GenericAdtField {
    sym: GenericAdtString,
    sort: GenericAdtString
}

impl GenericAdtField {
    // As usual, `AdtVariantField` is implemented for certain pairs.
    fn as_decl(&self) -> impl AdtVariantField {
        (self.sym.clone(), self.sort.clone())
    }
}

pub struct GenericAdtVariant {
    sym: GenericAdtString,
    fields: Vec<GenericAdtField>
}

impl GenericAdtVariant {
    // Variant declaration; again, `AdtVariant` is implemented for certain types of pairs.
    fn as_decl<'me>(&'me self) -> impl AdtVariant + 'me {
        (
            // Symbol.
            self.sym.clone(),
            // Iterator over field declarations.
            self.fields.iter().map(GenericAdtField::as_decl),
        )
    }
}

pub struct GenericAdtSort {
    sym: GenericAdtString,
    args: Vec<GenericAdtString>,
    variants: Vec<GenericAdtVariant>
}

impl GenericAdtSort {
    // This thing build the actual definition expected by rsmt2. Its output is something that
    // implements `AdtDecl` and can only live as long as the input ref to `self`.
    fn as_decl<'me>(&'me self) -> impl AdtDecl + 'me {
        // Check out rsmt2's documentation and you'll see that `AdtDecl` is already implemented for
        // certain triplets.
        (
            // Symbol.
            self.sym.clone(),
            // Sized collection of type-parameter symbols.
            &self.args,
            // Variant, collection of iterator over `impl AdtVariant` (see below).
            self.variants.iter().map(GenericAdtVariant::as_decl),
        )
    }
}

impl SMTSolver {
    pub fn new() -> SmtRes<Self> {
        Ok(SMTSolver {
            solver: Solver::default_z3(())?
        })
    }

    pub fn prepare_smt(&mut self) -> SmtRes<SExp> {
        todo!();
    }

    pub fn run_stmt(&mut self, stmt: &SExp) -> SmtRes<SExp> {
        let done = Ok(SExp::Nil(stmt.loc()));

        // Parse statement into smt-lib form
        //
        // smt-lib statement types:
        // set-logic
        // declare-const
        // assert
        // reset
        // push
        // pop
        // declare-datatype
        // declare-sort
        // declare-fun
        // define-sort
        // define-fun
        // define-fun-rec
        // check_sat
        let p =
            if let Some(p) = stmt.proper_list() {
                Ok(p)
            } else {
                Err(Error::from_kind(
                    ErrorKind::ParseError(
                        stmt.to_string(),
                        "Improper list".to_string()
                    )
                ))
            }?;
        if p.is_empty() {
            return Err(Error::from_kind(
                ErrorKind::ParseError(
                    stmt.to_string(),
                    "Empty list".to_string()
                )
            ));
        }

        let op =
            if let SExp::Atom(_,op) = &p[0] {
                Ok(op.clone())
            } else {
                Err(Error::from_kind(
                    ErrorKind::ParseError(
                        stmt.to_string(),
                        "not a keyword starting the statement".to_string()
                    )
                ))
            }?;

        if op == b"set-logic" && p.len() == 2 {
            if let SExp::Atom(_,name) = &p[1] {
                if let Some(l) = LOGICS.get(&decode_string(&name)) {
                    self.solver.set_logic(l.clone())?;
                    return done;
                }
            }
        } else if op == b"declare-const" && p.len() == 3 {
            if let SExp::Atom(_,name) = &p[1] {
                self.solver.declare_const(decode_string(&name), p[2].to_string())?;
                return done;
            }

            return Err(Error::from_kind(
                ErrorKind::ParseError(
                    stmt.to_string(),
                    "name wasn't an atom".to_string()
                )
            ));
        } else if op == b"assert" && p.len() == 2 {
            self.solver.assert(p[1].to_string())?;
            return done;
        } else if op == b"reset" && p.len() == 1 {
            self.solver.reset()?;
            return done;
        } else if op == b"push" && p.len() == 2 {
            if let SExp::Integer(_,i) = &p[1] {
                let n = to_u8(&i);
                self.solver.push(n)?;
                return done;
            }
        } else if op == b"pop" && p.len() == 2 {
            if let SExp::Integer(_,i) = &p[1] {
                let n = to_u8(&i);
                self.solver.pop(n)?;
                return done;
            }
        } else if op == b"declare-datatype" && p.len() == 3 {
            if let SExp::Atom(_,name) = &p[1] {
                if let Some(vlist) = p[2].proper_list() {
                    let mut new_sort = GenericAdtSort {
                        sym: GenericAdtString::new(decode_string(&name)),
                        args: Vec::new(),
                        variants: Vec::new()
                    };
                    if vlist.is_empty() {
                        self.solver.declare_datatypes([new_sort.as_decl()].iter())?;
                        return done;
                    }

                    let mut start_variants = 0;
                    if let SExp::Atom(_, par_name) = &vlist[0] {
                        if par_name == b"par" && vlist.len() > 1 {
                            // Take parameters.
                            if let Some(plist) = vlist[1].proper_list() {
                                for par in plist.iter() {
                                    if let SExp::Atom(_,pname) = &par {
                                        new_sort.args.push(GenericAdtString::new(decode_string(&pname)));
                                    } else {
                                        // Error
                                        todo!()
                                    }
                                }
                            } else {
                                // Error
                                todo!()
                            }
                            start_variants = 2;
                        }
                    }

                    for v in vlist.iter().skip(start_variants) {
                        // form of (name (accessor type) ...)
                        if let Some(variant_list) = v.proper_list() {
                            if variant_list.is_empty() {
                                // Error
                                todo!()
                            }
                            if let SExp::Atom(_,varname) = &variant_list[0] {
                                let mut variant = GenericAdtVariant {
                                    sym: GenericAdtString::new(decode_string(&varname)),
                                    fields: Vec::new()
                                };
                                for field in variant_list.iter().skip(1) {
                                    if let Some(flist) = field.proper_list() {
                                        if flist.len() != 2 {
                                            // Error
                                            todo!()
                                        }
                                        if let (SExp::Atom(_, fname), SExp::Atom(_, sname)) = (&flist[0], &flist[1]) {
                                            variant.fields.push(GenericAdtField {
                                                sym: GenericAdtString::new(decode_string(&fname)),
                                                sort: GenericAdtString::new(decode_string(&sname))
                                            });
                                        } else {
                                            // Error
                                            todo!()
                                        }
                                    } else {
                                        // Error
                                        todo!()
                                    }
                                }
                                new_sort.variants.push(variant);
                            } else {
                                // Error
                                todo!()
                            }
                        } else {
                            // Error
                            todo!()
                        }
                    }
                    self.solver.declare_datatypes(&[new_sort.as_decl()])?;
                    return done;
                }
            }
        } else if op == b"declare-sort" && p.len() == 3 {
            if let (SExp::Atom(_,name), SExp::Integer(_,i)) = (&p[1], integerize(&stmt, &p[2])?) {
                let n = to_u8(&i);
                self.solver.declare_sort(decode_string(&name), n)?;
                return done;
            }
        } else if op == b"declare-fun" && p.len() == 4 {
            if let (SExp::Atom(_,name), Some(lst)) =
                (&p[1], p[2].proper_list())
            {
                let mut argvec = Vec::new();
                for a in lst.iter() {
                    argvec.push(a.to_string());
                }
                self.solver.declare_fun(decode_string(&name), &argvec, p[3].to_string())?;
                return done;
            }
        } else if op == b"define-sort" && p.len() == 4 {
            if let (SExp::Atom(_,name), Some(lst)) =
                (&p[1], p[2].proper_list())
            {
                let mut argvec = Vec::new();
                for a in lst.iter() {
                    if let SExp::Atom(_,name) = a {
                        argvec.push(decode_string(&name));
                    } else {
                        return Err(Error::from_kind(
                            ErrorKind::ParseError(
                                stmt.to_string(),
                                "non-symbol argument".to_string()
                            )
                        ));
                    }
                }
                self.solver.define_sort(decode_string(&name), &argvec, p[3].to_string())?;
                return done;
            }
        } else if (op == b"define-fun" || op == b"define-fun-rec") && p.len() == 5 {
            if let (SExp::Atom(_,name), Some(lst)) =
                (&p[1], p[2].proper_list())
            {
                let mut argvec = Vec::new();
                for a in lst.iter() {
                    if let Some(alst) = a.proper_list() {
                        if alst.len() != 2 {
                            return Err(Error::from_kind(
                                ErrorKind::ParseError(
                                    stmt.to_string(),
                                    "non-pair argument".to_string()
                                )
                            ));
                        }
                        if let SExp::Atom(_,aname) = &alst[0] {
                            argvec.push((decode_string(&aname), alst[1].to_string()));
                        }
                    }
                }
                if op == b"define-fun" {
                    self.solver.define_fun(decode_string(&name), &argvec, p[3].to_string(), p[4].to_string())?;
                } else {
                    self.solver.define_funs_rec(&[
                        (decode_string(&name), &argvec, p[3].to_string(), p[4].to_string())
                    ])?;
                }
                return done;
            }
        } else if op == b"check-sat" {
            return self.solver.check_sat().map(|b| {
                if b {
                    SExp::Integer(stmt.loc(), bi_one())
                } else {
                    SExp::Integer(stmt.loc(), bi_zero())
                }
            });
        } else if op == b"want-unsat" {
            return self.solver.check_sat().and_then(|b| {
                if b {
                    return Err(Error::from_kind(
                        ErrorKind::ParseError(
                            stmt.to_string(),
                            "wanted unsat, got sat".to_string()
                        )
                    ));
                } else {
                    return Ok(SExp::Integer(stmt.loc(), bi_zero()));
                }
            });
        }

        Err(Error::from_kind(
            ErrorKind::ParseError(
                stmt.to_string(),
                "unrecognized keyword".to_string()
            )
        ))
    }
}
