use std::collections::HashMap;

use rsmt2::{Logic, Solver};
use rsmt2::errors::{Error, ErrorKind, SmtRes};

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

impl SMTSolver {
    pub fn new() -> SmtRes<Self> {
        Ok(SMTSolver {
            solver: Solver::default_z3(())?
        })
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
        // declare-sort
        // declare-fun
        // define-sort
        // define-fun
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

        eprintln!("op {}", decode_string(&op));

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
        } else if op == b"declare-sort" && p.len() == 3 {
            if let (SExp::Atom(_,name), SExp::Integer(_,i)) = (&p[1], &p[2]) {
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
        } else if op == b"define-fun" && p.len() == 5 {
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
                self.solver.define_fun(decode_string(&name), &argvec, p[3].to_string(), p[4].to_string())?;
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
        }

        Err(Error::from_kind(
            ErrorKind::ParseError(
                stmt.to_string(),
                "unrecognized keyword".to_string()
            )
        ))
    }
}
