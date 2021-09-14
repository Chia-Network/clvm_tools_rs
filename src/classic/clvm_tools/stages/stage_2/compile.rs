use std::rc::Rc;
use std::collections::{
    HashMap,
    HashSet
};

use clvm_rs::allocator::{
    Allocator,
    AtomBuf,
    NodePtr,
    SExp
};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::{
    EvalErr,
    Reduction,
    Response
};

use clvm_rs::operator_handler::OperatorHandler;

use crate::classic::clvm::{
    KEYWORD_FROM_ATOM,
    KEYWORD_TO_ATOM
};
use crate::classic::clvm::sexp::{
    proper_list,
    enlist,
    first,
    rest
};

use crate::classic::clvm_tools::binutils::disassemble;
use crate::classic::clvm_tools::NodePath::NodePath;
use crate::classic::clvm_tools::stages::stage_0::{
    DefaultProgramRunner,
    TRunProgram
};
use crate::classic::clvm_tools::stages::stage_2::defaults::DEFAULT_MACRO_LOOKUP;
use crate::classic::clvm_tools::stages::stage_2::helpers::{
    brun,
    evaluate,
    quote
};
use crate::classic::clvm_tools::stages::stage_2::module::compile_mod;

lazy_static! {
    static ref PASS_THROUGH_OPERATORS: HashSet<Vec<u8>> = {
        let mut result = HashSet::new();
        for key in KEYWORD_TO_ATOM().keys() {
            result.insert(key.as_bytes().to_vec());
        }
        for key in KEYWORD_FROM_ATOM().keys() {
            result.insert(key.to_vec());
        }
        return result;
    };
}

struct Closure<'a> {
    name: String,
    to_run: &'a dyn Fn(&mut Allocator, NodePtr, NodePtr, NodePtr, Rc<dyn TRunProgram>, usize) -> Result<NodePtr, EvalErr>
}

fn compile_bindings<'a>() -> HashMap<Vec<u8>, Closure<'a>> {
    let mut bindings = HashMap::new();
    let bindings_source = vec!(
        Closure { name: "qq".to_string(), to_run: &compile_qq },
        Closure { name: "macros".to_string(), to_run: &compile_macros },
        Closure { name: "symbols".to_string(), to_run: &compile_symbols },
        Closure { name: "lambda".to_string(), to_run: &compile_mod },
        Closure { name: "mod".to_string(), to_run: &compile_mod }
    );

    for c in bindings_source {
        bindings.insert(c.name.as_bytes().to_vec(), c);
    }

    return bindings;
}

fn qq_atom() -> Vec<u8> { return vec!('q' as u8, 'q' as u8); }
fn unquote_atom() -> Vec<u8> { return "unquote".as_bytes().to_vec(); }

#[derive(Clone)]
pub struct DoComProg {
    runner: Rc<dyn TRunProgram>
}

fn com_qq(
    allocator: &mut Allocator,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    runner: Rc<dyn TRunProgram>,
    sexp: NodePtr
) -> Result<NodePtr, EvalErr> {
    return m! {
        qq <- allocator.new_atom(&qq_atom());
        com_prog <- allocator.new_pair(qq, sexp);
        do_com_prog(allocator, com_prog, macro_lookup, symbol_table, runner)
    }.map(|x| x.1);
}

pub fn compile_qq(
    allocator: &mut Allocator,
    args: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    runner: Rc<dyn TRunProgram>,
    level: usize
) -> Result<NodePtr, EvalErr> {
    /*
     * (qq ATOM) => (q . ATOM)
     * (qq (unquote X)) => X
     * (qq (a . B)) => (c (qq a) (qq B))
     */

    let null = allocator.null();

    match allocator.sexp(args) {
        SExp::Atom(_b) => {
            // (qq ATOM) => (q . ATOM)
            return quote(allocator, args);
        },
        SExp::Pair(l,r) => {
            match allocator.sexp(l) {
                SExp::Atom(op) => {
                    if allocator.buf(&op).to_vec() == qq_atom() {
                        return m! {
                            cons_atom <- allocator.new_atom(&vec!(4));
                            subexp <-
                                compile_qq(allocator, r, macro_lookup, symbol_table, runner.clone(), level+1);
                            consed <- enlist(allocator, &vec!(cons_atom, subexp, null));
                            enlist(allocator, &vec!(cons_atom, l, consed))
                        };
                    } else if allocator.buf(&op).to_vec() == unquote_atom() {
                        if level == 1 {
                            // (qq (unquote X)) => X
                            return m! {
                                rest_of <- rest(allocator, args);
                                first(allocator, rest_of)
                            };
                        }
                        return m! {
                            cons_atom <- allocator.new_atom(&vec!(4));
                            subexp <-
                                compile_qq(allocator, r, macro_lookup, symbol_table, runner.clone(), level-1);
                            consed <- enlist(allocator, &vec!(cons_atom, subexp, null));
                            enlist(allocator, &vec!(cons_atom, l, consed))
                        };
                    }

                    // (qq (a . B)) => (c (qq a) (qq B))
                    return m! {
                        cons_atom <- allocator.new_atom(&vec!(4));
                        compiled_l <- com_qq(allocator, macro_lookup, symbol_table, runner.clone(), l);
                        compiled_r <- com_qq(allocator, macro_lookup, symbol_table, runner, r);
                        enlist(allocator, &vec!(cons_atom, compiled_l, compiled_r))
                    };
                },
                _ => Ok(args)
            }
        }
    }
}

pub fn compile_macros(
    allocator: &mut Allocator,
    args: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>,
    _level: usize
) -> Result<NodePtr, EvalErr> {
    return quote(allocator, macro_lookup);
}

pub fn compile_symbols(
    allocator: &mut Allocator,
    args: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>,
    _level: usize
) -> Result<NodePtr, EvalErr> {
    return quote(allocator, symbol_table);
}

// # Transform "quote" to "q" everywhere. Note that quote will not be compiled if behind qq.
// # Overrides symbol table defns.
pub fn lower_quote(
    allocator: &mut Allocator,
    prog: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    if prog == allocator.null() {
        return Ok(prog);
    }

    match proper_list(allocator, prog, true) {
        Some(qlist) => {
            if qlist.len() == 0 {
                return Ok(prog);
            }

            match allocator.sexp(qlist[0]) {
                SExp::Atom(q) => {
                    if allocator.buf(&q).to_vec() == "quote".as_bytes().to_vec() {
                        // Note: quote should have exactly one arg, so the length of
                        // quoted list should be 2: "(quote arg)"
                        if qlist.len() == 1 {
                            return Ok(allocator.null());
                        } else if qlist.len() > 2 {
                            return Err(EvalErr(prog, format!("Compilation error while compiling [{:?}]. quote takes exactly one argument.", disassemble(allocator, prog))));
                        }

                        return m! {
                            lowered <-
                                lower_quote(
                                    allocator,
                                    qlist[1],
                                    macro_lookup,
                                    symbol_table,
                                    run_program
                                );
                            quote(allocator, lowered)
                        };
                    } else {
                        // XXX Note that this recognizes potentially unintended
                        // syntax, in that (sha256 3 quote ()) is valid in this
                        // code.  It is corrected in the new compiler but left
                        // here in case this bug is exploited.
                        // Like a good neighbor, UB is there☺
                        match allocator.sexp(prog) {
                            SExp::Pair(f,r) => {
                                return m! {
                                    first <-
                                        lower_quote(
                                            allocator,
                                            f,
                                            macro_lookup,
                                            symbol_table,
                                            run_program.clone()
                                        );
                                    rest <-
                                        lower_quote(
                                            allocator,
                                            r,
                                            macro_lookup,
                                            symbol_table,
                                            run_program.clone()
                                        );
                                    allocator.new_pair(first, rest)
                                };
                            },
                            SExp::Atom(_) => { }

                        };
                    }
                },
                _ => { }
            }
        },
        _ => { }
    }

    return Ok(prog);
}

fn try_expand_macro_for_atom(
    allocator: &mut Allocator,
    macro_value: NodePtr,
    prog: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>
) -> Response {
    return m! {
        com_atom <- allocator.new_atom("com".as_bytes());
        macro_pair_rest <- rest(allocator, macro_value);
        macro_code <- first(allocator, macro_pair_rest);
        prog_rest <- rest(allocator, prog);
        post_prog <- brun(allocator, macro_code, prog);
        quoted_macros <- quote(allocator, macro_lookup);
        quoted_symbols <- quote(allocator, symbol_table);
        to_eval <- enlist(
            allocator,
            &vec!(
                com_atom,
                post_prog,
                quoted_macros,
                quoted_symbols
            )
        );
        top_path <- allocator.new_atom(NodePath::new(None).as_path().data());
        evaluate(allocator, to_eval, top_path).map(|x| Reduction(1, x))
    };
}

fn get_macro_program(
    allocator: &mut Allocator,
    operator: NodePtr,
    macro_lookup: NodePtr
) -> Result<Option<NodePtr>, EvalErr> {
    match (
        allocator.sexp(operator),
        proper_list(allocator, macro_lookup, true)
    ) {
        (SExp::Atom(a), Some(mlist)) => {
            for macro_pair in mlist {
                match proper_list(allocator, macro_pair, true) {
                    None => { },
                    Some(mp_list) => {
                        if mp_list.len() == 0 {
                            continue;
                        }
                        let value =
                            if mp_list.len() > 1 {
                                mp_list[1]
                            } else {
                                allocator.null()
                            };

                        match allocator.sexp(mp_list[0]) {
                            SExp::Atom(macro_name) => {
                                if allocator.buf(&macro_name).to_vec() == allocator.buf(&a).to_vec() {
                                }
                            },
                            SExp::Pair(_,_) => { continue; }
                        }
                    }
                }
            }
        },
        _ => { }
    }

    return Ok(None);
}

fn transform_program_atom(
    allocator: &mut Allocator,
    prog: NodePtr,
    a: &AtomBuf,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>
) -> Response {
    if allocator.buf(&a).to_vec() == "@".as_bytes().to_vec() {
        return allocator.new_atom(NodePath::new(None).as_path().data()).
            map(|x| Reduction(1, x));
    }
    match proper_list(allocator, symbol_table, true) {
        None => { },
        Some(symlist) => {
            for sym in symlist {
                match proper_list(allocator, sym, true) {
                    None => { },
                    Some(v) => {
                        if v.len() == 0 {
                            continue;
                        }

                        let value =
                            if v.len() > 1 {
                                v[1]
                            } else {
                                allocator.null()
                            };

                        match allocator.sexp(v[0]) {
                            SExp::Atom(s) => {
                                if allocator.buf(&s).to_vec() == allocator.buf(a).to_vec() {
                                    return Ok(Reduction(1, value));
                                }
                            },
                            SExp::Pair(l,r) => {
                            }
                        }
                    }
                }
            }
        }
    }

    return quote(allocator, prog).map(|x| Reduction(1, x));
}

fn compile_operator_atom(
    allocator: &mut Allocator,
    prog: NodePtr,
    a: &AtomBuf,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>
) -> Result<Option<NodePtr>, EvalErr> {
    let COMPILE_BINDINGS = compile_bindings();
    let avec = allocator.buf(a).to_vec();

    print!("avec {:?} bindings {:?}\n", avec, COMPILE_BINDINGS.keys().collect::<Vec<&Vec<u8>>>());

    match COMPILE_BINDINGS.get(&avec) {
        Some(f) => {
            return m! {
                prog_rest <- rest(allocator, prog);
                post_prog <-
                    (f.to_run)(
                        allocator,
                        prog_rest,
                        macro_lookup,
                        symbol_table,
                        run_program,
                        2
                    );
                quoted_post_prog <- quote(allocator, post_prog);
                top_atom <-
                    allocator.new_atom(NodePath::new(None).as_path().data());

                let _ = print!("evaluate {}\n", disassemble(allocator, quoted_post_prog));

                evaluate(
                    allocator,
                    quoted_post_prog,
                    top_atom
                ).map(|x| Some(x))
            };
        },
        None => { }
    }

    if avec == vec!('q' as u8) {
        return Ok(Some(prog));
    } else {
        return Ok(None);
    }
}

enum SymbolResult {
    Direct(Response),
    Matched(NodePtr,NodePtr)
}

fn find_symbol_match(
    allocator: &mut Allocator,
    prog: NodePtr,
    opbuf: &AtomBuf,
    compiled_args: Vec<NodePtr>,
    symbol_table: NodePtr
) -> Result<Option<SymbolResult>, EvalErr> {
    match proper_list(allocator, symbol_table, true) {
        Some(symlist) => {
            for sym in symlist {
                match proper_list(allocator, sym, true) {
                    Some(symdef) => {
                        if symdef.len() < 1 { continue; }

                        match allocator.sexp(symdef[0]) {
                            SExp::Atom(symptr) => {
                                let symbol = symdef[0];
                                let value =
                                    if symdef.len() == 1 {
                                        allocator.null()
                                    } else {
                                        symdef[1]
                                    };

                                let symbuf = allocator.buf(&symptr).to_vec();
                                let opvec = allocator.buf(&opbuf).to_vec();
                                if vec!('*' as u8) == symbuf {
                                        return enlist(
                                            allocator,
                                            &compiled_args
                                        ).map(|v| Some(SymbolResult::Direct(Ok(Reduction(1, v)))));
                                    } else if opvec == symbuf {
                                        return Ok(Some(SymbolResult::Matched(symbol,value)));
                                    }
                            },

                            SExp::Pair(l,r) => { }
                        }
                    },
                    _ => { }
                }
            }
        },
        _ => { }
    }

    return Ok(None);
}

fn compile_application(
    allocator: &mut Allocator,
    prog: NodePtr,
    operator: NodePtr,
    fbuf: &AtomBuf,
    rest: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>
) -> Result<NodePtr, EvalErr> {
    let mut compiled_args = vec!(operator);

    let error_result =
        Err(EvalErr(prog, format!("can't compile {}, unknown operator", disassemble(allocator, prog))));

    match proper_list(allocator, rest, true) {
        Some(prog_args) => {
            for arg in prog_args {
                match do_com_prog(allocator, arg, macro_lookup, symbol_table, run_program.clone()) {
                    Err(e) => { return Err(e); },
                    Ok(compiled) => { compiled_args.push(compiled.1); }
                }
            }

            let opbuf = allocator.buf(&fbuf).to_vec();
            print!("opbuf {:?} args {:?}\n", opbuf, compiled_args);
            if PASS_THROUGH_OPERATORS.contains(&opbuf) || (opbuf.len() > 0 && opbuf[0] == '_' as u8) {
                return enlist(allocator, &compiled_args);
            }

            print!("find symbol\n");
            find_symbol_match(
                allocator,
                prog,
                &fbuf,
                compiled_args,
                symbol_table
            ).and_then(|x| match x {
                Some(SymbolResult::Direct(v)) => { v.map(|x| x.1) },
                Some(SymbolResult::Matched(symbol,value)) => {
                    return match proper_list(allocator, prog, true) {
                        Some(proglist) => {
                            m! {
                                apply_atom <- allocator.new_atom(&vec!(2));
                                list_atom <- allocator.new_atom("list".as_bytes());
                                cons_atom <- allocator.new_atom(&vec!(4));
                                com_atom <- allocator.new_atom("com".as_bytes());
                                opt_atom <- allocator.new_atom("opt".as_bytes());
                                top_atom <- allocator.new_atom(NodePath::new(None).as_path().data());
                                left_atom <- allocator.new_atom(NodePath::new(None).first().as_path().data());

                                enlisted <- enlist(allocator, &proglist[1..].to_vec());
                                list_application <- allocator.new_pair(list_atom, enlisted);
                                quoted_macros <- quote(allocator, macro_lookup);
                                quoted_symbols <- quote(allocator, symbol_table);
                                compiled <- enlist(allocator, &vec!(com_atom, list_application, quoted_macros, quoted_symbols));
                                to_run <- enlist(allocator, &vec!(opt_atom, compiled));
                                new_args <- evaluate(allocator, to_run, top_atom);

                                cons_enlisted <- enlist(allocator, &vec!(cons_atom, left_atom, new_args));

                                enlist(
                                    allocator,
                                    &vec!(apply_atom, value, cons_enlisted)
                                )
                            }
                        },
                        None => { error_result }
                    };
                },
                None => { error_result }
            })
        },
        None => { error_result }
    }
}

pub fn do_com_prog(
    allocator: &mut Allocator,
    prog: NodePtr,
    macro_lookup: NodePtr,
    symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>
) -> Response {
    /*
     * Turn the given program `prog` into a clvm program using
     * the macros to do transformation.
     * prog is an uncompiled s-expression.
     * Return a new expanded s-expression PROG_EXP that is equivalent by rewriting
     * based upon the operator, where "equivalent" means
     * (a (com (q PROG) (MACROS)) ARGS) == (a (q PROG_EXP) ARGS)
     * for all ARGS.
     * Also, (opt (com (q PROG) (MACROS))) == (opt (com (q PROG_EXP) (MACROS)))
     */

    // lower "quote" to "q"
    print!("do_com_prog {}\n", disassemble(allocator, prog));
    return m! {
        prog <- lower_quote(
            allocator, prog, macro_lookup, symbol_table, run_program.clone()
        );

        let _ = print!("lowered {}\n", disassemble(allocator, prog));

        // quote atoms
        match allocator.sexp(prog) {
            SExp::Atom(a) => {
                transform_program_atom(
                    allocator,
                    prog,
                    &a,
                    macro_lookup,
                    symbol_table,
                    run_program.clone()
                )
            },
            SExp::Pair(operator,r) => {
                let _ = print!("operator {}\n", disassemble(allocator, operator));
                match proper_list(allocator, operator, false) {
                    Some(_) => {
                        // (com ((OP) . RIGHT)) => (a (com (q OP)) 1)
                        return m! {
                            com_atom <- allocator.new_atom("com".as_bytes());
                            quoted_op <- quote(allocator, operator);
                            quoted_macro_lookup <-
                                quote(allocator, macro_lookup);
                            quoted_symbol_table <-
                                quote(allocator, symbol_table);
                            top_atom <- allocator.new_atom(NodePath::new(None).as_path().data());
                            eval_list <- enlist(allocator, &vec!(
                                com_atom,
                                quoted_op,
                                quoted_macro_lookup,
                                quoted_symbol_table
                            ));
                            let _ = print!("compile: {} {}\n", disassemble(allocator, eval_list), disassemble(allocator, top_atom));
                            inner_exp <- evaluate(
                                allocator, eval_list, top_atom
                            );
                            enlist(allocator, &vec!(inner_exp)).
                                map(|x| Reduction(1, x))
                        };
                    },
                    _ => {
                    }
                }

                get_macro_program(allocator, operator, macro_lookup).
                    and_then(|x| match x {
                        Some(value) => {
                            try_expand_macro_for_atom(
                                allocator,
                                value,
                                prog,
                                macro_lookup,
                                symbol_table,
                                run_program.clone()
                            )
                        },
                        None => {
                            match allocator.sexp(operator) {
                                SExp::Atom(a) => {
                                    compile_operator_atom(
                                        allocator,
                                        prog,
                                        &a,
                                        macro_lookup,
                                        symbol_table,
                                        run_program.clone()
                                    ).and_then(|x| x.map(|y| Ok(y)).unwrap_or_else(|| m! {
                                        rest <- rest(allocator, prog);
                                        let _ = print!("handling program body with op {} and args {}\n", disassemble(allocator, operator), disassemble(allocator, rest));
                                        compile_application(
                                            allocator,
                                            prog,
                                            operator,
                                            &a,
                                            rest,
                                            macro_lookup,
                                            symbol_table,
                                            run_program.clone()
                                        )
                                    })).map(|x| Reduction(1, x))
                                },
                                SExp::Pair(f,l) => { Ok(Reduction(1, prog)) }
                            }
                        }
                    })
            }
        }
    };
}

impl OperatorHandler for DoComProg {
    fn op(
        &self,
        allocator: &mut Allocator,
        _op: NodePtr,
        sexp: NodePtr,
        _max_cost: Cost
    ) -> Response {
        match allocator.sexp(sexp) {
            SExp::Pair(prog,extras) => {
                let macro_lookup;
                let mut symbol_table = allocator.null();

                match allocator.sexp(extras) {
                    SExp::Pair(macros, symbols) => {
                        macro_lookup = macros;
                        symbol_table = symbols;
                    },
                    _ => {
                        macro_lookup = allocator.null();
                        //DEFAULT_MACRO_LOOKUP(allocator, self.runner.clone());
                    }
                }

                return do_com_prog(
                    allocator,
                    prog,
                    macro_lookup,
                    symbol_table,
                    self.runner.clone()
                );
            },
            _ => {
                return Err(EvalErr(sexp, "Program is not a pair in do_com_prog".to_string()));
            }
        }
    }
}

impl DoComProg {
    pub fn new() -> Self {
        return DoComProg { runner: Rc::new(DefaultProgramRunner::new()) };
    }

    pub fn set_runner(&mut self, runner: Rc<dyn TRunProgram>) {
        self.runner = runner;
    }
}
