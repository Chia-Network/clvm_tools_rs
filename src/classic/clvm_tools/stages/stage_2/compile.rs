use std::rc::Rc;

use clvm_rs::allocator::{
    Allocator,
    NodePtr,
    SExp
};
use clvm_rs::cost::Cost;
use clvm_rs::reduction::{
    EvalErr,
    Reduction,
    Response
};

use clvm_rs::run_program::{
    OperatorHandler
};

use crate::classic::clvm_tools::stages::stage_0::{
    TRunProgram
};

use crate::classic::clvm::sexp::{
    enlist,
    first,
    rest
};

use crate::classic::clvm_tools::stages::stage_0::DefaultProgramRunner;
use crate::classic::clvm_tools::stages::stage_2::defaults::DEFAULT_MACRO_LOOKUP;
use crate::classic::clvm_tools::stages::stage_2::helpers::quote;

// export const PASS_THROUGH_OPERATORS = new Set(Object.values(KEYWORD_TO_ATOM));

fn qq_atom() -> Vec<u8> { return vec!('q' as u8, 'q' as u8); }
fn unquote_atom() -> Vec<u8> { return "unquote".as_bytes().to_vec(); }

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
    level: usize,
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

// export function compile_macros(args: SExp, macro_lookup: SExp, symbol_table: SExp, run_program: TRunProgram){
//   return SExp.to(quote(macro_lookup));
// }

// export function compile_symbols(args: SExp, macro_lookup: SExp, symbol_table: SExp, run_program: TRunProgram){
//   return SExp.to(quote(symbol_table));
// }

// export const COMPILE_BINDINGS = {
//   [b("qq").hex()]: compile_qq,
//   [b("macros").hex()]: compile_macros,
//   [b("symbols").hex()]: compile_symbols,
//   [b("lambda").hex()]: compile_mod,
//   [b("mod").hex()]: compile_mod,
// };

// // # Transform "quote" to "q" everywhere. Note that quote will not be compiled if behind qq.
// // # Overrides symbol table defns.
// export function lower_quote(
//   prog: SExp,
//   macro_lookup: SExp|None=None,
//   symbol_table: SExp|None=None,
//   run_program: TRunProgram|None = None,
// ): SExp {
//   if(prog.nullp()){
//     return prog;
//   }
  
//   if(prog.listp()){
//     if(b("quote").equal_to(prog.first().atom as Bytes)){
//       // Note: quote should have exactly one arg, so the length of
//       // quoted list should be 2: "(quote arg)"
//       if(!prog.rest().rest().nullp()){
//         throw new SyntaxError(`Compilation error while compiling [${disassemble(prog)}]. quote takes exactly one argument.`);
//       }
//       return SExp.to(quote(lower_quote(prog.rest().first())));
//     }
//     else{
//       return SExp.to(t(lower_quote(prog.first()), lower_quote(prog.rest())));
//     }
//   }
//   else{
//     return prog;
//   }
// }

pub fn do_com_prog(
    allocator: &mut Allocator,
    _prog: NodePtr,
    _macro_lookup: NodePtr,
    _symbol_table: NodePtr,
    _run_program: Rc<dyn TRunProgram>
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

//   // lower "quote" to "q"
//   prog = lower_quote(prog, macro_lookup, symbol_table, run_program);
  
//   // quote atoms
//   if(prog.nullp() || !prog.listp()){
//     const atom = prog.atom as Bytes;
//     if(b("@").equal_to(atom)){
//       return SExp.to(TOP.as_path());
//     }
//     for(const pair of symbol_table.as_iter()){
//       const [symbol, value] = [pair.first(), pair.rest().first()];
//       if(symbol.equal_to(atom)){
//         return SExp.to(value);
//       }
//     }
//     return SExp.to(quote(prog));
//   }
  
//   const operator = prog.first();
//   if(operator.listp()){
//     // (com ((OP) . RIGHT)) => (a (com (q OP)) 1)
//     const inner_exp = evaluate(SExp.to([b("com"),
//       quote(operator), quote(macro_lookup), quote(symbol_table)]), TOP.as_path());
//     return SExp.to([inner_exp]);
//   }
  
//   const atom = operator.atom as Bytes;
  
//   for(const macro_pair of macro_lookup.as_iter()){
//     const macro_name = macro_pair.first().atom as Bytes;
//     if(atom.equal_to(macro_name)){
//       const macro_code = macro_pair.rest().first();
//       const post_prog = brun(macro_code, prog.rest());
//       return evaluate(SExp.to(
//         [b("com"), post_prog, quote(macro_lookup), quote(symbol_table)]), TOP.as_short_path());
//     }
//   }
  
//   if(atom.hex() in COMPILE_BINDINGS){
//     const f = COMPILE_BINDINGS[atom.hex()];
//     const post_prog = f(prog.rest(), macro_lookup, symbol_table, run_program);
//     return evaluate(SExp.to(quote(post_prog)), TOP.as_path());
//   }
  
//   if(operator.equal_to(h(QUOTE_ATOM))){
//     return prog;
//   }
  
//   const compiled_args: SExp[] = [];
//   for(const _ of prog.rest().as_iter()){
//     compiled_args.push(do_com_prog(_, macro_lookup, symbol_table, run_program));
//   }
  
//   let r = SExp.to([operator].concat(compiled_args));
  
//   if(PASS_THROUGH_OPERATORS.has(atom.hex()) || atom.startswith(b("_"))){
//     return r;
//   }
  
//   for(const [symbol, value] of symbol_table.as_javascript() as Array<[Bytes, Bytes]>){
//     if(b("*").equal_to(symbol)){
//       return r;
//     }
//     if(atom.equal_to(symbol)){
//       const list: SExp[] = [];
//       for(const _ of prog.rest().as_iter()){
//         list.push(_);
//       }
//       const new_args = evaluate(
//         SExp.to([b("opt"), [b("com"),
//           quote(([b("list")] as [Bytes, ...SExp[]]).concat(list)),
//           quote(macro_lookup),
//           quote(symbol_table)]]), TOP.as_path());
//       r = SExp.to([h(APPLY_ATOM), value, [h(CONS_ATOM), LEFT.as_path(), new_args]]);
//       return r;
//     }
//   }
  
//   throw new SyntaxError(`can't compile ${disassemble(prog)}, unknown operator`);

    return Ok(Reduction(1, allocator.null()));
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
                        macro_lookup = DEFAULT_MACRO_LOOKUP(allocator);
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

    pub fn setup(&mut self, runner: Rc<dyn TRunProgram>) {
        self.runner = runner;
    }
}
