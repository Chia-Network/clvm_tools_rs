use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use clvm_rs::allocator::{Allocator, NodePtr, SExp};
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm::sexp::{enlist, first, flatten, foldM, mapM, non_nil, proper_list, rest};
use crate::classic::clvm_tools::debug::build_symbol_dump;
use crate::classic::clvm_tools::stages::assemble;
use crate::classic::clvm_tools::stages::stage_0::TRunProgram;
use crate::classic::clvm_tools::stages::stage_2::helpers::{evaluate, quote};
use crate::classic::clvm_tools::stages::stage_2::inline::{
    formulate_path_selections_for_destructuring, is_at_capture, is_inline_destructure,
};
use crate::classic::clvm_tools::stages::stage_2::optimize::optimize_sexp;
use crate::classic::clvm_tools::NodePath::NodePath;

lazy_static! {
    pub static ref MAIN_NAME: String = "".to_string();
}

struct CollectionResult {
    pub functions: HashMap<Vec<u8>, NodePtr>,
    pub constants: HashMap<Vec<u8>, NodePtr>,
    pub macros: Vec<(Vec<u8>, NodePtr)>,
}

// export type TBuildTree = Bytes | Tuple<TBuildTree, TBuildTree> | [];
fn build_tree(allocator: &mut Allocator, items: &Vec<Vec<u8>>) -> Result<NodePtr, EvalErr> {
    if items.len() == 0 {
        Ok(allocator.null())
    } else if items.len() == 1 {
        allocator.new_atom(&items[0])
    } else {
        m! {
            let half_size = items.len() >> 1;
            left <- build_tree(allocator, &items[..half_size].to_vec());
            right <- build_tree(allocator, &items[half_size..].to_vec());
            allocator.new_pair(left, right)
        }
    }
}

// export type TBuildTreeProgram = SExp | [Bytes, TBuildTree, TBuildTree] | [Tuple<Bytes, SExp>];
fn build_tree_program(allocator: &mut Allocator, items: &Vec<NodePtr>) -> Result<NodePtr, EvalErr> {
    // This function takes a Python list of items and turns it into a program that
    //  a binary tree of the items, suitable for casting to an s-expression.
    let size = items.len();
    if size == 0 {
        m! {
            list_of_nil <- enlist(allocator, &vec!(allocator.null()));
            quote(allocator, list_of_nil)
        }
    } else if size == 1 {
        Ok(items[0])
    } else {
        m! {
            let half_size = items.len() >> 1;
            left <-
                build_tree_program(allocator, &items[..half_size].to_vec());
            right <-
                build_tree_program(allocator, &items[half_size..].to_vec());

            cons_atom <- allocator.new_atom(&vec!(4 as u8));
            enlist(allocator, &vec!(cons_atom, left, right))
        }
    }
}

/**
 * @return Used constants name array in `hex string` format.
 */
fn build_used_constants_names(
    allocator: &mut Allocator,
    functions: &HashMap<Vec<u8>, NodePtr>,
    constants: &HashMap<Vec<u8>, NodePtr>,
    macros: &Vec<(Vec<u8>, NodePtr)>,
) -> Result<Vec<Vec<u8>>, EvalErr> {
    /*
    Do a naïve pruning of unused symbols. It may be too big, but it shouldn't
    be too small. Return a list of all atoms used that are also the names of
    functions or constants, starting with the MAIN_NAME function.
     */
    let mut macro_as_dict = HashMap::new();

    for nv in macros {
        let (name, value) = nv;
        macro_as_dict.insert(name.to_vec(), *value);
    }

    let mut possible_symbols = HashSet::new();
    let _ = for key in functions.keys() {
        possible_symbols.insert(key);
    };

    let _ = for key in constants.keys() {
        possible_symbols.insert(key);
    };

    let mut new_names: HashSet<Vec<u8>> = HashSet::new();
    new_names.insert(MAIN_NAME.as_bytes().to_vec());
    let mut used_names = new_names.clone();

    let _ = while new_names.len() > 0 {
        let iterate_names = new_names.clone();
        new_names = HashSet::new();

        for name in iterate_names {
            let functions_and_macros = vec![functions.get(&name), macro_as_dict.get(&name)];

            let matching_names_1 = functions_and_macros
                .iter()
                .map(|v| {
                    v.map(|v| {
                        let mut res = Vec::new();
                        flatten(allocator, *v, &mut res);
                        res
                    })
                    .unwrap_or_else(|| Vec::new())
                })
                .flatten()
                .collect::<Vec<NodePtr>>();

            let matching_names = matching_names_1
                .iter()
                .map(|v| match allocator.sexp(*v) {
                    SExp::Atom(b) => Some(allocator.buf(&b).to_vec()),
                    _ => None,
                })
                .flatten();

            for name in matching_names {
                if !used_names.contains(&name) {
                    used_names.insert(name.to_vec());
                    new_names.insert(name);
                }
            }
        }
    };

    // used_names.intersection_update(possible_symbols)
    let mut used_name_list: Vec<Vec<u8>> = Vec::new();
    for name in used_names.iter() {
        if possible_symbols.contains(name) && *name != MAIN_NAME.as_bytes() {
            used_name_list.push(name.to_vec());
        }
    }

    used_name_list.sort();
    Ok(used_name_list)
}

fn parse_include(
    allocator: &mut Allocator,
    name: NodePtr,
    namespace: &mut HashSet<Vec<u8>>,
    functions: &mut HashMap<Vec<u8>, NodePtr>,
    constants: &mut HashMap<Vec<u8>, NodePtr>,
    macros: &mut Vec<(Vec<u8>, NodePtr)>,
    run_program: Rc<dyn TRunProgram>,
) -> Result<(), EvalErr> {
    return m! {
        prog <- assemble(
            allocator,
            &"(_read (_full_path_for_name 1))".to_string()
        );
        assembled_sexp <- run_program.run_program(
            allocator,
            prog,
            name,
            None
        );
        match proper_list(allocator, assembled_sexp.1, true) {
            None => { Err(EvalErr(name, "include returned malformed result".to_string())) },
            Some(assembled) => {
                for sexp in assembled {
                    match parse_mod_sexp(
                        allocator,
                        sexp,
                        namespace,
                        functions,
                        constants,
                        macros,
                        run_program.clone()
                    ) {
                        Err(e) => { return Err(e); },
                        Ok(_) => { }
                    }
                };
                Ok(())
            }
        }
    };
}

fn unquote_args(
    allocator: &mut Allocator,
    code: NodePtr,
    args: &Vec<Vec<u8>>,
    matches: &HashMap<Vec<u8>, NodePtr>,
) -> Result<NodePtr, EvalErr> {
    match allocator.sexp(code) {
        SExp::Atom(code_buf) => {
            let code_atom = allocator.buf(&code_buf);
            let matching_args = args
                .iter()
                .filter(|arg| *arg == code_atom)
                .map(|v| v.clone())
                .collect::<Vec<Vec<u8>>>();
            if matching_args.len() > 0 {
                if let Some(argval) = matches.get(&matching_args[0]) {
                    // New case: if we've been given an alternate way of computing
                    // the argument, use it here.
                    return Ok(*argval);
                }

                let unquote_atom = allocator.new_atom("unquote".as_bytes())?;
                return enlist(allocator, &vec![unquote_atom, code]);
            }

            Ok(code)
        }
        SExp::Pair(c1, c2) => {
            m! {
                unquoted_c2 <- unquote_args(allocator, c2, args, matches);
                unquoted_c1 <- unquote_args(allocator, c1, args, matches);
                allocator.new_pair(unquoted_c1, unquoted_c2)
            }
        }
    }
}

fn defun_inline_to_macro(
    allocator: &mut Allocator,
    declaration_sexp: NodePtr,
) -> Result<NodePtr, EvalErr> {
    let d2 = rest(allocator, declaration_sexp)?;
    let d3 = rest(allocator, d2)?;
    let defmacro_atom = allocator.new_atom("defmacro".as_bytes())?;
    let d2_first = first(allocator, d2)?;
    let d3_first = first(allocator, d3)?;

    let mut destructure_matches = HashMap::new();
    let mut use_args = d3_first;

    if is_inline_destructure(allocator, d3_first) {
        // Given an attempt to destructure via the argument list, we need
        // to ensure that the inline function receives arguments that are
        // relative to the _values_ given rather than the code given to
        // generate the arguments.  These overlap when the argument list is
        // a single level proper list, but not otherwise.
        use_args = formulate_path_selections_for_destructuring(
            allocator,
            d3_first,
            &mut destructure_matches,
        )?;
    }

    let mut r_vec = vec![defmacro_atom, d2_first, use_args];
    let code_rest = rest(allocator, d3)?;
    let code = first(allocator, code_rest)?;

    let mut arg_atom_list = Vec::new();
    let _ = flatten(allocator, use_args, &mut arg_atom_list);
    let arg_name_list = arg_atom_list
        .iter()
        .map(|x| match allocator.sexp(*x) {
            SExp::Atom(a) => Some(allocator.buf(&a)),
            _ => None,
        })
        .flatten()
        .filter(|x| x.len() > 0)
        .map(|v| v.to_vec())
        .collect::<Vec<Vec<u8>>>();

    let unquoted_code = unquote_args(allocator, code, &arg_name_list, &destructure_matches)?;
    let qq_atom = allocator.new_atom("qq".as_bytes())?;
    let qq_list = enlist(allocator, &vec![qq_atom, unquoted_code])?;
    r_vec.push(qq_list);
    let res = enlist(allocator, &r_vec)?;
    Ok(res)
}

fn parse_mod_sexp(
    allocator: &mut Allocator,
    declaration_sexp: NodePtr,
    namespace: &mut HashSet<Vec<u8>>,
    functions: &mut HashMap<Vec<u8>, NodePtr>,
    constants: &mut HashMap<Vec<u8>, NodePtr>,
    macros: &mut Vec<(Vec<u8>, NodePtr)>,
    run_program: Rc<dyn TRunProgram>,
) -> Result<(), EvalErr> {
    return m! {
        op_node <- first(allocator, declaration_sexp);
        dec_rest <- rest(allocator, declaration_sexp);
        name_node <- first(allocator, dec_rest);
        let op =
            match allocator.sexp(op_node) {
                SExp::Atom(b) => allocator.buf(&b).to_vec(),
                _ => Vec::new()
            };
        let name =
            match allocator.sexp(name_node) {
                SExp::Atom(b) => allocator.buf(&b).to_vec(),
                _ => Vec::new()
            };

        if op == "include".as_bytes() {
            parse_include(
                allocator,
                name_node,
                namespace,
                functions,
                constants,
                macros,
                run_program.clone()
            )
        } else if namespace.contains(&name) {
            Err(EvalErr(declaration_sexp, format!("symbol \"{}\" redefined", Bytes::new(Some(BytesFromType::Raw(name))).decode())))
        } else {
            namespace.insert(name.to_vec());

            if op == "defmacro".as_bytes() {
                macros.push((name.to_vec(), declaration_sexp));
                Ok(())
            } else if op == "defun".as_bytes() {
                m! {
                    declaration_sexp_r <- rest(allocator, declaration_sexp);
                    declaration_sexp_rr <- rest(allocator, declaration_sexp_r);
                    let _ = functions.insert(name, declaration_sexp_rr);
                    Ok(())
                }
            } else if op == "defun-inline".as_bytes() {
                m! {
                    defined_macro <-
                        defun_inline_to_macro(allocator, declaration_sexp);
                    let _ = macros.push((name, defined_macro));
                    Ok(())
                }
            } else if op == "defconstant".as_bytes() {
                m! {
                    r_of_declaration <- rest(allocator, declaration_sexp);
                    rr_of_declaration <- rest(allocator, r_of_declaration);
                    frr_of_declaration <- first(allocator, rr_of_declaration);
                    quoted_decl <- quote(allocator, frr_of_declaration);
                    let _ = constants.insert(name, quoted_decl);
                    Ok(())
                }
            } else {
                Err(EvalErr(declaration_sexp, "expected defun, defmacro, or defconstant".to_string()))
            }
        }
    };
}

fn compile_mod_stage_1(
    allocator: &mut Allocator,
    args: NodePtr,
    run_program: Rc<dyn TRunProgram>,
) -> Result<CollectionResult, EvalErr> {
    // stage 1: collect up names of globals (functions, constants, macros)
    m! {
        let mut functions = HashMap::new();
        let mut constants = HashMap::new();
        let mut macros = Vec::new();
        let mut namespace = HashSet::new();

        // eslint-disable-next-line no-constant-condition
        match proper_list(allocator, args, true) {
            None => { Err(EvalErr(args, "miscompiled mod is not a proper list\n".to_string())) },
            Some(alist) => {
                if alist.len() == 0 {
                    return Err(EvalErr(args, "miscompiled mod is 0 size\n".to_string()));
                }

                let main_local_arguments = alist[0];

                for i in 1..alist.len()-1 {
                    match parse_mod_sexp(
                        allocator,
                        alist[i],
                        &mut namespace,
                        &mut functions,
                        &mut constants,
                        &mut macros,
                        run_program.clone()
                    ) {
                        Err(e) => { return Err(e); },
                        Ok(_) => { }
                    }
                }

                let uncompiled_main = alist[alist.len() - 1];
                m! {
                    main_list <-
                        enlist(
                            allocator,
                            &vec!(main_local_arguments, uncompiled_main)
                        );

                    let _ = functions.insert(MAIN_NAME.as_bytes().to_vec(), main_list);
                    Ok(CollectionResult {
                        functions,
                        constants,
                        macros
                    })
                }
            }
        }
    }
}

// export type TSymbolTable = Array<[SExp, Bytes]>;

fn symbol_table_for_tree(
    allocator: &mut Allocator,
    tree: NodePtr,
    root_node: &NodePath,
) -> Result<Vec<(NodePtr, Vec<u8>)>, EvalErr> {
    if !non_nil(allocator, tree) {
        return Ok(Vec::new());
    }

    match allocator.sexp(tree) {
        SExp::Atom(_) => {
            return Ok(vec![(tree, root_node.as_path().data().to_vec())]);
        }
        SExp::Pair(_, _) => {
            let left_bytes = NodePath::new(None).first();
            let right_bytes = NodePath::new(None).rest();

            let tree_first = first(allocator, tree)?;
            let tree_rest = rest(allocator, tree)?;

            // Allow haskell-like @ capture for destructuring.
            // If we encounter a form like (@ name substructure) then
            // treat it as though name captures the current path but
            // we also continue evaluating at the current position.
            let mut result_fin = Vec::new();
            if let Some((capture, destructure)) = is_at_capture(allocator, tree_first, tree_rest) {
                // Push the given name here.
                result_fin.push((capture, root_node.as_path().data().to_vec()));

                let mut substructure = symbol_table_for_tree(allocator, destructure, root_node)?;

                result_fin.append(&mut substructure);
            } else {
                let mut left =
                    symbol_table_for_tree(allocator, tree_first, &root_node.add(left_bytes))?;
                let mut right =
                    symbol_table_for_tree(allocator, tree_rest, &root_node.add(right_bytes))?;

                result_fin.append(&mut left);
                result_fin.append(&mut right);
            }

            Ok(result_fin)
        }
    }
}

fn build_macro_lookup_program(
    allocator: &mut Allocator,
    macro_lookup: NodePtr,
    macros: &Vec<(Vec<u8>, NodePtr)>,
    run_program: Rc<dyn TRunProgram>,
) -> Result<NodePtr, EvalErr> {
    return m! {
        com_atom <- allocator.new_atom("com".as_bytes());
        cons_atom <- allocator.new_atom(&vec!(4));
        opt_atom <- allocator.new_atom("opt".as_bytes());

        let runner = || run_program.clone();
        macro_lookup_program <- quote(allocator, macro_lookup);
        result_program <- foldM(
            allocator,
            &|allocator, macro_lookup_program, macro_def: &(Vec<u8>, NodePtr)| m! {
                cons_list <-
                    enlist(
                        allocator,
                        &vec!(cons_atom, macro_def.1, macro_lookup_program)
                    );
                quoted_to_compile <- quote(allocator, cons_list);
                compile_form <-
                    enlist(
                        allocator,
                        &vec!(com_atom, quoted_to_compile, macro_lookup_program)
                    );
                opt_form <- enlist(allocator, &vec!(opt_atom, compile_form));
                top_atom <- allocator.new_atom(NodePath::new(None).as_path().data());
                macro_evaluated <- evaluate(allocator, opt_form, top_atom);
                optimize_sexp(allocator, macro_evaluated, runner())
            },
            macro_lookup_program,
            &mut macros.iter()
        );
        Ok(result_program)
    };
}

fn add_one_function(
    allocator: &mut Allocator,
    args_root_node: &NodePath,
    macro_lookup_program: NodePtr,
    constants_symbol_table: &Vec<(NodePtr, Vec<u8>)>,
    compiled_functions_: HashMap<Vec<u8>, NodePtr>,
    name: &Vec<u8>,
    lambda_expression: NodePtr,
) -> Result<HashMap<Vec<u8>, NodePtr>, EvalErr> {
    let mut compiled_functions = compiled_functions_;
    return m! {
        com_atom <- allocator.new_atom("com".as_bytes());
        opt_atom <- allocator.new_atom("opt".as_bytes());

        le_first <- first(allocator, lambda_expression);
        local_symbol_table <- symbol_table_for_tree(
            allocator, le_first, args_root_node
        );
        let mut all_symbols = local_symbol_table.clone();
        let _ = all_symbols.append(&mut constants_symbol_table.clone());
        lambda_form_content <- rest(allocator, lambda_expression);
        lambda_body <- first(allocator, lambda_form_content);
        quoted_lambda_expr <- quote(allocator, lambda_body);
        all_symbols_list_sexp <-
            mapM(
                allocator,
                &mut all_symbols.iter(),
                &|allocator, pair| m! {
                    path_atom <- allocator.new_atom(&pair.1);
                    enlist(allocator, &vec!(pair.0, path_atom))
                }
            );

        all_symbols_list <-
            enlist(allocator, &all_symbols_list_sexp);

        quoted_symbols <- quote(allocator, all_symbols_list);
        com_list <- enlist(
            allocator,
            &vec!(
                com_atom,
                quoted_lambda_expr,
                macro_lookup_program,
                quoted_symbols
            )
        );
        opt_list <- enlist(allocator, &vec!(opt_atom, com_list));
        let _ = compiled_functions.insert(name.to_vec(), opt_list);
        Ok(compiled_functions)
    };
}

fn compile_functions(
    allocator: &mut Allocator,
    functions: &HashMap<Vec<u8>, NodePtr>,
    macro_lookup_program: NodePtr,
    constants_symbol_table: &Vec<(NodePtr, Vec<u8>)>,
    args_root_node: &NodePath,
) -> Result<HashMap<Vec<u8>, NodePtr>, EvalErr> {
    let compiled_functions = HashMap::new();

    return foldM(
        allocator,
        &|allocator: &mut Allocator, compiled_functions, name_exp: (&Vec<u8>, &NodePtr)| {
            add_one_function(
                allocator,
                args_root_node,
                macro_lookup_program,
                constants_symbol_table,
                compiled_functions,
                name_exp.0,
                *name_exp.1,
            )
        },
        compiled_functions,
        &mut functions.iter(),
    );
}

pub fn compile_mod(
    allocator: &mut Allocator,
    args: NodePtr,
    macro_lookup: NodePtr,
    _symbol_table: NodePtr,
    run_program: Rc<dyn TRunProgram>,
    _level: usize,
) -> Result<NodePtr, EvalErr> {
    // Deal with the "mod" keyword.
    return m! {
        cr <- compile_mod_stage_1(allocator, args, run_program.clone());
        a_atom <- allocator.new_atom(&vec!(2));
        cons_atom <- allocator.new_atom(&vec!(4));
        opt_atom <- allocator.new_atom("opt".as_bytes());

        // move macros into the macro lookup
        macro_lookup_program <- build_macro_lookup_program(
            allocator, macro_lookup, &cr.macros, run_program.clone()
        );

        // get a list of all symbols that are possibly used
        all_constants_names <- build_used_constants_names(
            allocator, &cr.functions, &cr.constants, &cr.macros
        );

        let has_constants_tree = all_constants_names.len() > 0;
        // build defuns table, with function names as keys

        constants_tree <- build_tree(allocator, &all_constants_names);

        let constants_root_node = NodePath::new(None).first();
        let args_root_node =
            if has_constants_tree {
                NodePath::new(None).rest()
            } else {
                NodePath::new(None)
            };

        constants_symbol_table <- symbol_table_for_tree(
            allocator, constants_tree, &constants_root_node
        );

        compiled_functions <- compile_functions(
            allocator,
            &cr.functions,
            macro_lookup_program,
            &constants_symbol_table,
            &args_root_node,
        );

        let main_path = compiled_functions[MAIN_NAME.as_bytes()];

        if has_constants_tree {
            m! {
                let mut all_constants_lookup = HashMap::new();
                let _ = {
                    for (k,v) in compiled_functions {
                        if all_constants_names.contains(&k) {
                            all_constants_lookup.insert(k, v);
                        }
                    }
                };
                let _ = {
                    for (k,v) in cr.constants.iter() {
                        all_constants_lookup.insert(k.to_vec(), *v);
                    }
                };

                let all_constants_list =
                    all_constants_names.iter().map(
                        |name| all_constants_lookup.get(name)
                    ).flatten().map(|x| *x).collect::<Vec<NodePtr>>();

                all_constants_tree_program <-
                    build_tree_program(allocator, &all_constants_list);

                top_atom <- allocator.new_atom(NodePath::new(None).as_path().data());
                arg_tree <-
                    enlist(
                        allocator,
                        &vec!(cons_atom, all_constants_tree_program, top_atom)
                    );

                apply_list <-
                    enlist(
                        allocator,
                        &vec!(a_atom, main_path, arg_tree)
                    );
                quoted_apply_list <- quote(allocator, apply_list);
                opt_list <-
                    enlist(
                        allocator,
                        &vec!(opt_atom, quoted_apply_list)
                    );

                symbols <- build_symbol_dump(
                    allocator,
                    all_constants_lookup,
                    run_program.clone()
                );

                to_run <- assemble(
                    allocator,
                    &"(_set_symbol_table 1)".to_string()
                );

                _ <- run_program.run_program(
                    allocator,
                    to_run,
                    symbols,
                    None
                );

                Ok(opt_list)
            }
        } else {
            m! {
                top_atom <- allocator.new_atom(NodePath::new(None).as_path().data());
                apply_list <-
                    enlist(
                        allocator,
                        &vec!(a_atom, main_path, top_atom)
                    );
                quoted_apply_list <- quote(allocator, apply_list);
                enlist(
                    allocator,
                    &vec!(opt_atom, quoted_apply_list)
                )
            }
        }
    };
}
