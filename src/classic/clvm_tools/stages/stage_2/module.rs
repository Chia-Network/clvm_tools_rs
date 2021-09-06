// import {Bytes, KEYWORD_TO_ATOM, SExp, str, t, Tuple, b, isAtom, h} from "clvm";
// import * as binutils from "../../clvm_tools/binutils";
// import {build_symbol_dump} from "../../clvm_tools/debug";
// import {LEFT, NodePath, RIGHT, TOP} from "../../clvm_tools/NodePath";
// import {evaluate, quote} from "./helpers";
// import {optimize_sexp} from "./optimize";
// import {TRunProgram} from "../stage_0";

// export const QUOTE_ATOM = KEYWORD_TO_ATOM["q"];
// export const CONS_ATOM = KEYWORD_TO_ATOM["c"];

// export const MAIN_NAME = "";

// export type TBuildTree = Bytes | Tuple<TBuildTree, TBuildTree> | [];
// export function build_tree(items: str[]): TBuildTree {
//   // This function takes a Python list of items and turns it into a binary tree
//   // of the items, suitable for casting to an s-expression.
//   const size = items.length;
//   if(size === 0){
//     return [];
//   }
//   else if(size === 1){
//     return h(items[0]); // items[0] is expected to be a hex string representing constant name atom
//   }
//   const half_size = size >> 1;
//   const left = build_tree(items.slice(0, half_size));
//   const right = build_tree(items.slice(half_size));
//   return t(left, right);
// }

// export type TBuildTreeProgram = SExp | [Bytes, TBuildTree, TBuildTree] | [Tuple<Bytes, SExp>];
// export function build_tree_program(items: SExp[]): TBuildTreeProgram {
//   // This function takes a Python list of items and turns it into a program that
//   //  a binary tree of the items, suitable for casting to an s-expression.
//   const size = items.length;
//   if(size === 0){
//     return [quote([])] as [Tuple<Bytes, SExp>];
//   }
//   else if(size === 1){
//     return items[0];
//   }
//   const half_size = size >> 1;
//   const left = build_tree_program(items.slice(0, half_size));
//   const right = build_tree_program(items.slice(half_size));
//   return [h(CONS_ATOM), left, right] as [Bytes, TBuildTree, TBuildTree];
// }

// export function flatten(sexp: SExp): Bytes[] {
//   // Return a (python) list of every atom.
//   if(sexp.listp()){
//     let r: Bytes[] = [];
//     r = r.concat(flatten(sexp.first()));
//     r = r.concat(flatten(sexp.rest()));
//     return r;
//   }
//   return [sexp.atom as Bytes];
// }

// export type TNameToSExp = Record<str, SExp>;

// /**
//  * @return Used constants name array in `hex string` format.
//  */
// export function build_used_constants_names(functions: TNameToSExp, constants: TNameToSExp, macros: SExp[]){
//   /*
//     Do a naïve pruning of unused symbols. It may be too big, but it shouldn't
//     be too small. Return a list of all atoms used that are also the names of
//     functions or constants, starting with the MAIN_NAME function.
//    */
//   const macro_as_dict = macros.reduce((acc, _) => {
//     acc[(_.rest().first().atom as Bytes).hex()] = _;
//     return acc;
//   }, {} as Record<str, SExp>);
  
//   const possible_symbols = new Set(Object.keys(functions));
//   Object.keys(constants).forEach(c => possible_symbols.add(c));
  
//   let new_names = new Set<str>([MAIN_NAME]);
//   const used_names = new Set<str>(new_names);
//   while(new_names.size){
//     const prior_new_names = new Set(new_names);
//     new_names = new Set();
//     for(const _ of prior_new_names){
//       for(const k of [functions, macro_as_dict]){
//         if(_ in k){
//           flatten(k[_]).forEach(atom => new_names.add(atom.hex()));
//         }
//       }
//     }
//     // new_names.difference_update(used_names)
//     used_names.forEach(n => new_names.delete(n));
//     // used_names.update(new_names)
//     new_names.forEach(n => used_names.add(n));
//   }
//   // used_names.intersection_update(possible_symbols)
//   const used_name_list: str[] = [];
//   used_names.forEach(n => {
//     if(possible_symbols.has(n) && n !== MAIN_NAME){
//       used_name_list.push(n);
//     }
//   });
  
//   used_name_list.sort();
//   return used_name_list;
// }

// export function parse_include(
//   name: SExp,
//   namespace: Set<str>,
//   functions: TNameToSExp,
//   constants: TNameToSExp,
//   macros: SExp[],
//   run_program: TRunProgram,
// ){
//   const prog = binutils.assemble("(_read (_full_path_for_name 1))");
//   const assembled_sexp = run_program(prog, name)[1];
//   for(const sexp of assembled_sexp.as_iter()){
//     parse_mod_sexp(sexp, namespace, functions, constants, macros, run_program);
//   }
// }

// export function unquote_args(code: SExp, args: Bytes[]): SExp {
//   if(code.listp()){
//     const c1 = code.first();
//     const c2 = code.rest();
//     return unquote_args(c1, args).cons(unquote_args(c2, args));
//   }
  
//   if(isAtom(code) && args.some(arg => arg.equal_to(code.atom))){
//     return SExp.to([b("unquote"), code]);
//   }
  
//   return code;
// }


// export function defun_inline_to_macro(declaration_sexp: SExp){
//   const d2 = declaration_sexp.rest();
//   const d3 = d2.rest();
//   const r = [b("defmacro"), d2.first(), d3.first()];
//   const code = d3.rest().first();
//   const args = flatten(d3.first()).filter(_ => !_.equal_to(Bytes.NULL));
//   const unquoted_code = unquote_args(code, args);
//   const r2 = [...r, [b("qq"), unquoted_code]];
//   return SExp.to(r2);
// }

// export function parse_mod_sexp(
//   declaration_sexp: SExp,
//   namespace: Set<str>,
//   functions: TNameToSExp,
//   constants: TNameToSExp,
//   macros: SExp[],
//   run_program: TRunProgram,
// ){
//   const op = declaration_sexp.first().atom as Bytes;
//   const name = declaration_sexp.rest().first();
  
//   if(op.equal_to(b("include"))){
//     parse_include(name, namespace, functions, constants, macros, run_program);
//     return;
//   }
  
//   const name_atom = name.atom as Bytes;
//   if(namespace.has(name_atom.hex())){
//     throw new SyntaxError(`symbol "${name_atom.decode()}" redefined`);
//   }
//   namespace.add(name_atom.hex());
  
//   if(op.equal_to(b("defmacro"))){
//     macros.push(declaration_sexp);
//   }
//   else if(op.equal_to(b("defun"))){
//     functions[name_atom.hex()] = declaration_sexp.rest().rest();
//   }
//   else if(op.equal_to(b("defun-inline"))){
//     macros.push(defun_inline_to_macro(declaration_sexp));
//   }
//   else if(op.equal_to(b("defconstant"))){
//     constants[name_atom.hex()] = SExp.to(quote(declaration_sexp.rest().rest().first()));
//   }
//   else{
//     throw new SyntaxError("expected defun, defmacro, or defconstant");
//   }
// }

// export function compile_mod_stage_1(args: SExp, run_program: TRunProgram){
//   // stage 1: collect up names of globals (functions, constants, macros)
  
//   const functions: TNameToSExp = {};
//   const constants: TNameToSExp = {};
//   const macros: SExp[] = [];
//   const main_local_arguments = args.first();
  
//   const namespace = new Set<str>();
//   // eslint-disable-next-line no-constant-condition
//   while (true){
//     args = args.rest();
//     if(args.rest().nullp()){
//       break;
//     }
//     parse_mod_sexp(args.first(), namespace, functions, constants, macros, run_program);
//   }
  
//   const uncompiled_main = args.first();
//   functions[MAIN_NAME] = SExp.to([main_local_arguments, uncompiled_main]);
  
//   return [functions, constants, macros] as [TNameToSExp, TNameToSExp, SExp[]];
// }

// export type TSymbolTable = Array<[SExp, Bytes]>;
// export function symbol_table_for_tree(tree: SExp, root_node: NodePath): TSymbolTable {
//   if(tree.nullp()){
//     return [];
//   }
//   else if(!tree.listp()){
//     return [[tree, root_node.as_path()]];
//   }
  
//   const left = symbol_table_for_tree(tree.first(), root_node.add(LEFT));
//   const right = symbol_table_for_tree(tree.rest(), root_node.add(RIGHT));
  
//   return left.concat(right);
// }

// export function build_macro_lookup_program(macro_lookup: SExp, macros: SExp[], run_program: TRunProgram){
//   let macro_lookup_program = SExp.to(quote(macro_lookup));
//   for(const macro of macros){
//     macro_lookup_program = evaluate(SExp.to(
//       [b("opt"), [b("com"), quote([h(CONS_ATOM), macro, macro_lookup_program]), macro_lookup_program]]),
//     TOP.as_path(),
//     );
//     macro_lookup_program = optimize_sexp(macro_lookup_program, run_program);
//   }
//   return macro_lookup_program;
// }

// export function compile_functions(
//   functions: TNameToSExp,
//   macro_lookup_program: SExp,
//   constants_symbol_table: Array<[SExp, Bytes]>,
//   args_root_node: NodePath,
// ){
//   const compiled_functions: Record<str, SExp> = {};
//   for(const [name, lambda_expression] of Object.entries(functions)){
//     const local_symbol_table = symbol_table_for_tree(lambda_expression.first(), args_root_node);
//     const all_symbols = local_symbol_table.concat(constants_symbol_table);
//     compiled_functions[name] = SExp.to(
//       [b("opt"), [b("com"),
//         quote(lambda_expression.rest().first()),
//         macro_lookup_program,
//         quote(all_symbols)]]);
//   }
//   return compiled_functions;
// }

// export function compile_mod(args: SExp, macro_lookup: SExp, symbol_table: SExp, run_program: TRunProgram){
//   // Deal with the "mod" keyword.
//   const [functions, constants, macros] = compile_mod_stage_1(args, run_program);
  
//   // move macros into the macro lookup
//   const macro_lookup_program = build_macro_lookup_program(macro_lookup, macros, run_program);
  
//   // get a list of all symbols that are possibly used
//   const all_constants_names = build_used_constants_names(functions, constants, macros);
//   const has_constants_tree = all_constants_names.length > 0;
  
//   // build defuns table, with function names as keys
  
//   const constants_tree = SExp.to(build_tree(all_constants_names));
  
//   const constants_root_node = LEFT;
//   let args_root_node;
//   if(has_constants_tree){
//     args_root_node = RIGHT;
//   }
//   else{
//     args_root_node = TOP;
//   }
  
//   const constants_symbol_table = symbol_table_for_tree(constants_tree, constants_root_node);
  
//   const compiled_functions = compile_functions(
//     functions,
//     macro_lookup_program,
//     constants_symbol_table,
//     args_root_node,
//   );
  
//   const main_path_src = binutils.disassemble(compiled_functions[MAIN_NAME]);
  
//   let main_code;
//   if(has_constants_tree){
//     const all_constants_lookup: typeof compiled_functions = {};
//     Object.entries(compiled_functions).forEach(([k, v]) => {
//       if(all_constants_names.includes(k)){
//         all_constants_lookup[k] = v;
//       }
//     });
//     Object.entries(constants).forEach(([k, v]) => {
//       all_constants_lookup[k] = v;
//     });
    
//     const all_constants_list = all_constants_names.map(_ => all_constants_lookup[_]);
//     const all_constants_tree_program = SExp.to(build_tree_program(all_constants_list));
    
//     const all_constants_tree_src = binutils.disassemble(all_constants_tree_program);
//     const arg_tree_src = `(c ${all_constants_tree_src} 1)`;
//     main_code = `(opt (q . (a ${main_path_src} ${arg_tree_src})))`;
//     build_symbol_dump(all_constants_lookup, run_program, "main.sym");
//   }
//   else{
//     const arg_tree_src = "1";
//     main_code = `(opt (q . (a ${main_path_src} ${arg_tree_src})))`;
//   }
  
//   return binutils.assemble(main_code);
// }
