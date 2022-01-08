// export function ir_as_int(ir_sexp: SExp): int {
//   return int_from_bytes(ir_as_atom(ir_sexp));
// }

// export function ir_offset(ir_sexp: SExp): int {
//   const val = ir_sexp.first();
//   let the_offset;
//   if(val.listp()){
//     the_offset = val.rest().atom;
//   }
//   else{
//     the_offset = h("0xff");
//   }
//   return int_from_bytes(the_offset);
// }

// export function ir_val(ir_sexp: SExp): SExp {
//   return ir_sexp.rest();
// }

// export function ir_nullp(ir_sexp: SExp): bool {
//   return ir_type(ir_sexp) === Type.NULL.i;
// }

// export function ir_listp(ir_sexp: SExp): bool {
//   return CONS_TYPES.includes(ir_type(ir_sexp));
// }

// export function ir_as_sexp(ir_sexp: SExp): SExp|[] {
//   if(ir_nullp(ir_sexp)){
//     return [];
//   }
//   else if(ir_type(ir_sexp) === Type.CONS.i){
//     return (ir_as_sexp(ir_first(ir_sexp)) as SExp).cons(ir_as_sexp(ir_rest(ir_sexp)));
//   }
//   return ir_sexp.rest();
// }

// export function ir_is_atom(ir_sexp: SExp): bool {
//   return !ir_listp(ir_sexp);
// }

// export function ir_as_atom(ir_sexp: SExp): Bytes {
//   return Bytes.from(ir_sexp.rest().atom);
// }

// export function ir_first(ir_sexp: SExp): SExp {
//   return ir_sexp.rest().first();
// }

// export function ir_rest(ir_sexp: SExp): SExp {
//   return ir_sexp.rest().rest();
// }

// export function ir_as_symbol(ir_sexp: SExp): Optional<str> {
//   if(ir_sexp.listp() && ir_type(ir_sexp) === Type.SYMBOL.i){
//     const b = Bytes.from((ir_as_sexp(ir_sexp) as SExp).atom);
//     return b.decode();
//   }
//   return None;
// }

// export function* ir_iter(ir_sexp: SExp){
//   while(ir_listp(ir_sexp)){
//     yield ir_first(ir_sexp);
//     ir_sexp = ir_rest(ir_sexp);
//   }
// }

// export function is_ir(sexp: SExp): bool {
//   if(sexp.atom !== None){
//     return false;
//   }

//   const [type_sexp, val_sexp] = sexp.pair as Tuple<SExp, SExp>;
//   const f = type_sexp.atom;
//   if(f === None || f.length > 1){
//     return false;
//   }

//   const the_type = int_from_bytes(f);
//   let t;
//   try{
//     t = new Type(the_type);
//   }
//   catch (e){
//     return false;
//   }

//   if(t.is(Type.CONS)){
//     if(val_sexp.atom.equal_to(Bytes.NULL)){
//       return true;
//     }
//     if(val_sexp.pair){
//       return val_sexp.every((_: SExp) => is_ir(_));
//     }
//     return false;
//   }

//   return val_sexp.atom !== None;
// }
