// import {b, Bytes, int, int_from_bytes, int_to_bytes, limbs_for_int} from "clvm";


// function i(b: Bytes){
//   return int_from_bytes(b);
// }

// const types = {
//   CONS: i(b("CONS")),
//   NULL: i(b("NULL")),
//   INT: i(b("INT")),
//   HEX: i(b("HEX")),
//   QUOTES: i(b("QT")),
//   DOUBLE_QUOTE: i(b("DQT")),
//   SINGLE_QUOTE: i(b("SQT")),
//   SYMBOL: i(b("SYM")),
//   OPERATOR: i(b("OP")),
//   CODE: i(b("CODE")),
//   NODE: i(b("NODE")),
// };

// function isValidType(i: int){
//   return Object.values(types).includes(i);
// }

// export class Type {
//   static CONS = new Type(types.CONS);
//   static NULL = new Type(types.NULL);
//   static INT = new Type(types.INT);
//   static HEX = new Type(types.HEX);
//   static QUOTES = new Type(types.QUOTES);
//   static DOUBLE_QUOTE = new Type(types.DOUBLE_QUOTE);
//   static SINGLE_QUOTE = new Type(types.SINGLE_QUOTE);
//   static SYMBOL = new Type(types.SYMBOL);
//   static OPERATOR = new Type(types.OPERATOR);
//   static CODE = new Type(types.CODE);
//   static NODE = new Type(types.NODE);
  
//   private readonly _i: number;
//   public get i(){
//     return this._i;
//   }
  
//   public get length(){
//     return limbs_for_int(this.i);
//   }
  
//   public get atom(){
//     return int_to_bytes(this.i);
//   }
  
//   public constructor(i: int|Type) {
//     if(typeof i === "number"){
//       if(!isValidType(i)){
//         throw new Error(`${i} is not a valid Type`);
//       }
//       this._i = i;
//     }
//     else{
//       this._i = i.i;
//     }
//   }
  
//   public is(other: Type){
//     return this._i === other.i;
//   }
  
//   public listp(){
//     return false;
//   }
// }

// export const CONS_TYPES = [Type.CONS.i];
