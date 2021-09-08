use num_bigint::ToBigInt;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    bi_zero,
    bi_one,
    get_u32
};
use crate::classic::clvm::EvalError::EvalError;
use crate::util::Number;

pub struct TConvertOption {
    pub signed: bool
}

pub fn int_from_bytes(b: Bytes, option: Option<TConvertOption>) -> Result<u64, EvalError> {
    if b.length() == 0 {
        return Ok(0);
    }  else if b.length() * 8 > 64 {
        return Err(EvalError::new_str("Cannot convert Bytes to Integer larger than 64bit. Use bigint_from_bytes instead.".to_string()));
    }

    let signed = option.map(|cvt| cvt.signed).unwrap_or_else(|| false);
    let mut unsigned64 : u64 = 0;
    let dv = b.raw();

    let bytes4_remain = dv.len() % 4;
    let bytes4_length = (dv.len() - bytes4_remain) / 4;

    let mut order : u64 = 1;

    if bytes4_length > 0 {
        for i_reverse in 0..bytes4_length {
            let i = bytes4_length - i_reverse - 1;
            let byte32 = get_u32(&dv, i*4 + bytes4_remain) as u64;
            unsigned64 += byte32 * order;
            order = order << 32;
        }
    }

    if bytes4_remain > 0 {
        if bytes4_length == 0 {
            order = 1;
        }
        for i_reverse in 0..bytes4_remain {
            let i = bytes4_remain - i_reverse - 1;
            let byte = dv[i] as u64;
            unsigned64 += byte * order;
            order = order << 8;
        }
    }

    // If the first bit is 1, it is recognized as a negative number.
    if signed && ((dv[0] & 0x80) != 0) {
        return Ok((unsigned64 - 1 << (b.length()*8)) as u64);
    }
    return Ok(unsigned64);
}

pub fn bigint_from_bytes(b: &Bytes, option: Option<TConvertOption>) -> Number {
    if b.length() == 0 {
        return bi_zero();
    }

    let signed = option.map(|cvt| cvt.signed).unwrap_or_else(|| false);
    let mut unsigned = bi_zero();
    let dv = b.raw();

    let bytes4_remain = dv.len() % 4;
    let bytes4_length = (dv.len() - bytes4_remain) / 4;

    let mut order = bi_one();

    if bytes4_length > 0 {
        for i_reverse in 0..bytes4_length {
            let i = bytes4_length - i_reverse - 1;
            let byte32 = get_u32(&dv, i*4 + bytes4_remain);
            unsigned += byte32.to_bigint().unwrap() * order.clone();
            order <<= 32;
        }
    }

    if bytes4_remain > 0 {
        if bytes4_length == 0 {
            order = bi_one();
        }
        for i_reverse in 0..bytes4_remain {
            let i = bytes4_remain - i_reverse - 1;
            let byte = dv[i];
            unsigned += byte.to_bigint().unwrap() * order.clone();
            order <<= 8;
        }
    }

    // If the first bit is 1, it is recognized as a negative number.
    if signed && ((dv[0] & 0x80) != 0) {
        return unsigned - (bi_one() << (b.length()*8));
    }
    return unsigned;
}

// export function int_to_bytes(v: number, option?: Partial<TConvertOption>): Bytes {
//   if(v > Number.MAX_SAFE_INTEGER || v < Number.MIN_SAFE_INTEGER){
//     throw new Error(`The int value is beyond ${v > 0 ? "MAX_SAFE_INTEGER" : "MIN_SAFE_INTEGER"}: ${v}`);
//   }
//   if(v === 0){
//     return Bytes.NULL;
//   }
  
//   const signed = (option && typeof option.signed === "boolean") ? option.signed : false;
//   if(!signed && v < 0){
//     throw new Error("OverflowError: can't convert negative int to unsigned");
//   }
  
//   let byte_count = 1;
//   const div = signed ? 1 : 0;
//   const b16 = 65536;
//   if(v > 0){
//     let right_hand = (v + 1) * (div + 1);
//     while((b16 ** ((byte_count-1)/2 + 1)) < right_hand){
//       byte_count += 2;
//     }
//     right_hand = (v + 1) * (div + 1);
//     while (2 ** (8 * byte_count) < right_hand) {
//       byte_count++;
//     }
//   }
//   else if(v < 0){
//     let right_hand = (-v + 1) * (div + 1);
//     while((b16 ** ((byte_count-1)/2 + 1)) < right_hand){
//       byte_count += 2;
//     }
//     right_hand = -v * 2;
//     while (2 ** (8 * byte_count) < right_hand) {
//       byte_count++;
//     }
//   }
  
//   const extraByte = signed && v > 0 && ((v >> ((byte_count-1)*8)) & 0x80) > 0 ? 1 : 0;
//   const u8 = new Uint8Array(byte_count + extraByte);
//   for(let i=0;i<byte_count;i++){
//     const j = extraByte ? i+1 : i;
//     u8[j] = (v >> (byte_count-i-1)*8) & 0xff;
//   }
  
//   return new Bytes(u8);
// }

// export function bigint_to_bytes(v: bigint, option?: Partial<TConvertOption>): Bytes {
//   if(v === BigInt(0)){
//     return Bytes.NULL;
//   }
  
//   const signed = (option && typeof option.signed === "boolean") ? option.signed : false;
//   if(!signed && v < BigInt(0)){
//     throw new Error("OverflowError: can't convert negative int to unsigned");
//   }
//   let byte_count = 1;
//   const div = BigInt(signed ? 1 : 0);
//   const b32 = BigInt(4294967296);
//   if(v > 0){
//     let right_hand = (v + BigInt(1)) * (div + BigInt(1));
//     while((b32 ** BigInt((byte_count-1)/4 + 1)) < right_hand){
//       byte_count += 4;
//     }
//     right_hand = (v + BigInt(1)) * (div + BigInt(1));
//     while (BigInt(2) ** (BigInt(8) * BigInt(byte_count)) < right_hand) {
//       byte_count++;
//     }
//   }
//   else if(v < 0){
//     let right_hand = (-v + BigInt(1)) * (div + BigInt(1));
//     while((b32 ** BigInt((byte_count-1)/4 + 1)) < right_hand){
//       byte_count += 4;
//     }
//     right_hand = -v * BigInt(2);
//     while (BigInt(2) ** (BigInt(8) * BigInt(byte_count)) < right_hand) {
//       byte_count++;
//     }
//   }
  
//   const extraByte = (signed && v > 0 && ((v >> (BigInt(byte_count-1)*BigInt(8))) & BigInt(0x80)) > BigInt(0)) ? 1 : 0;
//   const total_bytes = byte_count + extraByte;
//   const u8 = new Uint8Array(total_bytes);
//   const dv = new DataView(u8.buffer);
//   const byte4Remain = byte_count % 4;
//   const byte4Length = (byte_count - byte4Remain) / 4;
  
//   let bitmask = BigInt(0xffffffff);
//   for(let i=0;i<byte4Length;i++){
//     const num = Number((v >> BigInt(32)*BigInt(i)) & bitmask);
//     const pointer = extraByte + byte4Remain + (byte4Length-1 - i)*4;
//     dv.setUint32(pointer, num);
//   }
//   v >>= BigInt(32) * BigInt(byte4Length);
//   bitmask = BigInt(0xff);
//   for(let i=0;i<byte4Remain;i++){
//     const num = Number((v >> BigInt(8)*BigInt(i)) & bitmask);
//     const pointer = extraByte + byte4Remain-1-i;
//     dv.setUint8(pointer, num);
//   }
  
//   return new Bytes(u8);
// }

// /**
//  * Return the number of bytes required to represent this integer.
//  * @param {number} v
//  */
// export function limbs_for_int(v: number|bigint): number {
//   return ((v >= 0 ? v : -v).toString(2).length + 7) >> 3;
// }
