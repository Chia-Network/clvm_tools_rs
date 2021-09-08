use num_bigint::ToBigInt;
use num::pow;

use crate::classic::clvm::__type_compatibility__::{
    Bytes,
    BytesFromType,
    bi_zero,
    bi_one,
    get_u32,
    set_u32,
    set_u8
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

pub fn bigint_to_bytes(v_: &Number, option: Option<TConvertOption>) -> Result<Bytes, String> {
    let v = v_.clone();

    if v == bi_zero() {
        return Ok(Bytes::new(None));
    }

    let signed = option.map(|o| o.signed).unwrap_or_else(|| false);
    if !signed && v < bi_zero() {
        return Err("OverflowError: can't convert negative int to unsigned".to_string());
    }
    let mut byte_count = 1;
    let div = if signed { bi_one() } else { bi_zero() };
    let b32 : u64 = 1_u64 << 32;
    let bval = b32.to_bigint().unwrap();

    if v > bi_zero() {
        let mut right_hand = (v.clone() + bi_one()) * (div.clone() + bi_one());
        while pow(bval.clone(), (byte_count-1)/4 + 1) < right_hand {
            byte_count += 4;
        }
        right_hand = (v.clone() + bi_one()) * (div.clone() + bi_one());
        while pow(2_u32.to_bigint().unwrap(), 8 * byte_count) < right_hand {
            byte_count += 1;
        }
    } else if v < bi_zero() {
        let mut right_hand = (-(v.clone()) + bi_one()) * (div + bi_one());
        while pow(bval.clone(), (byte_count-1)/4 + 1) < right_hand {
            byte_count += 4;
        }
        right_hand = -(v.clone()) * 2.to_bigint().unwrap();
        while pow(2.to_bigint().unwrap(), 8 * byte_count) < right_hand {
            byte_count += 1;
        }
    }

    let extra_byte =
        if signed && v > bi_zero() && ((v.clone() >> ((byte_count-1) * 8)) & 0x80_u32.to_bigint().unwrap()) > bi_zero() { 1 } else { 0 };

    let total_bytes = byte_count + extra_byte;
    let mut dv = Vec::<u8>::with_capacity(total_bytes);
    let byte4_remain = byte_count % 4;
    let byte4_length = (byte_count - byte4_remain) / 4;

    dv.resize(total_bytes, 0);

    let (_sign, u32_digits) = v.to_u32_digits();
    for i in 0..byte4_length {
        let num = u32_digits[i];
        let pointer = extra_byte + byte4_remain + (byte4_length-1 - i)*4;
        set_u32(&mut dv, pointer, num);
    }

    let lastbytes = u32_digits[u32_digits.len() - 1];
    let bytes_bitmask = 0xff;
    for i in 0..byte4_remain {
        let num = (lastbytes >> (8*i)) & bytes_bitmask;
        let pointer = extra_byte + byte4_remain-1-i;
        set_u8(&mut dv, pointer, num as u8);
    }

    return Ok(Bytes::new(Some(BytesFromType::Raw(dv))));
}

// /**
//  * Return the number of bytes required to represent this integer.
//  * @param {number} v
//  */
// export function limbs_for_int(v: number|bigint): number {
//   return ((v >= 0 ? v : -v).toString(2).length + 7) >> 3;
// }
