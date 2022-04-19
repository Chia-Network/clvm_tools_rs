use num::pow;
use num_bigint::ToBigInt;

use clvm_rs::allocator::Allocator;
use clvm_rs::reduction::EvalErr;

use crate::classic::clvm::__type_compatibility__::{
    bi_one, bi_zero, get_u32, set_u32, set_u8, Bytes, BytesFromType,
};
use crate::util::Number;

pub struct TConvertOption {
    pub signed: bool,
}

pub fn int_from_bytes<'a>(
    allocator: &'a mut Allocator,
    b: Bytes,
    option: Option<TConvertOption>,
) -> Result<u64, EvalErr> {
    if b.length() == 0 {
        return Ok(0);
    } else if b.length() * 8 > 64 {
        return Err(EvalErr(
            allocator.null(),
            "Cannot convert Bytes to Integer larger than 64bit. Use bigint_from_bytes instead."
                .to_string(),
        ));
    }

    let signed = option.map(|cvt| cvt.signed).unwrap_or_else(|| false);
    let mut unsigned64: u64 = 0;
    let dv = b.raw();

    let bytes4_remain = dv.len() % 4;
    let bytes4_length = (dv.len() - bytes4_remain) / 4;

    let mut order: u64 = 1;

    if bytes4_length > 0 {
        for i_reverse in 0..bytes4_length {
            let i = bytes4_length - i_reverse - 1;
            let byte32 = get_u32(&dv, i * 4 + bytes4_remain) as u64;
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
        return Ok((unsigned64 - 1 << (b.length() * 8)) as u64);
    }
    Ok(unsigned64)
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
            let byte32 = get_u32(&dv, i * 4 + bytes4_remain);
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
        return unsigned - (bi_one() << (b.length() * 8));
    }
    unsigned
}

pub fn bigint_to_bytes(v_: &Number, option: Option<TConvertOption>) -> Result<Bytes, String> {
    let v = v_.clone();

    if v == bi_zero() {
        return Ok(Bytes::new(None));
    }

    let negative = v < bi_zero();

    let signed = option.map(|o| o.signed).unwrap_or_else(|| false);
    if !signed && negative {
        return Err("OverflowError: can't convert negative int to unsigned".to_string());
    }
    let mut byte_count = 1;
    let div = if signed { bi_one() } else { bi_zero() };
    let b32: u64 = 1_u64 << 32;
    let bval = b32.to_bigint().unwrap();

    if negative {
        let mut right_hand = (-(v.clone()) + bi_one()) * (div + bi_one());
        while pow(bval.clone(), (byte_count - 1) / 4 + 1) < right_hand {
            byte_count += 4;
        }
        right_hand = -(v.clone()) * 2.to_bigint().unwrap();
        while pow(2.to_bigint().unwrap(), 8 * byte_count) < right_hand {
            byte_count += 1;
        }
    } else {
        let mut right_hand = (v.clone() + bi_one()) * (div.clone() + bi_one());
        while pow(bval.clone(), (byte_count - 1) / 4 + 1) < right_hand {
            byte_count += 4;
        }
        right_hand = (v.clone() + bi_one()) * (div.clone() + bi_one());
        while pow(2_u32.to_bigint().unwrap(), 8 * byte_count) < right_hand {
            byte_count += 1;
        }
    }

    let extra_byte = if signed
        && v > bi_zero()
        && ((v.clone() >> ((byte_count - 1) * 8)) & 0x80_u32.to_bigint().unwrap()) > bi_zero()
    {
        1
    } else {
        0
    };

    let total_bytes = byte_count + extra_byte;
    let mut dv = Vec::<u8>::with_capacity(total_bytes);
    let byte4_remain = byte_count % 4;
    let byte4_length = (byte_count - byte4_remain) / 4;

    dv.resize(total_bytes, 0);

    let (_sign, u32_digits) = v.to_u32_digits();
    for i in 0..byte4_length {
        let num = u32_digits[i];
        let pointer = extra_byte + byte4_remain + (byte4_length - 1 - i) * 4;
        let setval = if negative {
            (1_u64 << 32) - num as u64
        } else {
            num as u64
        };
        set_u32(&mut dv, pointer, setval as u32);
    }

    let lastbytes = u32_digits[u32_digits.len() - 1];
    let bytes_bitmask = 0xff;
    for i in 0..byte4_remain {
        let num = (lastbytes >> (8 * i)) & bytes_bitmask;
        let pointer = extra_byte + byte4_remain - 1 - i;
        let setval = if negative {
            (1_u32 << 8) - num as u32
        } else {
            num as u32
        };
        set_u8(&mut dv, pointer, setval as u8);
    }

    Ok(Bytes::new(Some(BytesFromType::Raw(dv))))
}

// /**
//  * Return the number of bytes required to represent this integer.
//  * @param {number} v
//  */
// export function limbs_for_int(v: number|bigint): number {
//   return ((v >= 0 ? v : -v).toString(2).length + 7) >> 3;
// }
