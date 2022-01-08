pub const IF_COST: u64 = 33;
pub const CONS_COST: u64 = 50;
pub const FIRST_COST: u64 = 30;
pub const REST_COST: u64 = 30;
pub const LISTP_COST: u64 = 19;

pub const MALLOC_COST_PER_BYTE: u64 = 10;

pub const ARITH_BASE_COST: u64 = 99;
pub const ARITH_COST_PER_BYTE: u64 = 3;
pub const ARITH_COST_PER_ARG: u64 = 320;

pub const LOG_BASE_COST: u64 = 100;
pub const LOG_COST_PER_BYTE: u64 = 3;
pub const LOG_COST_PER_ARG: u64 = 264;

pub const GRS_BASE_COST: u64 = 117;
pub const GRS_COST_PER_BYTE: u64 = 1;

pub const EQ_BASE_COST: u64 = 117;
pub const EQ_COST_PER_BYTE: u64 = 1;

pub const GR_BASE_COST: u64 = 498;
pub const GR_COST_PER_BYTE: u64 = 2;

pub const DIVMOD_BASE_COST: u64 = 1116;
pub const DIVMOD_COST_PER_BYTE: u64 = 6;

pub const DIV_BASE_COST: u64 = 988;
pub const DIV_COST_PER_BYTE: u64 = 4;

pub const SHA256_BASE_COST: u64 = 87;
pub const SHA256_COST_PER_ARG: u64 = 134;
pub const SHA256_COST_PER_BYTE: u64 = 2;

pub const POINT_ADD_BASE_COST: u64 = 101094;
pub const POINT_ADD_COST_PER_ARG: u64 = 1343980;

pub const PUBKEY_BASE_COST: u64 = 1325730;
pub const PUBKEY_COST_PER_BYTE: u64 = 38;

pub const MUL_BASE_COST: u64 = 92;
pub const MUL_COST_PER_OP: u64 = 885;
pub const MUL_LINEAR_COST_PER_BYTE: u64 = 6;
pub const MUL_SQUARE_COST_PER_BYTE_DIVIDER: u64 = 128;

pub const STRLEN_BASE_COST: u64 = 173;
pub const STRLEN_COST_PER_BYTE: u64 = 1;

pub const PATH_LOOKUP_BASE_COST: u64 = 40;
pub const PATH_LOOKUP_COST_PER_LEG: u64 = 4;
pub const PATH_LOOKUP_COST_PER_ZERO_BYTE: u64 = 4;

pub const CONCAT_BASE_COST: u64 = 142;
pub const CONCAT_COST_PER_ARG: u64 = 135;
pub const CONCAT_COST_PER_BYTE: u64 = 3;

pub const BOOL_BASE_COST: u64 = 200;
pub const BOOL_COST_PER_ARG: u64 = 300;

pub const ASHIFT_BASE_COST: u64 = 596;
pub const ASHIFT_COST_PER_BYTE: u64 = 3;

pub const LSHIFT_BASE_COST: u64 = 277;
pub const LSHIFT_COST_PER_BYTE: u64 = 3;

pub const LOGNOT_BASE_COST: u64 = 331;
pub const LOGNOT_COST_PER_BYTE: u64 = 3;

pub const APPLY_COST: u64 = 90;
pub const QUOTE_COST: u64 = 20;
