use num_bigint::ToBigInt;
use num_traits::ToPrimitive;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

use crate::compiler::sexp::random_atom_name;
use crate::util::number_from_u8;

pub mod fuzzrng;

// Note: Used for testing out aspects of the generated programs, since i've
// funneled in the bits from fuzzing to an rng interface.
pub fn make_random_u64_seed() -> u64 {
    let mut rng = ChaCha8Rng::from_entropy();
    let random_seed = random_atom_name(&mut rng, 10);
    let random_seed_as_bigint =
        number_from_u8(&random_seed) & 0xffffffffffff_u64.to_bigint().unwrap();
    random_seed_as_bigint.to_u64().unwrap()
}
