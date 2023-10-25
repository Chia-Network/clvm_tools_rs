use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

pub mod fuzzrng;

// Note: Used for testing out aspects of the generated programs, since i've
// funneled in the bits from fuzzing to an rng interface.
pub fn make_random_u64_seed() -> u64 {
    let mut rng = ChaCha8Rng::from_entropy();
    rng.gen()
}
