use rand::prelude::*;
use rand::Error;

use random_lfsr_256_galois::{InitRegisterPayload, LFSRGalois, LFSRGaloisBuilder};

// A pseudo RNG which uses a slice for all entropy.  It iterates a given slice
// many times, scrambling the bits through an LFSR in subsequent passes so that
// the fuzzer maintains a relationship between the original input bits and the
// output with some predictability.
//
// This differs from BufRng in that it's not intended to be exhaustible since
// it's being used to generate extensible data structures.
pub struct FuzzPseudoRng<'slice> {
    slice: &'slice [u8],
    progress: usize,
}

impl<'slice> FuzzPseudoRng<'slice> {
    pub fn new(slice: &'slice [u8]) -> Self {
        return FuzzPseudoRng {
            slice: slice,
            progress: 0,
        };
    }

    fn next_u8_untreated(&mut self) -> u8 {
        if self.progress >= self.slice.len() {
            return 0;
        }
        let res = self.slice[self.progress];
        self.progress += 1;
        res
    }

    fn next_u32_untreated(&mut self) -> u32 {
        let mut result_u32: u32 = 0;
        for _ in 0..4 {
            result_u32 <<= 8;
            result_u32 |= self.next_u8_untreated() as u32;
        }
        result_u32
    }

    fn next_u64_untreated(&mut self) -> u64 {
        let result_u64: u64 = self.next_u32_untreated() as u64;
        result_u64 << 32 | self.next_u32_untreated() as u64
    }
}

impl<'slice> RngCore for FuzzPseudoRng<'slice> {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.next_u32_untreated()
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        self.next_u64_untreated()
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for i in 0..dest.len() {
            dest[i] = self.next_u8_untreated()
        }
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}