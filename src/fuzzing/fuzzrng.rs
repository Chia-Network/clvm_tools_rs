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
    lfsr: LFSRGalois,
    slice: &'slice [u8],

    // Set on second or subsequent run
    lfsr_scramble: bool,
    progress: usize,
}

impl<'slice> FuzzPseudoRng<'slice> {
    pub fn new(slice: &'slice [u8]) -> Self {
        // Ensure the lfsr state is consistent so the entropy bits produce
        // an identical randomness every time.
        let lfsr = LFSRGaloisBuilder::new()
            .set_initial_payload(InitRegisterPayload::Meander)
            .build();
        return FuzzPseudoRng {
            lfsr: lfsr,
            slice: slice,

            lfsr_scramble: false,
            progress: 0,
        };
    }

    fn next_u8_untreated(&mut self) -> u8 {
        if self.slice.len() == 0 {
            self.lfsr_scramble = true;
            return 0;
        }
        if self.progress == self.slice.len() {
            self.progress = 0;
            self.lfsr_scramble = true;
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
        if self.lfsr_scramble {
            let lfsr32: u32 = self.lfsr.next();
            self.next_u32_untreated() ^ lfsr32
        } else {
            self.next_u32_untreated()
        }
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        eprintln!("next_u64");
        if self.lfsr_scramble {
            let lfsr64: u64 = self.lfsr.next();
            self.next_u64_untreated() ^ lfsr64
        } else {
            self.next_u64_untreated()
        }
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        eprintln!("fill_bytes");
        if self.lfsr_scramble {
            for i in 0..dest.len() {
                let lfsr8: u8 = self.lfsr.next();
                dest[i] = self.next_u8_untreated() ^ lfsr8
            }
        } else {
            for i in 0..dest.len() {
                dest[i] = self.next_u8_untreated()
            }
        }
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}
