mod issuance;
mod util;

#[cfg(test)]
mod test_util;

use crate::util::BlsFr;
use ark_ff::UniformRand;
use ark_std::rand::{CryptoRng, Rng};

/// A user's private ID, aka credential. This is the ID that's used in all our proofs
#[derive(Copy, Clone)]
pub struct PrivateId(pub BlsFr);

impl PrivateId {
    pub fn gen<R: Rng + CryptoRng + ?Sized>(rng: &mut R) -> PrivateId {
        PrivateId(BlsFr::rand(rng))
    }
}
