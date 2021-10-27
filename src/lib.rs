mod util;

use ark_ff::{PrimeField, UniformRand};
use ark_std::rand::Rng;

/// A user's private ID, aka credential. This is the ID that's used in all our proofs
#[derive(Copy, Clone)]
pub struct PrivateId<F: PrimeField>(pub F);

impl<F: PrimeField> UniformRand for PrivateId<F> {
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> PrivateId<F> {
        PrivateId(F::rand(rng))
    }
}
