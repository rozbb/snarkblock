pub mod api;
pub mod blocklist;
pub mod issuance;
mod util;

pub use crate::api::*;
pub use ark_serialize;
pub use ark_std::rand;
pub use blocklist::*;
pub use issuance::*;

#[cfg(any(test, feature = "benchmarking"))]
pub mod test_util;

use crate::util::{BlsFr, BlsFrV};

use ark_ff::UniformRand;
use ark_r1cs_std::alloc::AllocVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::rand::{CryptoRng, Rng};

/// A user's private ID, aka credential. This is the ID that's used in all our proofs
#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct PrivateId(pub BlsFr);

impl core::fmt::Debug for PrivateId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "[private ID]")
    }
}

impl PrivateId {
    pub fn gen<R: Rng + CryptoRng + ?Sized>(rng: &mut R) -> PrivateId {
        PrivateId(BlsFr::rand(rng))
    }
}

/// A user's private ID as it appears in a zero-knowledge circuit
#[derive(Clone)]
pub struct PrivateIdVar(pub BlsFrV);

impl PrivateIdVar {
    fn new_input(
        cs: impl Into<Namespace<BlsFr>>,
        priv_id: &PrivateId,
    ) -> Result<PrivateIdVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        let val = BlsFrV::new_input(cs, || Ok(priv_id.0))?;
        Ok(PrivateIdVar(val))
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("error in HiCIAP computation: {0}")]
    HiciapError(#[from] hiciap::Error),
}
