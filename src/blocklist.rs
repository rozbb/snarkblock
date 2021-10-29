use crate::{
    util::{BlsFr, BlsFrV, PoseidonCtx, PoseidonCtxVar},
    PrivateId, PrivateIdVar,
};

use ark_ff::{UniformRand, Zero};
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, eq::EqGadget, R1CSVar};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::rand::{CryptoRng, RngCore};

/// A nonce that has been bound to an SPID
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy)]
pub struct SessionNonce(pub(crate) BlsFr);

impl SessionNonce {
    pub(crate) fn gen<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> SessionNonce {
        SessionNonce(BlsFr::rand(rng))
    }
}

/// A session tag of the form tag = Prf_k(nonce) where k is a private ID
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy)]
pub struct SessionTag(pub(crate) BlsFr);

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy)]
pub struct BlocklistElem {
    pub(crate) sess_nonce: SessionNonce,
    pub(crate) sess_tag: SessionTag,
}

impl BlocklistElem {
    /// Returns a randomly generated blocklist elements. This is an invalid blocklist element with
    /// overwhelming probability, so it shouldn't interfere with proofs of nonmembership.
    #[cfg(test)]
    fn gen<R: RngCore + CryptoRng>(rng: &mut R) -> BlocklistElem {
        BlocklistElem {
            sess_nonce: SessionNonce::gen(rng),
            sess_tag: SessionTag(BlsFr::rand(rng)),
        }
    }
}

impl Default for BlocklistElem {
    /// Returns a blocklist element of all 0s. This is an invalid blocklist element with
    /// overwhelming probability, so it shouldn't interfere with proofs of nonmembership.
    fn default() -> BlocklistElem {
        BlocklistElem {
            sess_nonce: SessionNonce(BlsFr::zero()),
            sess_tag: SessionTag(BlsFr::zero()),
        }
    }
}

#[derive(Clone)]
pub(crate) struct BlocklistElemVar {
    pub(crate) sess_nonce: BlsFrV,
    pub(crate) sess_tag: BlsFrV,
}

impl BlocklistElemVar {
    fn new_input(
        cs: impl Into<Namespace<BlsFr>>,
        elem: &BlocklistElem,
    ) -> Result<BlocklistElemVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        let sess_nonce = BlsFrV::new_input(ns!(cs, "session nonce"), || Ok(elem.sess_nonce.0))?;
        let sess_tag = BlsFrV::new_input(ns!(cs, "session tag"), || Ok(elem.sess_tag.0))?;

        Ok(BlocklistElemVar {
            sess_nonce,
            sess_tag,
        })
    }
}

impl PrivateId {
    /// Given service provider ID, sess_nonce, privID, computes H(ID || sess_nonce || privID)
    pub(crate) fn compute_session_tag(
        &self,
        hash_ctx: &PoseidonCtx,
        sess_nonce: SessionNonce,
    ) -> SessionTag {
        SessionTag(hash_ctx.prf(self.0, sess_nonce.0))
    }

    /// Creates a valid, random blocklist element under this ID
    #[cfg(test)]
    pub(crate) fn gen_blocklist_elem<R: RngCore + CryptoRng>(&self, rng: &mut R) -> BlocklistElem {
        let hash_ctx = PoseidonCtx::new();

        // Make a random nonce and compute the corresponding tag
        let sess_nonce = SessionNonce::gen(rng);
        let sess_tag = self.compute_session_tag(&hash_ctx, sess_nonce);
        BlocklistElem {
            sess_nonce,
            sess_tag,
        }
    }
}

impl PrivateIdVar {
    /// Given service provider ID, sess_nonce, private ID, computes H(ID || sess_nonce || privID)
    fn compute_session_tag(
        &self,
        hash_ctx: &PoseidonCtxVar,
        sess_nonce: BlsFrV,
    ) -> Result<BlsFrV, SynthesisError> {
        hash_ctx.prf(self.0.clone(), sess_nonce)
    }

    /// Returns a boolean which represents the statement "this private ID has generated some tag
    /// that appears in the given chunk"
    fn is_in_chunk(&self, chunk: &ChunkVar) -> Result<Boolean<BlsFr>, SynthesisError> {
        let cs = self.0.cs();
        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        // Go through each (sess_nonce, sess_tag) pair of the chunk, keeping track of whether this
        // private ID created anything in the chunk
        let mut found = Boolean::constant(false);
        for BlocklistElemVar {
            sess_nonce,
            sess_tag,
            ..
        } in &chunk.0
        {
            let my_tag = self.compute_session_tag(&hash_ctx, sess_nonce.clone())?;
            let tags_equal = my_tag.is_eq(sess_tag)?;
            found = found.or(&tags_equal)?;
        }

        Ok(found)
    }
}

#[derive(Clone)]
pub(crate) struct Chunk(Vec<BlocklistElem>);

impl Chunk {
    /// Returns a chunk of all-zero blocklist elements. These are invalid elements with
    /// overwhelming probability, so it shouldn't interfere with proofs of nonmembership.
    pub(crate) fn default_with_size(size: usize) -> Chunk {
        Chunk(vec![BlocklistElem::default(); size])
    }

    #[cfg(test)]
    pub(crate) fn gen_with_size<R: RngCore + CryptoRng>(rng: &mut R, size: usize) -> Chunk {
        let elems = core::iter::repeat_with(|| BlocklistElem::gen(rng))
            .take(size)
            .collect();
        Chunk(elems)
    }
}

struct ChunkVar(Vec<BlocklistElemVar>);

impl ChunkVar {
    fn new_input(
        cs: impl Into<Namespace<BlsFr>>,
        chunk: &[BlocklistElem],
    ) -> Result<ChunkVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        // Witness all the elements
        let contents = chunk
            .iter()
            .map(|elem| BlocklistElemVar::new_input(ns!(cs, "blocklist elem"), elem))
            .collect::<Result<Vec<BlocklistElemVar>, SynthesisError>>()?;
        Ok(ChunkVar(contents))
    }
}

#[derive(Clone)]
pub(crate) struct ChunkNonMembershipCircuit {
    // Hidden common inputs
    pub(crate) priv_id: PrivateId,
    // Public inputs
    pub(crate) chunk: Chunk,
}

impl ChunkNonMembershipCircuit {
    /// Creates a placeholder circuit using 0s for the private ID and blocklist elements
    pub(crate) fn new_placeholder(chunk_size: usize) -> ChunkNonMembershipCircuit {
        ChunkNonMembershipCircuit {
            chunk: Chunk::default_with_size(chunk_size),
            priv_id: PrivateId::default(),
        }
    }
}

impl ConstraintSynthesizer<BlsFr> for ChunkNonMembershipCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        // Get hidden common input
        let priv_id_var = PrivateIdVar::new_input(ns!(cs, "private id"), &self.priv_id)?;

        // Get the chunk input and check whether priv_id has generated of its elements
        let chunk_var = ChunkVar::new_input(ns!(cs, "chunk input"), &self.chunk.0)?;
        let is_in_chunk = priv_id_var.is_in_chunk(&chunk_var)?;

        // Assert nonmembership
        is_in_chunk.enforce_equal(&Boolean::constant(false))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_util::test_rng;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_blocklist() {
        let mut rng = test_rng();
        let chunk_size = 100;

        // First, we show that a randomly generated priv_id does not appear in a randomly
        // generated blocklist

        // Generate everything randomly
        let priv_id = PrivateId::gen(&mut rng);
        let chunk = Chunk::gen_with_size(&mut rng, chunk_size);

        // Prove that the priv_id is not on the randomly generated blocklist
        let cs = ConstraintSystem::<BlsFr>::new_ref();
        let circuit = ChunkNonMembershipCircuit { priv_id, chunk };
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // Now check soundness. Make sure that the proof fails when the private ID is indeed on the
        // blocklist. Generate a fresh random blocklist, and also block the private ID we're using
        let mut chunk = Chunk::gen_with_size(&mut rng, chunk_size);
        chunk.0.push(priv_id.gen_blocklist_elem(&mut rng));

        // Prove that the private ID is not on the randomly generated blocklist
        let cs = ConstraintSystem::new_ref();
        let circuit = ChunkNonMembershipCircuit { priv_id, chunk };
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }
}
