use crate::{
    util::{to_canonical_bytes, BlsFr, BlsFrV, PoseidonCtx, PoseidonCtxVar},
    PrivateId, PrivateIdVar,
};

use ark_ff::{PrimeField, ToConstraintField, UniformRand, Zero};
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, eq::EqGadget, R1CSVar};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::rand::{CryptoRng, RngCore};
use blake2::Blake2b;
use digest::Digest;

const NONCE_CTX_DOMAIN_STR: &[u8] = b"snarkblock-nonce";

/// A nonce that has been bound to an SPID
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy, Default)]
pub struct SessionNonce(pub(crate) BlsFr);

impl SessionNonce {
    /// Generates a random nonce
    pub fn gen<R: RngCore + CryptoRng>(rng: &mut R) -> SessionNonce {
        SessionNonce(BlsFr::rand(rng))
    }

    /// Binds this nonce to the given context string
    pub fn bind_to_context(&self, context: &[u8]) -> SessionNonce {
        // The output nonce is H(input_nonce || spid)
        let mut h = Blake2b::with_params(b"", NONCE_CTX_DOMAIN_STR, b"");
        h.update(to_canonical_bytes(self.0).unwrap());
        h.update(context);

        // Parse the hash as a field element, reducing as necessary
        let nonce = BlsFr::from_be_bytes_mod_order(&h.finalize());
        SessionNonce(nonce)
    }
}

/// A session tag of the form tag = Prf_k(nonce) where k is a private ID
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy, Default)]
pub struct SessionTag(pub(crate) BlsFr);

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy)]
pub struct BlocklistElem {
    pub(crate) nonce: SessionNonce,
    pub(crate) tag: SessionTag,
}

impl Default for BlocklistElem {
    /// Returns a blocklist element of all 0s. This is an invalid blocklist element with
    /// overwhelming probability, so it shouldn't interfere with proofs of nonmembership.
    fn default() -> BlocklistElem {
        BlocklistElem {
            nonce: SessionNonce(BlsFr::zero()),
            tag: SessionTag(BlsFr::zero()),
        }
    }
}

// Define a way to serialize a blocklist element for HiCIAP verification
impl ToConstraintField<BlsFr> for BlocklistElem {
    fn to_field_elements(&self) -> Option<Vec<BlsFr>> {
        Some(vec![self.nonce.0, self.tag.0])
    }
}

#[derive(Clone)]
pub(crate) struct BlocklistElemVar {
    pub(crate) nonce: BlsFrV,
    pub(crate) tag: BlsFrV,
}

impl BlocklistElemVar {
    pub(crate) fn new_input(
        cs: impl Into<Namespace<BlsFr>>,
        elem: &BlocklistElem,
    ) -> Result<BlocklistElemVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        let nonce = BlsFrV::new_input(ns!(cs, "session nonce"), || Ok(elem.nonce.0))?;
        let tag = BlsFrV::new_input(ns!(cs, "session tag"), || Ok(elem.tag.0))?;

        Ok(BlocklistElemVar { nonce, tag })
    }
}

impl PrivateId {
    /// Given service provider ID, nonce, privID, computes H(ID || nonce || privID)
    pub(crate) fn compute_session_tag(
        &self,
        hash_ctx: &PoseidonCtx,
        nonce: SessionNonce,
    ) -> SessionTag {
        SessionTag(hash_ctx.prf(self.0, nonce.0))
    }

    /// Creates a valid, random blocklist element under this ID
    pub fn gen_blocklist_elem<R: RngCore + CryptoRng>(&self, rng: &mut R) -> BlocklistElem {
        let hash_ctx = PoseidonCtx::new();

        // Make a random nonce and compute the corresponding tag
        let nonce = SessionNonce::gen(rng);
        let tag = self.compute_session_tag(&hash_ctx, nonce);
        BlocklistElem { nonce, tag }
    }
}

impl PrivateIdVar {
    /// Given service provider ID, nonce, private ID, computes H(ID || nonce || privID)
    fn compute_session_tag(
        &self,
        hash_ctx: &PoseidonCtxVar,
        nonce: BlsFrV,
    ) -> Result<BlsFrV, SynthesisError> {
        hash_ctx.prf(self.0.clone(), nonce)
    }

    /// Returns a boolean which represents the statement "this private ID has generated some tag
    /// that appears in the given chunk"
    fn is_in_chunk(&self, chunk: &ChunkVar) -> Result<Boolean<BlsFr>, SynthesisError> {
        let cs = self.0.cs();
        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        // Go through each (nonce, tag) pair of the chunk, keeping track of whether this
        // private ID created anything in the chunk
        let mut found = Boolean::constant(false);
        for BlocklistElemVar { nonce, tag, .. } in &chunk.0 {
            let my_tag = self.compute_session_tag(&hash_ctx, nonce.clone())?;
            let tags_equal = my_tag.is_eq(tag)?;
            found = found.or(&tags_equal)?;
        }

        Ok(found)
    }
}

#[derive(Clone)]
pub struct Chunk(pub(crate) Vec<BlocklistElem>);

impl Chunk {
    /// Returns a chunk of all-zero blocklist elements. These are invalid elements with
    /// overwhelming probability, so it shouldn't interfere with proofs of nonmembership.
    pub(crate) fn default_with_size(size: usize) -> Chunk {
        Chunk(vec![BlocklistElem::default(); size])
    }

    /// Pads this chunk to the given chunk size. Panics if chunk_size < self.0.len()
    pub(crate) fn pad_to(&mut self, chunk_size: usize) {
        let padding_size = chunk_size
            .checked_sub(self.0.len())
            .expect("chunk slice too big");
        self.0
            .extend(core::iter::repeat(BlocklistElem::default()).take(padding_size));
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

/// This circuit proves that the blacklist element (nonce, tag) satisfies the relation
/// `tag = H(sp_id || nonce || credential)` where `sp_id` is the (public) service
/// provider ID, and credential is the hidden credential.
#[derive(Clone, Default)]
pub struct TagWellFormednessCircuit {
    // Hidden common inputs
    pub priv_id: PrivateId,
    // Public inputs
    pub blocklist_elem: BlocklistElem,
}

impl TagWellFormednessCircuit {
    pub(crate) fn new_placeholder() -> TagWellFormednessCircuit {
        Self::default()
    }

    /// The main logic of the circuit. The goal of this function is to prove that
    //     H(self.blocklist_elem.nonce || self.priv_id) = self.tag,
    // i.e., that the given session tag is correctly constructed wrt the hidden credential
    pub(crate) fn generate_constraints_preallocated(
        priv_id_var: PrivateIdVar,
        blocklist_elem_var: BlocklistElemVar,
        hash_ctx: PoseidonCtxVar,
    ) -> Result<(), SynthesisError> {
        // Compute the session tag from the credential and session nonce and assert that the
        // computed session tag is equal to the given session tag
        let computed_tag = priv_id_var.compute_session_tag(&hash_ctx, blocklist_elem_var.nonce)?;
        computed_tag.enforce_equal(&blocklist_elem_var.tag)
    }
}

impl ConstraintSynthesizer<BlsFr> for TagWellFormednessCircuit {
    // Witness the variables and run generate_constraints_preallocated
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        // Get hidden common input and public input
        let priv_id_var = PrivateIdVar::new_input(ns!(cs, "private id"), &self.priv_id)?;
        let blocklist_elem_var =
            BlocklistElemVar::new_input(ns!(cs, "blocklist elem"), &self.blocklist_elem)?;

        // Make a Poseidon instance
        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        // Run the logic
        Self::generate_constraints_preallocated(priv_id_var, blocklist_elem_var, hash_ctx)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_util::test_rng;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    #[test]
    fn test_well_formedness() {
        let mut rng = test_rng();

        // Generate a fresh ID and associated blocklist element
        let priv_id = PrivateId::gen(&mut rng);
        let blocklist_elem = priv_id.gen_blocklist_elem(&mut rng);

        // Ensure that tag well-formedness holds
        let cs = ConstraintSystem::<BlsFr>::new_ref();
        let circuit = TagWellFormednessCircuit {
            priv_id,
            blocklist_elem,
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // Now ensure that changing the tag to a random tag breaks this relation. Make the bad
        // element
        let mut bad_blocklist_elem = blocklist_elem;
        bad_blocklist_elem.tag = SessionTag(BlsFr::rand(&mut rng));
        let circuit = TagWellFormednessCircuit {
            priv_id,
            blocklist_elem: bad_blocklist_elem,
        };

        // Check that the circuit isn't satisfied
        let cs = ConstraintSystem::<BlsFr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_blocklist() {
        let mut rng = test_rng();
        let chunk_size = 256;

        // First, we show that a randomly generated priv_id does not appear in a randomly
        // generated blocklist

        // Generate everything randomly
        let priv_id = PrivateId::gen(&mut rng);
        let chunk = Chunk::gen_with_size(&mut rng, chunk_size);

        // Prove that the priv_id is not on the randomly generated blocklist
        let cs = ConstraintSystem::<BlsFr>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        let circuit = ChunkNonMembershipCircuit { priv_id, chunk };
        circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // Print the number of constraints in this chunk non-membership circuit
        println!(
            "Circuit for chunk of size {} is {} constraints",
            chunk_size,
            cs.num_constraints()
        );

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
