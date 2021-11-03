use crate::{
    blocklist::{BlocklistElem, Chunk, ChunkNonMembershipCircuit, TagWellFormednessCircuit},
    issuance::{IssuanceOpening, OneofNSchnorrVerifyCircuit, SchnorrPubkey, SchnorrSignature},
    util::{Bls12_381, BlsFr},
    PrivateId,
};

use core::iter;

use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::rand::{CryptoRng, RngCore};
use hiciap::HiciapError;

/// A Groth16 proving key specifically for issuance and tag well-formedness proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct IssuanceAndTagProvingKey(ark_groth16::ProvingKey<Bls12_381>);

/// A Groth16 verifying key specifically for issuance and tag well-formedness proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct IssuanceAndTagVerifKey(ark_groth16::VerifyingKey<Bls12_381>);

/// A proof of issuance and tag well-formedness
pub struct IssuanceAndTagProof(ark_groth16::Proof<Bls12_381>);

/// A Groth16 proving key specifically for chunk proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct ChunkProvingKey {
    /// The chunk size this is supposed to be used for
    chunk_size: usize,
    /// The proving key itself
    pk: ark_groth16::ProvingKey<Bls12_381>,
}

/// A Groth16 proving key specifically for chunk proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct ChunkVerifKey {
    /// The chunk size this is supposed to be used for
    chunk_size: usize,
    /// The verif key itself
    vk: ark_groth16::VerifyingKey<Bls12_381>,
}

/// Returns a size-specific chunk proving key and verifying key
pub fn chunk_setup<R: CryptoRng + RngCore>(
    rng: &mut R,
    chunk_size: usize,
) -> (ChunkProvingKey, ChunkVerifKey) {
    let circuit = ChunkNonMembershipCircuit::new_placeholder(chunk_size);
    let (pk, vk) = Groth16::setup(circuit, rng).expect("couldn't setup chunk circuit");

    (
        ChunkProvingKey { chunk_size, pk },
        ChunkVerifKey { chunk_size, vk },
    )
}

/// A proof nonmembership in a chunk
pub struct ChunkProof(ark_groth16::Proof<Bls12_381>);

/// Holds the context to construct Snarkblock chunk proofs
pub struct ChunkProver {
    /// The user's private ID
    pub priv_id: PrivateId,
    /// The proving key for chunk proofs
    pub proving_key: ChunkProvingKey,
}

// A helper function that binds the chunk to the given SPID and pads it to the given length
fn bind_and_pad(chunk: &[BlocklistElem], spid: &[u8], chunk_size: usize) -> Chunk {
    if chunk.len() > chunk_size {
        panic!("Provided chunk is bigger than prover's preprogrammed chunk size");
    }

    // Make a copy of the chunk because we need to edit it
    let mut chunk = chunk.to_vec();

    // Bind every sessions nonce in the chunk to the SPID
    for elem in chunk.iter_mut() {
        elem.sess_nonce = elem.sess_nonce.bind_to_spid(spid);
    }

    // Now pad the chunk out to the correct chunk size
    let padding_size = chunk_size - chunk.len();
    chunk.extend(iter::repeat(BlocklistElem::default()).take(padding_size));

    Chunk(chunk)
}

impl ChunkProver {
    /// Computes a proof of nonmembership of the private ID in the current chunk. If the given
    /// chunk is less than this `ChunkProver`'s chunk size, then it will be right-padded with
    /// the appropriate number of null blocklist elements.
    ///
    /// # Panics
    /// Iff the provided chunk is greater than this `ChunkProver`'s chunk size.
    pub fn prove<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
        elems: &[BlocklistElem],
    ) -> Result<ChunkProof, SynthesisError> {
        // Pad the chunk to the appropriate length
        let mut chunk = Chunk(elems.to_vec());
        chunk.pad_to(self.proving_key.chunk_size);

        // Construct the circuit and prove it
        let circuit = ChunkNonMembershipCircuit {
            priv_id: self.priv_id,
            chunk,
        };
        Groth16::prove(&self.proving_key.pk, circuit, rng).map(ChunkProof)
    }
}

/// A compressed value representing an entire chunk. This is used in verification
pub struct PreparedChunk(hiciap::PreparedCircuitInput<Bls12_381>);

/// Holds the context to allow Snarkblock to verify chunks
pub struct ChunkVerifCtx {
    /// The proving key for chunk proofs
    pub verif_key: ChunkVerifKey,
}

impl ChunkVerifCtx {
    /// Prepares a chunk into a form that can be used for HiCIAP verification. If `chunk.len() <
    /// chunk_size`, then the chunk will be right-padded with the appropriate number of null
    /// blocklist elements.
    ///
    /// # Panics
    /// Iff `chunk.len() > chunk_size`
    pub fn prepare_chunk(&self, elems: &[BlocklistElem]) -> Result<PreparedChunk, HiciapError> {
        // Pad the chunk to the appropriate length
        let mut chunk = Chunk(elems.to_vec());
        chunk.pad_to(self.verif_key.chunk_size);

        // Now serialize the chunk into a flat array of field elements
        let serialized_chunk: Vec<BlsFr> = chunk
            .0
            .iter()
            .flat_map(|e| iter::once(&e.sess_nonce.0).chain(iter::once(&e.sess_tag.0)))
            .cloned()
            .collect();

        hiciap::prepare_circuit_input(&self.verif_key.vk, &serialized_chunk).map(PreparedChunk)
    }
}

/// This circuit proves the conjunction of the OneofNSchnorrVerifyCircuit and
/// TagWellFormednessCircuit
pub(crate) struct IssuanceAndWfCircuit {
    pub issuance_circuit: OneofNSchnorrVerifyCircuit,
    pub wf_circuit: TagWellFormednessCircuit,
}

impl IssuanceAndWfCircuit {
    /*
    fn new(
        priv_id: PrivateId,
        proving_key: IssuanceAndTagProvingKey,
        pubkeys: Vec<SchnorrPubkey>,
        signers_pubkey_idx: u16,
        opening: IssuanceOpening,
        sig: SchnorrSignature,
    ) -> IssuanceAndWfCircuit {
        let issuance_circuit =
            OneofNSchnorrVerifyCircuit::new(pubkeys, signers_pubkey_idx, priv_id, opening, sig);
        let wf_circuit = TagWellFormednessCircuit {
            priv_id,
            blocklist_elem,
        };
    }
    */

    /// Returns a placeholder circuit where only `num_pubkeys` is set. This is used for circuit
    /// parameter generation.
    fn new_placeholder(num_pubkeys: usize) -> IssuanceAndWfCircuit {
        let issuance_circuit = OneofNSchnorrVerifyCircuit::new_placeholder(num_pubkeys);
        let wf_circuit = TagWellFormednessCircuit::new_placeholder();

        IssuanceAndWfCircuit {
            issuance_circuit,
            wf_circuit,
        }
    }
}

impl ConstraintSynthesizer<BlsFr> for IssuanceAndWfCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        self.issuance_circuit.generate_constraints(cs.clone())?;
        self.wf_circuit.generate_constraints(cs)
    }
}

/// Holds the context for proving the issuance-and-tag-well-formedness statement
pub struct IssuanceAndTagProver {
    /// The user's private ID
    pub priv_id: PrivateId,
    // The set of verifier keys that could have signed a commitment to msg
    pub pubkeys: Vec<SchnorrPubkey>,
    // The the pubkey being used for verification
    pub signers_pubkey_idx: u16,
    // The opnening to a commitment to priv_id
    pub opening: IssuanceOpening,
    // A signature over Com(priv_id; com_opening) wrt the pubkey selected by pubkey_selector
    pub sig: SchnorrSignature,
    /// The proving key for issuance-and-tag-well-formedness proofs
    pub proving_key: IssuanceAndTagProvingKey,
}

impl IssuanceAndTagProver {
    /// Computes a proof that 1) the private ID has been issued by an issuer in `pubkeys`, and
    /// 2) the given private ID has produced the given blocklist element.
    pub fn prove<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
        blocklist_elem: BlocklistElem,
    ) -> Result<IssuanceAndTagProof, SynthesisError> {
        // Construct the circuit and prove it
        let issuance_circuit = OneofNSchnorrVerifyCircuit::new(
            self.pubkeys.clone(),
            self.signers_pubkey_idx,
            self.priv_id,
            self.opening.clone(),
            self.sig.clone(),
        );
        let wf_circuit = TagWellFormednessCircuit {
            priv_id: self.priv_id,
            blocklist_elem,
        };
        let issuance_and_wf_circuit = IssuanceAndWfCircuit {
            issuance_circuit,
            wf_circuit,
        };

        Groth16::prove(&self.proving_key.0, issuance_and_wf_circuit, rng).map(IssuanceAndTagProof)
    }
}
