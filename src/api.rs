use crate::{
    blocklist::{
        BlocklistElem, BlocklistElemVar, Chunk, ChunkNonMembershipCircuit, TagWellFormednessCircuit,
    },
    issuance::{
        IssuanceOpening, OneofNSchnorrVerifyCircuit, SchnorrPubkey, SchnorrPubkeyVar,
        SchnorrSignature, SchnorrSignatureVar,
    },
    util::{Bls12_381, BlsFr, BlsFrV, PoseidonCtxVar},
    Error, PrivateId, PrivateIdVar,
};

use core::iter;

use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_ff::ToConstraintField;
use ark_groth16::Groth16;
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::rand::{CryptoRng, RngCore};
use hiciap::{
    hiciap_prove, hiciap_setup, hiciap_verify,
    linkage::{hiciap_link, LinkageProof},
    merlin::Transcript,
    HiciapProof, HiciapProvingKey, HiciapVerifKey, HiddenInputOpening,
};

// Domain separators for our proofs
const AGG_CHUNK_DOMAIN_STR: &[u8] = b"snarkblock-aggproof-chunk";
const AGG_IWF_DOMAIN_STR: &[u8] = b"snarkblock-aggproof-iwf";

/// A Groth16 proving key specifically for issuance-and-tag well-formedness proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct IssuanceAndWfProvingKey(ark_groth16::ProvingKey<Bls12_381>);

/// A Groth16 verifying key specifically for issuance-and-tag well-formedness proofs
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct IssuanceAndWfVerifKey(ark_groth16::VerifyingKey<Bls12_381>);

/// A proof of issuance and tag well-formedness
pub struct IssuanceAndWfProof(ark_groth16::Proof<Bls12_381>);

/// Returns a pubkey-list-size-specific issuance-and-tag-well-formedenss proving key and verifying key
pub fn issuance_and_wf_setup<R: CryptoRng + RngCore>(
    rng: &mut R,
    num_pubkeys: usize,
) -> (IssuanceAndWfProvingKey, IssuanceAndWfVerifKey) {
    let circuit = IssuanceAndWfWfCircuit::new_placeholder(num_pubkeys);
    let (pk, vk) = Groth16::setup(circuit, rng).expect("couldn't setup IWF circuit");

    (IssuanceAndWfProvingKey(pk), IssuanceAndWfVerifKey(vk))
}

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
pub type ChunkProof = ark_groth16::Proof<Bls12_381>;

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
        chunk: &Chunk,
    ) -> Result<ChunkProof, SynthesisError> {
        let desired_chunk_size = self.proving_key.chunk_size;

        // Pad the chunk to the appropriate length if it's not already there
        let chunk = if chunk.0.len() == desired_chunk_size {
            chunk.clone()
        } else {
            let mut copy = chunk.clone();
            copy.pad_to(desired_chunk_size);
            copy
        };

        // Construct the circuit and prove it
        let circuit = ChunkNonMembershipCircuit {
            priv_id: self.priv_id,
            chunk,
        };
        Groth16::prove(&self.proving_key.pk, circuit, rng)
    }
}

/// A compressed value representing an entire chunk. This is used in verification
pub type PreparedChunk = hiciap::PreparedCircuitInput<Bls12_381>;

/// Holds the context to allow Snarkblock to prepare chunks for verification
pub struct ChunkPreparer {
    /// The proving key for chunk proofs
    pub verif_key: ChunkVerifKey,
}

impl ChunkPreparer {
    /// Prepares a chunk into a form that can be used for HiCIAP verification. If `chunk.len() <
    /// chunk_size`, then the chunk will be right-padded with the appropriate number of null
    /// blocklist elements.
    ///
    /// # Panics
    /// Iff `chunk.len() > chunk_size`
    pub fn prepare(&self, chunk: &Chunk) -> Result<PreparedChunk, Error> {
        let desired_chunk_size = self.verif_key.chunk_size;

        // Pad the chunk to the appropriate length if it's not already there
        let chunk = if chunk.0.len() == desired_chunk_size {
            chunk.clone()
        } else {
            let mut copy = chunk.clone();
            copy.pad_to(desired_chunk_size);
            copy
        };

        // Now serialize the chunk into a flat array of field elements
        let serialized_chunk: Vec<BlsFr> = chunk
            .0
            .iter()
            .flat_map(|e| iter::once(&e.sess_nonce.0).chain(iter::once(&e.sess_tag.0)))
            .cloned()
            .collect();

        hiciap::prepare_circuit_input(&self.verif_key.vk, &serialized_chunk).map_err(Into::into)
    }
}

/// This circuit proves the conjunction of the OneofNSchnorrVerifyCircuit and
/// TagWellFormednessCircuit
pub(crate) struct IssuanceAndWfWfCircuit {
    pub issuance_circuit: OneofNSchnorrVerifyCircuit,
    pub wf_circuit: TagWellFormednessCircuit,
}

impl IssuanceAndWfWfCircuit {
    /// Returns a placeholder circuit where only `num_pubkeys` is set. This is used for circuit
    /// parameter generation.
    fn new_placeholder(num_pubkeys: usize) -> IssuanceAndWfWfCircuit {
        let issuance_circuit = OneofNSchnorrVerifyCircuit::new_placeholder(num_pubkeys);
        let wf_circuit = TagWellFormednessCircuit::new_placeholder();

        IssuanceAndWfWfCircuit {
            issuance_circuit,
            wf_circuit,
        }
    }
}

impl ConstraintSynthesizer<BlsFr> for IssuanceAndWfWfCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        // Check that the private IDs of the subcircuits are the same
        assert_eq!(
            self.issuance_circuit.priv_id, self.wf_circuit.priv_id,
            "private IDs of issuance and well-formedness circuits differ"
        );
        let priv_id = self.issuance_circuit.priv_id;

        // Get the public inputs: Private ID, pubkey list, new blocklist element
        let priv_id_var = PrivateIdVar::new_input(ns!(cs, "priv_id var"), &priv_id)?;
        let pubkey_vars = self
            .issuance_circuit
            .pubkeys
            .iter()
            .map(|pk| SchnorrPubkeyVar::new_input(ns!(cs, "pubkey var"), pk))
            .collect::<Result<Vec<SchnorrPubkeyVar>, _>>()?;
        let blocklist_elem_var = BlocklistElemVar::new_input(
            ns!(cs, "blocklist elem"),
            &self.wf_circuit.blocklist_elem,
        )?;

        // Witness the hidden inputs
        let sig_var =
            SchnorrSignatureVar::new_witness(ns!(cs, "sig var"), &self.issuance_circuit.sig)?;
        let priv_id_opening_var = BlsFrV::new_witness(ns!(cs, "priv_id opening var"), || {
            Ok(self.issuance_circuit.priv_id_opening.0)
        })?;
        let pubkey_selector_var = self
            .issuance_circuit
            .pubkey_selector
            .iter()
            .map(|b| Boolean::new_witness(ns!(cs, "pubkey var"), || Ok(b)))
            .collect::<Result<Vec<Boolean<BlsFr>>, _>>()?;

        // Make a Poseidon hasher
        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        // Now run the subcircuits on the variables
        TagWellFormednessCircuit::generate_constraints_preallocated(
            priv_id_var.clone(),
            blocklist_elem_var,
            hash_ctx.clone(),
        )?;
        OneofNSchnorrVerifyCircuit::generate_constraints_preallocated(
            priv_id_var,
            pubkey_vars,
            sig_var,
            priv_id_opening_var,
            pubkey_selector_var,
            hash_ctx,
        )
    }
}

/// Holds the context for proving the issuance-and-tag-well-formedness statement
pub struct IssuanceAndWfProver {
    /// The user's private ID
    pub priv_id: PrivateId,
    // The set of verifier keys that could have signed a commitment to msg
    pub pubkeys: Vec<SchnorrPubkey>,
    // The the pubkey being used for verification
    pub signers_pubkey_idx: u16,
    // The opnening to a commitment to priv_id
    pub priv_id_opening: IssuanceOpening,
    // A signature over Com(priv_id; com_opening) wrt the pubkey selected by pubkey_selector
    pub sig: SchnorrSignature,
    /// The proving key for issuance-and-tag-well-formedness proofs
    pub proving_key: IssuanceAndWfProvingKey,
}

impl IssuanceAndWfProver {
    /// Computes a proof that 1) the private ID has been issued by an issuer in `pubkeys`, and
    /// 2) the given private ID has produced the given blocklist element.
    pub fn prove<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
        blocklist_elem: BlocklistElem,
    ) -> Result<IssuanceAndWfProof, SynthesisError> {
        // Construct the subcircuits
        let issuance_circuit = OneofNSchnorrVerifyCircuit::new(
            self.pubkeys.clone(),
            self.signers_pubkey_idx,
            self.priv_id,
            self.priv_id_opening.clone(),
            self.sig.clone(),
        );
        let wf_circuit = TagWellFormednessCircuit {
            priv_id: self.priv_id,
            blocklist_elem,
        };

        // Combine the subcircuits and prove it
        let issuance_and_wf_circuit = IssuanceAndWfWfCircuit {
            issuance_circuit,
            wf_circuit,
        };
        Groth16::prove(&self.proving_key.0, issuance_and_wf_circuit, rng).map(IssuanceAndWfProof)
    }
}

/// A HiCIAP proving key for aggregating issuance-and-tag-well-formedness proofs
pub struct AggIwfProvingKey(HiciapProvingKey<Bls12_381>);
/// A HiCIAP verifying key for aggregated issuance-and-tag-well-formedness proofs
pub struct AggIwfVerifKey(HiciapVerifKey<Bls12_381>);

/// Returns a proving key and verifying key for aggregating issuance-and-tag-well-formedness proofs
pub fn agg_iwf_setup<R: CryptoRng + RngCore>(rng: &mut R) -> (AggIwfProvingKey, AggIwfVerifKey) {
    // This is fixed because there's only ever 1 IWF proof anyway. We just repeat it 13 times.
    let num_proofs = 14;
    let pk = hiciap_setup(rng, num_proofs).expect("couldn't generate agg chunk CRS");
    let vk: hiciap::HiciapVerifKey<Bls12_381> = From::from(&pk);

    (AggIwfProvingKey(pk), AggIwfVerifKey(vk))
}

/// A struct for turning `IssuanceAndWfProof`s into HiCIAP proofs of the same statement
pub struct AggIwfProver {
    /// The user's private ID
    pub priv_id: PrivateId,
    /// Verification key for verifying the issuance-and-tag-well-formedness circuit
    pub circuit_verif_key: IssuanceAndWfVerifKey,
    /// Key for proving aggregates
    pub agg_proving_key: AggIwfProvingKey,
}

/// A struct for verifying `AggIwfProof`s
pub struct AggIwfVerifier {
    // The set of verifier keys that could have signed a commitment to msg
    pub pubkeys: Vec<SchnorrPubkey>,
    /// Verification key for verifying the issuance-and-tag-well-formedness circuit
    pub circuit_verif_key: IssuanceAndWfVerifKey,
    /// Key for verifying aggregates
    pub agg_verif_key: AggIwfVerifKey,
}

/// A HiCIAP proof of issuance-and-tag-well-formedness
pub struct AggIwfProof {
    /// The proof of the aggregate of the IAT circuit proofs
    hiciap_proof: HiciapProof<Bls12_381>,
    /// The opening of the commitment to priv_id
    priv_id_opening: HiddenInputOpening<Bls12_381>,
}

impl AggIwfProver {
    /// Computes an aggregate proof of the given ChunkProofs
    pub fn prove<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
        proof: &IssuanceAndWfProof,
    ) -> Result<AggIwfProof, Error> {
        // HiCIAP requires a minimum of 14 proofs to function
        let mut proof_vec = vec![proof.0.clone(); 14];

        let mut proof_transcript = Transcript::new(AGG_IWF_DOMAIN_STR);

        // Do a no-CSM proof for the issuance-and-tag
        let (hiciap_proof, priv_id_opening) = hiciap_prove(
            rng,
            &mut proof_transcript,
            &self.agg_proving_key.0,
            &self.circuit_verif_key.0,
            proof_vec.as_mut_slice(),
            None,
            self.priv_id.0,
        )?;

        Ok(AggIwfProof {
            hiciap_proof,
            priv_id_opening,
        })
    }
}

impl AggIwfVerifier {
    // TODO: Do the input preprocessing beforehand
    pub fn verify(&self, new_elem: &BlocklistElem, proof: &AggIwfProof) -> Result<bool, Error> {
        let mut verif_transcript = Transcript::new(AGG_IWF_DOMAIN_STR);

        // The public input to a single issuance-and-tag-well-formedness circuit is the pubkeys
        // followed by the blocklisted element
        let single_circuit_input: Vec<BlsFr> = self
            .pubkeys
            .iter()
            .flat_map(|pk| pk.0.to_field_elements().unwrap())
            .chain(new_elem.to_field_elements().unwrap().into_iter())
            .collect();
        let prepared_circuit_input =
            hiciap::prepare_circuit_input(&self.circuit_verif_key.0, &single_circuit_input)?;

        // We have 14 copies of the same circuit because HiCIAP needs at least that many
        let mut prepared_circuit_inputs = vec![prepared_circuit_input; 14];
        let verifier_inputs = hiciap::VerifierInputs::List(&mut prepared_circuit_inputs);

        // Now make the verifier context and prove
        let mut verif_ctx = hiciap::VerifierCtx {
            hiciap_vk: &self.agg_verif_key.0,
            circuit_vk: &self.circuit_verif_key.0,
            pub_input: verifier_inputs,
        };
        hiciap_verify(&mut verif_ctx, &mut verif_transcript, &proof.hiciap_proof)
            .map_err(Into::into)
    }
}

/// A commitment to the entire blocklist. This must be updated every time the blocklist is updated
pub struct BlocklistCom(hiciap::VerifierInputs<'static, Bls12_381>);

impl BlocklistCom {
    pub fn from_prepared_chunks(
        chunks: &mut Vec<PreparedChunk>,
        pk: &AggChunkProvingKey,
    ) -> BlocklistCom {
        let mut inputs = hiciap::VerifierInputs::List(chunks);
        inputs
            .compress(&pk.0)
            .expect("could not compress prepared chunk inputs");

        match inputs {
            hiciap::VerifierInputs::Com(a, b) => {
                // We need to convince the compiler that the com is indeed 'static, so we
                // reconstruct it from scratch.
                let com: hiciap::VerifierInputs<'static, Bls12_381> =
                    hiciap::VerifierInputs::Com(a, b);
                BlocklistCom(com)
            }
            // This is impossible. The compress() method always produces a VerifierInputs::Com
            _ => panic!("inputs did not compress"),
        }
    }
}

/// A HiCIAP proving key for aggregating chunk non-membership proofs
#[derive(Clone)]
pub struct AggChunkProvingKey(HiciapProvingKey<Bls12_381>);
/// A HiCIAP verifying key for aggregated chunk non-membership proofs
#[derive(Clone)]
pub struct AggChunkVerifKey(HiciapVerifKey<Bls12_381>);

/// Returns a blocklist-length-specific proving key and verifying key for aggregated chunk proofs
pub fn agg_chunk_setup<R: CryptoRng + RngCore>(
    rng: &mut R,
    num_chunks: usize,
) -> (AggChunkProvingKey, AggChunkVerifKey) {
    let pk = hiciap_setup(rng, num_chunks).expect("couldn't generate agg chunk CRS");
    let vk: hiciap::HiciapVerifKey<Bls12_381> = From::from(&pk);

    (AggChunkProvingKey(pk), AggChunkVerifKey(vk))
}

/// An aggregate of chunk non-membership proofs
pub struct AggChunkProof {
    /// The proof of the aggregate of the chunks
    hiciap_proof: HiciapProof<Bls12_381>,
    /// The opening of the commitment to priv_id
    priv_id_opening: HiddenInputOpening<Bls12_381>,
}

/// A struct for aggregating `ChunkProof`s into a single `AggChunkProof`
pub struct AggChunkProver {
    /// The user's private ID
    pub priv_id: PrivateId,
    /// Verification key for verifying the issuance-and-tag-well-formedness circuit
    pub circuit_verif_key: ChunkVerifKey,
    /// Key for proving aggregates
    pub agg_proving_key: AggChunkProvingKey,
}

/// A struct for verifying `AggChunkProof`s
pub struct AggChunkVerifier {
    /// Verification key for verifying the issuance-and-tag-well-formedness circuit
    pub circuit_verif_key: ChunkVerifKey,
    /// Key for verifying aggregates
    pub agg_verif_key: AggChunkVerifKey,
}

impl AggChunkProver {
    /// Computes an aggregate proof of the given ChunkProofs
    pub fn prove<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
        proofs: &mut [ChunkProof],
        prepared_chunks: &mut Vec<PreparedChunk>,
    ) -> Result<AggChunkProof, Error> {
        let mut proof_transcript = Transcript::new(AGG_CHUNK_DOMAIN_STR);
        let (hiciap_proof, priv_id_opening) = hiciap_prove(
            rng,
            &mut proof_transcript,
            &self.agg_proving_key.0,
            &self.circuit_verif_key.vk,
            proofs,
            Some(prepared_chunks),
            self.priv_id.0,
        )?;

        Ok(AggChunkProof {
            hiciap_proof,
            priv_id_opening,
        })
    }
}

impl AggChunkVerifier {
    pub fn verify(&self, com: BlocklistCom, proof: &AggChunkProof) -> Result<bool, Error> {
        let mut verif_transcript = Transcript::new(AGG_CHUNK_DOMAIN_STR);
        let mut verif_ctx = hiciap::VerifierCtx {
            hiciap_vk: &self.agg_verif_key.0,
            circuit_vk: &self.circuit_verif_key.vk,
            pub_input: com.0,
        };
        hiciap_verify(&mut verif_ctx, &mut verif_transcript, &proof.hiciap_proof)
            .map_err(Into::into)
    }
}

pub struct SnarkblockProof {
    chunk_proofs: Vec<AggChunkProof>,
    issuance_and_tag_proof: AggIwfProof,
    linkage_proof: LinkageProof<Bls12_381>,
}

pub fn snarkblock_link<R: CryptoRng + RngCore>(
    rng: &mut R,
    issuance_and_tag_proof: AggIwfProof,
    chunk_proofs: Vec<AggChunkProof>,
) -> SnarkblockProof {
    let proof_data: Vec<(&HiciapProof<Bls12_381>, &HiddenInputOpening<Bls12_381>)> = iter::once((
        &issuance_and_tag_proof.hiciap_proof,
        &issuance_and_tag_proof.priv_id_opening,
    ))
    .chain(
        chunk_proofs
            .iter()
            .map(|cp| (&cp.hiciap_proof, &cp.priv_id_opening)),
    )
    .collect();
    let linkage_proof = hiciap_link(rng, &proof_data);

    SnarkblockProof {
        chunk_proofs,
        issuance_and_tag_proof,
        linkage_proof,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_util::{rand_issuance, test_rng};

    /// Tests the correctness of the aggregate issuance-and-tag-well-formedness prover
    #[test]
    fn test_agg_iwf() {
        let mut rng = test_rng();
        let num_pubkeys = 16;

        // Generate a fresh private ID, make a valid blocklist element, and do the issuance
        let priv_id = PrivateId::gen(&mut rng);
        let blocklist_elem = priv_id.gen_blocklist_elem(&mut rng);
        let (pubkeys, signers_pubkey_idx, sig, priv_id_opening) =
            rand_issuance(&mut rng, priv_id, num_pubkeys);

        // Do all the setups
        let (iwf_pk, iwf_vk) = issuance_and_wf_setup(&mut rng, num_pubkeys);
        let (agg_iwf_pk, agg_iwf_vk) = agg_iwf_setup(&mut rng);

        let iwf_prover = IssuanceAndWfProver {
            priv_id,
            pubkeys: pubkeys.clone(),
            signers_pubkey_idx,
            priv_id_opening,
            sig,
            proving_key: iwf_pk,
        };
        let agg_iwf_prover = AggIwfProver {
            priv_id,
            circuit_verif_key: iwf_vk.clone(),
            agg_proving_key: agg_iwf_pk,
        };
        let agg_iwf_verifier = AggIwfVerifier {
            pubkeys,
            circuit_verif_key: iwf_vk,
            agg_verif_key: agg_iwf_vk,
        };

        // Do the proof
        let base_proof = iwf_prover
            .prove(&mut rng, blocklist_elem)
            .expect("couldn't prove base IWF");
        let agg_proof = agg_iwf_prover
            .prove(&mut rng, &base_proof)
            .expect("couldn't prove IWF HiCIAP");

        // Ensure that the aggregate verifies
        assert!(agg_iwf_verifier
            .verify(&blocklist_elem, &agg_proof)
            .expect("couldn't verify agg IWF proof"));
    }

    /// Tests the correctness of the aggregate chunk prover
    #[test]
    fn test_agg_blocklist() {
        let mut rng = test_rng();
        let chunk_size = 16;
        let num_chunks = 14;

        // Generate everything randomly
        let priv_id = PrivateId::gen(&mut rng);
        let blocklist: Vec<Chunk> =
            iter::repeat_with(|| Chunk::gen_with_size(&mut rng, chunk_size))
                .take(num_chunks)
                .collect();

        // Do all the setups
        let (chunk_pk, chunk_vk) = chunk_setup(&mut rng, chunk_size);
        let (agg_chunk_pk, agg_chunk_vk) = agg_chunk_setup(&mut rng, num_chunks);

        let chunk_prover = ChunkProver {
            priv_id,
            proving_key: chunk_pk,
        };
        let chunk_preparer = ChunkPreparer {
            verif_key: chunk_vk.clone(),
        };
        let agg_chunk_prover = AggChunkProver {
            priv_id,
            circuit_verif_key: chunk_vk.clone(),
            agg_proving_key: agg_chunk_pk.clone(),
        };
        let agg_chunk_verifier = AggChunkVerifier {
            circuit_verif_key: chunk_vk,
            agg_verif_key: agg_chunk_vk,
        };

        // Prepare all the chunks, then compress them for verification
        let mut prepared_chunks: Vec<PreparedChunk> = blocklist
            .iter()
            .map(|chunk| {
                chunk_preparer
                    .prepare(chunk)
                    .expect("couldn't prepare chunk")
            })
            .collect();
        let blocklist_com = BlocklistCom::from_prepared_chunks(&mut prepared_chunks, &agg_chunk_pk);

        // Start proving things. Start with proving each individual chunk
        let mut chunk_proofs: Vec<ChunkProof> = blocklist
            .iter()
            .map(|chunk| {
                chunk_prover
                    .prove(&mut rng, chunk)
                    .expect("couldn't prove chunk")
            })
            .collect();
        // Now prove the aggregate
        let agg_chunk_proof = agg_chunk_prover
            .prove(&mut rng, &mut chunk_proofs, &mut prepared_chunks)
            .expect("couldn't prove HiCIAP over chunks");

        assert!(agg_chunk_verifier
            .verify(blocklist_com, &agg_chunk_proof)
            .expect("couldn't verify agg chunk proof"));
    }
}
