use crate::{
    util::{
        enforce_one_hot, fr_to_fs, to_canonical_bytes, BlsFr, BlsFrV, GetAffineCoords, PoseidonCtx,
        PoseidonCtxVar,
    },
    PrivateId, PrivateIdVar,
};

use core::iter;

use ark_ec::ProjectiveCurve;
use ark_ed_on_bls12_381::{constraints::EdwardsVar as JubjubVar, EdwardsProjective as Jubjub};
use ark_ff::{Field, PrimeField, UniformRand};
use ark_r1cs_std::{
    alloc::AllocVar, bits::ToBitsGadget, boolean::Boolean, eq::EqGadget, groups::CurveVar, R1CSVar,
};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::rand::{CryptoRng, Rng, RngCore};

type JubjubFr = <Jubjub as ProjectiveCurve>::ScalarField;
#[derive(Clone)]
pub struct SchnorrPrivkey(JubjubFr);
#[derive(Clone, Default)]
pub struct SchnorrPubkey(pub(crate) Jubjub);
#[derive(Clone)]
pub(crate) struct SchnorrPubkeyVar(JubjubVar);
#[derive(Clone, Default)]
pub struct SchnorrSignature {
    /// Challenge
    e: JubjubFr,
    /// Response to challenge
    s: JubjubFr,
}
#[derive(Clone)]
pub(crate) struct SchnorrSignatureVar {
    /// Challenge
    e: BlsFrV,
    /// Response to challenge
    s: BlsFrV,
}

impl SchnorrSignatureVar {
    pub(crate) fn new_witness(
        cs: impl Into<Namespace<BlsFr>>,
        sig: &SchnorrSignature,
    ) -> Result<SchnorrSignatureVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        // Signatures are Jubjub scalars. In order to use them in the circuit we need to embed them
        // into the Jubjub's scalar field (which is at least as big as the Jubjub scalar field, so
        // this is injective)
        let lifted_s = fr_to_fs::<Jubjub, BlsFr>(sig.s);
        let lifted_e = fr_to_fs::<Jubjub, BlsFr>(sig.e);

        // Construct the lifted signature
        let s_var = BlsFrV::new_witness(ns!(cs, "sig s var"), || Ok(lifted_s))?;
        let e_var = BlsFrV::new_witness(ns!(cs, "sig e var"), || Ok(lifted_e))?;

        Ok(SchnorrSignatureVar { e: e_var, s: s_var })
    }
}

impl SchnorrPubkey {
    /// Function for generating random pubkeys. Not useful outside of testing
    #[cfg(test)]
    pub(crate) fn gen<R: Rng + ?Sized + CryptoRng>(rng: &mut R) -> SchnorrPubkey {
        From::from(&SchnorrPrivkey::gen(rng))
    }
}

impl<'a> From<&'a SchnorrPrivkey> for SchnorrPubkey {
    fn from(privkey: &'a SchnorrPrivkey) -> SchnorrPubkey {
        // g^privkey is the pubkey
        let g = Jubjub::prime_subgroup_generator();
        let pubkey = g.mul(privkey.0.into_repr());
        SchnorrPubkey(pubkey)
    }
}

impl SchnorrPrivkey {
    pub(crate) fn gen<R: Rng + ?Sized + CryptoRng>(rng: &mut R) -> SchnorrPrivkey {
        SchnorrPrivkey(JubjubFr::rand(rng))
    }

    /// Signs the given message under `privkey`. Return value is `(s, e)` where (using sigma
    /// protocol terminology) `e` is the challenge and `s` is the response.
    pub(crate) fn sign<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        msg: &BlsFr,
    ) -> SchnorrSignature {
        let hash_ctx = PoseidonCtx::new();

        // g is the public generator
        // k is the secret nonce
        // g^k is the commitment
        let g = Jubjub::prime_subgroup_generator();
        let k = JubjubFr::rand(rng);
        let com = g.mul(k.into_repr());

        // e is H(com || msg)
        let mut hash_input = com.affine_coords();
        hash_input.push(*msg);
        let digest = hash_ctx.digest(&hash_input);

        // The hash function outputs a Jubjub base field element, which we can't use as a Jubjub
        // scalar. So we convert it to bytes and truncate it to as many bits as a ScalarField
        // element can hold
        let e = {
            let mut digest_bytes = to_canonical_bytes(digest).unwrap();

            // We only want the first floor(log2(p)) bits of e, where r is the prime order of the
            // scalar field. We do this by finding how many bytes are needed to represent r,
            // truncating e to that many bytes, and then bitmasking the most significant byte of e
            // to be less than the most significant byte of r.
            let r_bitlen = JubjubFr::size_in_bits();

            // Calculate the index of the most significant byte in a scalar field element. Then
            // truncate the digest to be precisely this length. The truncated bytes still might
            // exceed r, so we're gonna bitmask the most significant byte
            let r_msb_pos = (r_bitlen - 1) / 8;
            let truncated_bytes = &mut digest_bytes[..r_msb_pos + 1];

            // The bitlength of the most significant byte of r
            let r_msb_bitlen = ((r_bitlen - 1) % 8) + 1;
            // This bitmask will mask the most significant bit of the most significant byte of r
            let msb_bitmask = (1 << (r_msb_bitlen - 1)) - 1;

            // Apply the bitmask
            truncated_bytes[r_msb_pos] &= msb_bitmask;

            // The truncated bytes now represent an integer that's less than r. This cannot fail.
            JubjubFr::from_random_bytes(&*truncated_bytes)
                .expect("couldn't convert BaseField elem to ScalarField elem")
        };

        // s is k - e * privkey
        let s = k - (e * self.0);

        SchnorrSignature { e, s }
    }

    /// Issues the given credential commitment by signing it and returning the signature
    pub fn issue<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        issuance_req: &IssuanceReq,
    ) -> SchnorrSignature {
        self.sign(rng, &issuance_req.0)
    }
}

impl SchnorrPubkeyVar {
    pub(crate) fn new_input(
        cs: impl Into<Namespace<BlsFr>>,
        pk: &SchnorrPubkey,
    ) -> Result<SchnorrPubkeyVar, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        let aff_pk = pk.0.into_affine();
        JubjubVar::new_input(cs, || Ok(aff_pk)).map(SchnorrPubkeyVar)
    }

    /// Verifies the given (message, signature) pair under the given public key. All this is done in
    /// zero-knowledge.
    /// The signature is expected to have been embedded from (Fr, Fr) to (Fq, Fq). The reason we do
    /// this is because doing that map in ZK is cumbersome and unnecessary.
    pub fn verify(
        &self,
        msg: BlsFrV,
        sig: SchnorrSignatureVar,
    ) -> Result<Boolean<BlsFr>, SynthesisError> {
        let cs = self.0.cs().or(msg.cs()).or(sig.e.cs()).or(sig.s.cs());

        // Witness the group generator. This is the same across all signatures
        let g = Jubjub::prime_subgroup_generator();
        let gv = JubjubVar::new_constant(ns!(cs, "Jubjub gen"), g)?;

        // The signature is (s, e)
        // r is g^s pubkey^e
        let SchnorrSignatureVar { e, s } = sig;
        let r = {
            // Computs g^s
            let s_bits = s.to_bits_le()?;
            let g_s = gv.scalar_mul_le(s_bits.iter())?;
            // Compute pubkey^e
            let e_bits = e.to_bits_le()?;
            let pubkey_e = self.0.scalar_mul_le(e_bits.iter())?;

            // Add them
            g_s + pubkey_e
        };

        // e' is H(r || msg). This should be equal to the given e, up to Fr::size() many bits
        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;
        let mut hash_input = r.affine_coords();
        hash_input.push(msg);
        let e_prime = hash_ctx.digest(&hash_input)?;

        // Show that e' and e agree for all the bits up to the bitlength of the scalar field's modulus.
        // We check the truncation because we have to use the truncation of e as a scalar field element
        // (since e is naturally a base field element and too big to be a scalar field element).
        let e_prime_bits = e_prime.to_bits_le()?;
        let e_bits = e.to_bits_le()?;
        let scalar_mod_bitlen = JubjubFr::size_in_bits();
        let is_equal =
            e_prime_bits[..scalar_mod_bitlen - 1].is_eq(&e_bits[..scalar_mod_bitlen - 1])?;

        // Return whether this verified
        Ok(is_equal)
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
/// An issuance request contains just a Poseidon commitment to the credential
pub struct IssuanceReq(BlsFr);

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Default)]
/// The opening to a private ID commitment
pub struct IssuanceOpening(pub(crate) BlsFr);

impl PrivateId {
    /// Constructs an issuance request for this private ID. Returns the secret opening for the
    /// request, to be used in later issuance proofs.
    pub fn request_issuance<R: CryptoRng + RngCore>(
        &self,
        rng: &mut R,
    ) -> (IssuanceReq, IssuanceOpening) {
        let hash_ctx = PoseidonCtx::new();

        // Make a random commitment to this private ID
        let priv_id_opening = BlsFr::rand(rng);
        let com = hash_ctx.com(self.0, priv_id_opening);

        (IssuanceReq(com), IssuanceOpening(priv_id_opening))
    }
}

/// A circuit which proves the statement "I know the opening to a commitment C on private ID K.
/// Further, I know a signature over C which is signed by a public key in list L".
#[derive(Clone)]
pub(crate) struct OneofNSchnorrVerifyCircuit {
    // Hidden common inputs //
    pub priv_id: PrivateId,
    // Public inputs //
    // The set of verifier keys that could have signed a commitment to msg
    pub pubkeys: Vec<SchnorrPubkey>,
    // Private inputs //
    // The one-hot encoding of the pubkey being used for verification
    pub pubkey_selector: Vec<bool>,
    // The opnening to a commitment to priv_id
    pub priv_id_opening: IssuanceOpening,
    // A signature over Com(priv_id; com_opening) wrt the pubkey selected by pubkey_selector
    pub sig: SchnorrSignature,
}

impl OneofNSchnorrVerifyCircuit {
    /// Constructs a verification circuit given a list of pubkeys, the index of the pubkey that was
    /// used to sign the private ID commitment, the private ID, and the signature
    pub fn new(
        pubkeys: Vec<SchnorrPubkey>,
        signers_pubkey_idx: u16,
        priv_id: PrivateId,
        priv_id_opening: IssuanceOpening,
        sig: SchnorrSignature,
    ) -> OneofNSchnorrVerifyCircuit {
        // Signer's index must be valid
        assert!(
            (signers_pubkey_idx as usize) < pubkeys.len(),
            "signer's pubkey index must be a valid index into the vector of pubkeys"
        );

        // Make a one-hot encoding of signers_pubkey_idx
        let mut pubkey_selector = vec![false; pubkeys.len()];
        pubkey_selector[signers_pubkey_idx as usize] = true;

        OneofNSchnorrVerifyCircuit {
            pubkeys,
            pubkey_selector,
            priv_id,
            priv_id_opening,
            sig,
        }
    }

    /// Returns a placeholder circuit where only `num_pubkeys` is set. This is used for circuit
    /// parameter generation.
    pub(crate) fn new_placeholder(num_pubkeys: usize) -> OneofNSchnorrVerifyCircuit {
        OneofNSchnorrVerifyCircuit {
            pubkeys: vec![SchnorrPubkey::default(); num_pubkeys],
            pubkey_selector: vec![false; num_pubkeys],
            priv_id: PrivateId::default(),
            priv_id_opening: IssuanceOpening::default(),
            sig: SchnorrSignature::default(),
        }
    }

    pub(crate) fn generate_constraints_preallocated(
        priv_id_var: PrivateIdVar,
        pubkey_vars: Vec<SchnorrPubkeyVar>,
        sig_var: SchnorrSignatureVar,
        priv_id_opening_var: BlsFrV,
        pubkey_selector_var: Vec<Boolean<BlsFr>>,
        hash_ctx: PoseidonCtxVar,
    ) -> Result<(), SynthesisError> {
        // Calculate the commitment com = H(nonce || msg). This is the thing that was signed by the
        // issuer
        let com_var = hash_ctx.com(priv_id_var.0, priv_id_opening_var)?;

        // Ensure that the encoding has exactly 1 bit set
        enforce_one_hot(&pubkey_selector_var)?;

        // Now compute the verification pubkey by dotting the selector with the list of pubkeys.
        // Since the selector is the one-hot encoding of signers_pubkey_idx, the final result will
        // be selected_pubkey == pubkeys[signers_pubkey_idx].
        let mut selected_pubkey = SchnorrPubkeyVar(JubjubVar::zero());
        for (bit, pubkey) in pubkey_selector_var.iter().zip(pubkey_vars.iter()) {
            selected_pubkey.0 += pubkey.0.scalar_mul_le(iter::once(bit))?;
        }

        // Assert that the signature verifies under the selected pubkey
        let is_valid = selected_pubkey.verify(com_var, sig_var)?;
        is_valid.enforce_equal(&Boolean::constant(true))
    }
}

impl ConstraintSynthesizer<BlsFr> for OneofNSchnorrVerifyCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        // Get the public inputs
        let priv_id_var = PrivateIdVar::new_input(ns!(cs, "priv_id var"), &self.priv_id)?;
        let pubkey_vars = self
            .pubkeys
            .iter()
            .map(|pk| SchnorrPubkeyVar::new_input(ns!(cs, "pubkey var"), pk))
            .collect::<Result<Vec<SchnorrPubkeyVar>, _>>()?;

        // Witness the hidden inputs
        let sig_var = SchnorrSignatureVar::new_witness(ns!(cs, "sig var"), &self.sig)?;
        let priv_id_opening_var = BlsFrV::new_witness(ns!(cs, "priv_id opening var"), || {
            Ok(self.priv_id_opening.0)
        })?;
        let pubkey_selector_var = self
            .pubkey_selector
            .iter()
            .map(|b| Boolean::new_witness(ns!(cs, "pubkey var"), || Ok(b)))
            .collect::<Result<Vec<Boolean<BlsFr>>, _>>()?;

        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        Self::generate_constraints_preallocated(
            priv_id_var,
            pubkey_vars,
            sig_var,
            priv_id_opening_var,
            pubkey_selector_var,
            hash_ctx,
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{test_util::rand_schnorr_verify_circuit, PrivateId};

    use ark_ff::UniformRand;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    // Just checks that Schnorr signing doesn't panic
    #[test]
    fn test_sign() {
        // Try signing 100 times with different randomness. There used to be an issue where the
        // value of e was invalid and it would panic some of the time. So now we run the test a lot
        // of times.
        for seed in 0..100 {
            // Make a random privkey and message
            let mut rng = StdRng::seed_from_u64(seed);
            let privkey = SchnorrPrivkey::gen(&mut rng);
            let msg = BlsFr::rand(&mut rng);

            // Sign the random message under the random privkey
            privkey.sign(&mut rng, &msg);
        }
    }

    // Tests that the verification circuit is satisfied iff the signature is valid
    #[test]
    fn test_verify() -> Result<(), SynthesisError> {
        let num_pubkeys = 10;

        for seed in 0..10 {
            let mut rng = StdRng::seed_from_u64(seed);

            let priv_id = PrivateId::gen(&mut rng);

            let (circuit, _) = rand_schnorr_verify_circuit(&mut rng, priv_id, num_pubkeys);
            let mut circuit_copy = circuit.clone();

            // Now run the circuit and make sure it verifies
            let cs = ConstraintSystem::<BlsFr>::new_ref();
            circuit.generate_constraints(cs.clone()).unwrap();
            assert!(cs.is_satisfied()?);

            // Now change the signature and assert that it does not verify. Pick a random e.
            let old_s = circuit_copy.sig.clone().s;
            let new_e = JubjubFr::rand(&mut rng);
            let new_sig = SchnorrSignature { s: old_s, e: new_e };
            circuit_copy.sig = new_sig;

            // Now run the circuit and make sure it's false
            let cs = ConstraintSystem::<BlsFr>::new_ref();
            circuit_copy.generate_constraints(cs.clone()).unwrap();
            assert!(!cs.is_satisfied()?);
        }
        Ok(())
    }
}
