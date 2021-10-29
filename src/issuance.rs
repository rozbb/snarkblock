use crate::util::{
    enforce_one_hot, fr_to_fs, to_canonical_bytes, BlsFr, BlsFrV, GetAffineCoords, PoseidonCtx,
    PoseidonCtxVar,
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
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_std::rand::{CryptoRng, Rng, RngCore};

type JubjubFr = <Jubjub as ProjectiveCurve>::ScalarField;
#[derive(Clone)]
pub(crate) struct SchnorrPrivkey(JubjubFr);
#[derive(Clone)]
pub(crate) struct SchnorrPubkey(pub(crate) Jubjub);
#[derive(Clone)]
pub(crate) struct SchnorrPubkeyVar(JubjubVar);
#[derive(Clone)]
pub(crate) struct SchnorrSignature {
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
}

impl SchnorrPubkeyVar {
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

/// A circuit which proves the statement "I know the opening to a commitment C on message M.
/// Further, I know a signature over C which is signed by a public key in list L".
#[derive(Clone)]
pub(crate) struct OneofNSchnorrVerifyCircuit {
    // Hidden Common Inputs
    pub msg: Option<BlsFr>,
    // Public inputs
    pub num_pubkeys: usize,
    pub pubkeys: Option<Vec<SchnorrPubkey>>,
    // Private inputs
    /// The one-hot encoding of the pubkey being used for verification
    pub pubkey_selector: Option<Vec<bool>>,
    pub com_nonce: Option<BlsFr>,
    pub sig: Option<SchnorrSignature>,
}

impl OneofNSchnorrVerifyCircuit {
    /// Constructs a verification circuit given a list of pubkeys, the index of the pubkey that was
    /// used to sign a message, the message, and the signature
    pub fn new(
        pubkeys: Vec<SchnorrPubkey>,
        signers_pubkey_idx: u16,
        msg: BlsFr,
        com_nonce: BlsFr,
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
            num_pubkeys: pubkeys.len(),
            pubkeys: Some(pubkeys),
            pubkey_selector: Some(pubkey_selector),
            msg: Some(msg),
            com_nonce: Some(com_nonce),
            sig: Some(sig),
        }
    }

    /// Returns a placeholder circuit where only `num_pubkeys` is set. This is used for circuit
    /// parameter generation.
    pub(crate) fn new_placeholder(num_pubkeys: usize) -> OneofNSchnorrVerifyCircuit {
        OneofNSchnorrVerifyCircuit {
            num_pubkeys,
            pubkeys: None,
            pubkey_selector: None,
            msg: None,
            com_nonce: None,
            sig: None,
        }
    }
}

impl OneofNSchnorrVerifyCircuit {
    /// Returns
    ///     com_nonce_var,
    ///     pubkey_vars,
    ///     pubkey_selector_var,
    ///     sig_var,
    pub(crate) fn get_input_vars(
        self,
        cs: &ConstraintSystemRef<BlsFr>,
    ) -> Result<
        (
            BlsFrV,
            Vec<SchnorrPubkeyVar>,
            Vec<Boolean<BlsFr>>,
            SchnorrSignatureVar,
        ),
        SynthesisError,
    > {
        let com_nonce_var = BlsFrV::new_witness(ns!(cs, "com nonce var"), || {
            self.com_nonce.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let pubkey_vars: Vec<SchnorrPubkeyVar> = match self.pubkeys {
            // If we're the prover, witness all the pubkeys into a vector
            Some(pubkeys) => pubkeys
                .iter()
                .map(|pk| pk.0.into_affine())
                .map(|aff_pubkey| JubjubVar::new_input(ns!(cs, "pubkey var"), || Ok(aff_pubkey)))
                .map(|pkv| pkv.map(SchnorrPubkeyVar))
                .collect::<Result<Vec<SchnorrPubkeyVar>, _>>()?,
            // If we're the verifier, create the appropriate number of symbolic pubkey vars
            None => {
                let value_placeholder: Result<Jubjub, _> = Err(SynthesisError::AssignmentMissing);
                (0..self.num_pubkeys)
                    .map(|_| JubjubVar::new_input(ns!(cs, "pubkey var"), || value_placeholder))
                    .map(|pkv| pkv.map(SchnorrPubkeyVar))
                    .collect::<Result<Vec<SchnorrPubkeyVar>, _>>()?
            }
        };

        // Witness the public key selector
        let pubkey_selector_var: Vec<Boolean<BlsFr>> = match self.pubkey_selector {
            // If we're the prover, witness all the bools into a vector
            Some(v) => v
                .iter()
                .map(|bit| Boolean::new_witness(ns!(cs, "selector bit"), || Ok(bit)))
                .collect::<Result<Vec<Boolean<BlsFr>>, _>>()?,
            // Otherwise, construct a vector of the same expected length, using palceholder values
            None => {
                // If we're the verifier, create the appropriate number of symbolic bit vars
                let value_placeholder: Result<bool, _> = Err(SynthesisError::AssignmentMissing);
                (0..self.num_pubkeys)
                    .map(|_| {
                        Boolean::<BlsFr>::new_witness(ns!(cs, "selector bit"), || value_placeholder)
                    })
                    .collect::<Result<Vec<Boolean<BlsFr>>, _>>()?
            }
        };

        // Signatures are Jubjub scalars. In order to use them in the circuit we need to embed them
        // into the Jubjub's scalar field (which is at least as big as the Jubjub scalar field, so
        // this is injective)
        let sig_var = {
            let lifted_s: Result<BlsFr, _> = self
                .sig
                .as_ref()
                .ok_or(SynthesisError::AssignmentMissing)
                .map(|sig| fr_to_fs::<Jubjub, BlsFr>(sig.s));
            let lifted_e: Result<BlsFr, _> = self
                .sig
                .as_ref()
                .ok_or(SynthesisError::AssignmentMissing)
                .map(|sig| fr_to_fs::<Jubjub, BlsFr>(sig.e));

            // Construct the lifted signature
            let s_var = BlsFrV::new_witness(ns!(cs, "sig s var"), || lifted_s)?;
            let e_var = BlsFrV::new_witness(ns!(cs, "sig e var"), || lifted_e)?;
            SchnorrSignatureVar { e: e_var, s: s_var }
        };

        Ok((com_nonce_var, pubkey_vars, pubkey_selector_var, sig_var))
    }
}

impl ConstraintSynthesizer<BlsFr> for OneofNSchnorrVerifyCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<BlsFr>) -> Result<(), SynthesisError> {
        // Check consistency of num_pubkeys wrt the given list
        if let Some(v) = &self.pubkeys {
            assert_eq!(v.len(), self.num_pubkeys);
        }

        // Witness the message
        let msg_var = BlsFrV::new_input(ns!(cs, "msg var"), || {
            self.msg.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Get the rest of the circuit input vars
        let (com_nonce_var, pubkey_vars, pubkey_selector_var, sig_var) =
            self.get_input_vars(&cs)?;

        let hash_ctx = PoseidonCtxVar::new(ns!(cs, "hash ctx"))?;

        // Calculate the commitment com = H(nonce || msg). This is the thing that was signed by the
        // issuer
        let com_var = hash_ctx.com(msg_var, com_nonce_var)?;

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
            let old_s = circuit_copy.sig.clone().unwrap().s;
            let new_e = JubjubFr::rand(&mut rng);
            let new_sig = SchnorrSignature { s: old_s, e: new_e };
            circuit_copy.sig = Some(new_sig);

            // Now run the circuit and make sure it's false
            let cs = ConstraintSystem::<BlsFr>::new_ref();
            circuit_copy.generate_constraints(cs.clone()).unwrap();
            assert!(!cs.is_satisfied()?);
        }
        Ok(())
    }
}
