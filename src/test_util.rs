use crate::{
    issuance::{
        IssuanceOpening, OneofNSchnorrVerifyCircuit, SchnorrPrivkey, SchnorrPubkey,
        SchnorrSignature,
    },
    util::BlsFr,
    PrivateId,
};

use ark_ff::ToConstraintField;
use ark_std::rand::{rngs::StdRng, CryptoRng, Rng, RngCore, SeedableRng};

pub(crate) fn test_rng() -> StdRng {
    StdRng::seed_from_u64(1337)
}

pub(crate) fn rand_schnorr_verify_circuit<R: CryptoRng + RngCore>(
    rng: &mut R,
    priv_id: PrivateId,
    num_pubkeys: usize,
) -> (OneofNSchnorrVerifyCircuit, Vec<BlsFr>) {
    let (pubkeys, signers_pubkey_idx, sig, priv_id_opening) =
        rand_issuance(rng, priv_id, num_pubkeys);

    let circuit = OneofNSchnorrVerifyCircuit::new(
        pubkeys.clone(),
        signers_pubkey_idx,
        priv_id,
        priv_id_opening,
        sig,
    );

    let public_input: Vec<BlsFr> = pubkeys
        .into_iter()
        .flat_map(|pubkey| pubkey.0.to_field_elements().unwrap())
        .collect();

    (circuit, public_input)
}

/// Makes a random list of public keys, uses one of them to sign the private ID, and returns the
/// list, the signature, the index of the signing pubkey, and the private ID commitment opening
pub(crate) fn rand_issuance<R: CryptoRng + RngCore>(
    rng: &mut R,
    priv_id: PrivateId,
    num_pubkeys: usize,
) -> (Vec<SchnorrPubkey>, u16, SchnorrSignature, IssuanceOpening) {
    // Generate a signing keypair and sign a commitment to the private ID
    let privkey = SchnorrPrivkey::gen(rng);
    let signers_pubkey = From::from(&privkey);
    let (req, priv_id_opening) = priv_id.request_issuance(rng);
    let sig = privkey.issue(rng, &req);

    // Generate some other random pubkeys that did not sign the commitment
    let mut pubkeys: Vec<SchnorrPubkey> = (0..num_pubkeys - 1)
        .map(|_| SchnorrPubkey::gen(rng))
        .collect();

    // Add the signer's pubkey into the list of random pubkeys. Place it at a random index.
    let signers_pubkey_idx = rng.gen_range(0..pubkeys.len() + 1) as u16;
    pubkeys.insert(signers_pubkey_idx as usize, signers_pubkey);

    (pubkeys, signers_pubkey_idx, sig, priv_id_opening)
}
