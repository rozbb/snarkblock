use crate::{
    issuance::{OneofNSchnorrVerifyCircuit, SchnorrPrivkey, SchnorrPubkey},
    util::{BlsFr, PoseidonCtx},
    PrivateId,
};

use ark_ff::{ToConstraintField, UniformRand};
use ark_std::rand::{CryptoRng, Rng};

pub(crate) fn rand_schnorr_verify_circuit<R: Rng + CryptoRng>(
    rng: &mut R,
    priv_id: PrivateId,
    num_pubkeys: usize,
) -> (OneofNSchnorrVerifyCircuit, Vec<BlsFr>) {
    let hash_ctx = PoseidonCtx::new();

    // Generate a signing keypair and sign a commitment to the credential
    let privkey = SchnorrPrivkey::gen(rng);
    let signers_pubkey = (&privkey).into();

    let msg = priv_id.0;
    let com_nonce = BlsFr::rand(rng);
    let com = hash_ctx.com(msg, com_nonce);
    let sig = privkey.sign(rng, &com);

    // Generate some other random pubkeys that did not sign the above message
    let mut pubkeys: Vec<SchnorrPubkey> = (0..num_pubkeys - 1)
        .map(|_| {
            let privkey = SchnorrPrivkey::gen(rng);
            (&privkey).into()
        })
        .collect();

    // Add the signer's pubkey into the list of random pubkeys. Place it at a random index.
    let signers_pubkey_idx = rng.gen_range(0..pubkeys.len() + 1) as u16;
    pubkeys.insert(signers_pubkey_idx as usize, signers_pubkey);

    let circuit =
        OneofNSchnorrVerifyCircuit::new(pubkeys.clone(), signers_pubkey_idx, msg, com_nonce, sig);

    let public_input: Vec<BlsFr> = pubkeys
        .into_iter()
        .flat_map(|pubkey| pubkey.0.to_field_elements().unwrap())
        .collect();

    (circuit, public_input)
}
