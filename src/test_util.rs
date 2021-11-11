use crate::{
    issuance::{OneofNSchnorrVerifyCircuit, SchnorrPrivkey, SchnorrPubkey},
    util::BlsFr,
    PrivateId,
};

use ark_ff::ToConstraintField;
use ark_std::rand::{rngs::StdRng, CryptoRng, Rng, SeedableRng};

pub(crate) fn test_rng() -> StdRng {
    StdRng::seed_from_u64(1337)
}

pub(crate) fn rand_schnorr_verify_circuit<R: Rng + CryptoRng>(
    rng: &mut R,
    priv_id: PrivateId,
    num_pubkeys: usize,
) -> (OneofNSchnorrVerifyCircuit, Vec<BlsFr>) {
    // Generate a signing keypair and sign a commitment to the credential
    let privkey = SchnorrPrivkey::gen(rng);
    let signers_pubkey = (&privkey).into();

    let (req, priv_id_opening) = priv_id.request_issuance(rng);
    let sig = privkey.issue(rng, &req);

    // Generate some other random pubkeys that did not sign the commitment
    let mut pubkeys: Vec<SchnorrPubkey> = (0..num_pubkeys - 1)
        .map(|_| {
            let privkey = SchnorrPrivkey::gen(rng);
            (&privkey).into()
        })
        .collect();

    // Add the signer's pubkey into the list of random pubkeys. Place it at a random index.
    let signers_pubkey_idx = rng.gen_range(0..pubkeys.len() + 1) as u16;
    pubkeys.insert(signers_pubkey_idx as usize, signers_pubkey);

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
