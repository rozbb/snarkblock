use core::iter;

use snarkblock::rand::{rngs::StdRng, SeedableRng};
use snarkblock::test_util::rand_issuance;
use snarkblock::{
    agg_chunk_setup, agg_iwf_setup, chunk_setup, issuance_and_wf_setup, AggChunkProver,
    AggChunkVerifier, AggIwfProver, AggIwfVerifier, BlocklistCom, Chunk, ChunkPreparer, ChunkProof,
    ChunkProver, IssuanceAndWfProver, PreparedChunk, PrivateId, SnarkblockProof,
    SnarkblockVerifier,
};

use criterion::{criterion_group, criterion_main, Criterion};
use rayon::prelude::*;

pub(crate) fn test_rng() -> StdRng {
    StdRng::seed_from_u64(1337)
}

fn snarkblock(c: &mut Criterion) {
    let mut rng = test_rng();
    let chunk_size = 16;
    let num_chunks = 14;
    let num_pubkeys = 16;

    // The the buffer is always 16 chunks of size 16
    let tail_chunk_size = 16;
    let num_tail_chunks = 16;

    // Generate a fresh private ID, make a valid blocklist element, and do the issuance
    let priv_id = PrivateId::gen(&mut rng);
    let blocklist_elem = priv_id.gen_blocklist_elem(&mut rng);
    let (pubkeys, signers_pubkey_idx, sig, priv_id_opening) =
        rand_issuance(&mut rng, priv_id, num_pubkeys);

    // Generate a fresh blocklist. For brevity we repeat the same chunk many times
    let blocklist_chunk = Chunk::gen_with_size(&mut rng, chunk_size);
    let blocklist_tail_chunk = Chunk::gen_with_size(&mut rng, tail_chunk_size);

    // Do all the setups
    let (iwf_pk, iwf_vk) = issuance_and_wf_setup(&mut rng, num_pubkeys);
    let (chunk_pk, chunk_vk) = chunk_setup(&mut rng, chunk_size);
    let (tail_chunk_pk, tail_chunk_vk) = chunk_setup(&mut rng, tail_chunk_size);
    let (agg_iwf_pk, agg_iwf_vk) = agg_iwf_setup(&mut rng);
    let (agg_chunk_pk, agg_chunk_vk) = agg_chunk_setup(&mut rng, num_chunks);
    let (agg_tail_chunk_pk, agg_tail_chunk_vk) = agg_chunk_setup(&mut rng, num_tail_chunks);

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
    let chunk_prover = ChunkProver {
        priv_id,
        proving_key: chunk_pk,
    };
    let tail_chunk_prover = ChunkProver {
        priv_id,
        proving_key: tail_chunk_pk,
    };
    let chunk_preparer = ChunkPreparer {
        verif_key: chunk_vk.clone(),
    };
    let tail_chunk_preparer = ChunkPreparer {
        verif_key: tail_chunk_vk.clone(),
    };
    let agg_chunk_prover = AggChunkProver {
        priv_id,
        circuit_verif_key: chunk_vk.clone(),
        agg_proving_key: agg_chunk_pk.clone(),
    };
    let agg_tail_chunk_prover = AggChunkProver {
        priv_id,
        circuit_verif_key: tail_chunk_vk.clone(),
        agg_proving_key: agg_tail_chunk_pk.clone(),
    };
    let agg_chunk_verifier = AggChunkVerifier {
        circuit_verif_key: chunk_vk,
        agg_verif_key: agg_chunk_vk,
    };
    let agg_tail_chunk_verifier = AggChunkVerifier {
        circuit_verif_key: tail_chunk_vk,
        agg_verif_key: agg_tail_chunk_vk,
    };
    let snarkblock_verifier = SnarkblockVerifier {
        agg_chunk_verifier,
        agg_iwf_verifier,
    };

    // Prepare all the chunks, then compress them for verification. For brevity, we prepare 1 chunk
    // and repeat it.
    let mut prepared_chunks: Vec<PreparedChunk> = {
        let prepared_chunk = chunk_preparer
            .prepare(&blocklist_chunk)
            .expect("couldn't prepare chunk");
        vec![prepared_chunk; num_chunks]
    };
    let blocklist_com = BlocklistCom::from_prepared_chunks(&mut prepared_chunks, &agg_chunk_pk);

    // Do the same thing for the tail
    let mut prepared_tail_chunks: Vec<PreparedChunk> = {
        let prepared_chunk = tail_chunk_preparer
            .prepare(&blocklist_tail_chunk)
            .expect("couldn't prepare chunk");
        vec![prepared_chunk; num_tail_chunks]
    };
    let blocklist_tail_com =
        BlocklistCom::from_prepared_chunks(&mut prepared_tail_chunks, &agg_tail_chunk_pk);

    // Start proving things. Start with the IWF proof
    let base_iwf_proof = iwf_prover
        .prove(&mut rng, blocklist_elem)
        .expect("couldn't prove base IWF");
    let agg_iwf_proof = agg_iwf_prover
        .prove(&mut rng, &base_iwf_proof)
        .expect("couldn't prove IWF HiCIAP");

    // Now prove the individual chunks. For brevity we just prove 1 chunk and repeat it
    let mut chunk_proofs: Vec<ChunkProof> = {
        let proof = chunk_prover
            .prove(&mut rng, &blocklist_chunk)
            .expect("couldn't prove chunk");
        vec![proof; num_chunks]
    };

    // Do the same for the tail
    let mut tail_chunk_proofs: Vec<ChunkProof> = {
        let proof = tail_chunk_prover
            .prove(&mut rng, &blocklist_tail_chunk)
            .expect("couldn't prove chunk");
        vec![proof; num_tail_chunks]
    };

    // Now prove the chunk aggregate and the tail chunk aggregate
    let agg_chunk_proof = agg_chunk_prover
        .prove(&mut rng, &mut chunk_proofs, &mut prepared_chunks)
        .expect("couldn't prove HiCIAP over chunks");
    let agg_tail_chunk_proof = agg_tail_chunk_prover
        .prove(&mut rng, &mut tail_chunk_proofs, &mut prepared_tail_chunks)
        .expect("couldn't prove HiCIAP over chunks");

    // Put it all together and verify it
    let snarkblock_proof = SnarkblockProof::new(
        &mut rng,
        agg_iwf_proof,
        vec![agg_chunk_proof, agg_tail_chunk_proof],
    );
    assert!(snarkblock_verifier
        .verify(
            vec![blocklist_com, blocklist_tail_com],
            &blocklist_elem,
            snarkblock_proof
        )
        .unwrap());
}

criterion_group!(benches, snarkblock);
criterion_main!(benches);
