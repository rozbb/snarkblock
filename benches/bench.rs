use snarkblock::test_util::{rand_issuance, test_rng};
use snarkblock::{
    agg_chunk_setup, agg_iwf_setup, chunk_setup, issuance_and_wf_setup, AggChunkProver,
    AggChunkVerifier, AggIwfProver, AggIwfVerifier, BlocklistCom, Chunk, ChunkPreparer, ChunkProof,
    ChunkProver, IssuanceAndWfProver, PreparedChunk, PrivateId, SnarkblockProof,
    SnarkblockVerifier,
};

use criterion::{criterion_group, criterion_main, Criterion};
use rayon::prelude::*;

const NUM_CHUNKS_TO_TEST: &[usize] = &[16 - 2, 64 - 2, 256 - 2, 1024 - 2, 4096 - 2, 16384 - 2];
const CHUNK_SIZES_TO_TEST: &[usize] = &[1024, 8192];

/// This experiment constructs a blocklist and times how long it takes to prove IWF, the last
/// chunk, and the aggregates thereof. The blocklist is split into head and tail. We call the tail
/// the "buffer" and it consists of 14 chunks of size 16. We condition on head chunk size and
/// existence of the tail. In the case that the tail exists, the "last chunk" proof is one of size
/// 16. In the case that the tail does not exist, the "last chunk" proof is one of the head chunk
/// size.
fn full_attestation(c: &mut Criterion) {
    let mut rng = test_rng();

    // The the buffer is always 14 chunks of size 16
    let tail_chunk_size = 16;
    let num_tail_chunks = 14;

    // This doesn't matter much. Chunk proofs dominate attestation time by far
    let num_pubkeys = 16;

    // Generate a fresh private ID, make a valid blocklist element, and do the issuance
    let priv_id = PrivateId::gen(&mut rng);
    let blocklist_elem = priv_id.gen_blocklist_elem(&mut rng);
    let (pubkeys, signers_pubkey_idx, sig, priv_id_opening) =
        rand_issuance(&mut rng, priv_id, num_pubkeys);

    for &head_chunk_size in CHUNK_SIZES_TO_TEST {
        for &num_head_chunks in NUM_CHUNKS_TO_TEST {
            // Generate a fresh blocklist. For brevity we repeat the same chunk many times
            let blocklist_head_chunk = Chunk::gen_with_size(&mut rng, head_chunk_size);
            let blocklist_tail_chunk = Chunk::gen_with_size(&mut rng, tail_chunk_size);

            // Do all the setups
            let (iwf_pk, iwf_vk) = issuance_and_wf_setup(&mut rng, num_pubkeys);
            let (agg_iwf_pk, agg_iwf_vk) = agg_iwf_setup(&mut rng);
            let (head_chunk_pk, head_chunk_vk) = chunk_setup(&mut rng, head_chunk_size);
            let (tail_chunk_pk, tail_chunk_vk) = chunk_setup(&mut rng, tail_chunk_size);
            let (agg_head_chunk_pk, agg_head_chunk_vk) = agg_chunk_setup(&mut rng, num_head_chunks);
            let (agg_tail_chunk_pk, agg_tail_chunk_vk) = agg_chunk_setup(&mut rng, num_tail_chunks);

            let iwf_prover = IssuanceAndWfProver {
                priv_id,
                pubkeys: pubkeys.clone(),
                signers_pubkey_idx,
                priv_id_opening: priv_id_opening.clone(),
                sig: sig.clone(),
                proving_key: iwf_pk,
            };
            let agg_iwf_prover = AggIwfProver {
                priv_id,
                circuit_verif_key: iwf_vk.clone(),
                agg_proving_key: agg_iwf_pk,
            };
            let agg_iwf_verifier = AggIwfVerifier {
                pubkeys: pubkeys.clone(),
                circuit_verif_key: iwf_vk,
                agg_verif_key: agg_iwf_vk,
            };
            let head_chunk_prover = ChunkProver {
                priv_id,
                proving_key: head_chunk_pk,
            };
            let tail_chunk_prover = ChunkProver {
                priv_id,
                proving_key: tail_chunk_pk,
            };
            let head_chunk_preparer = ChunkPreparer {
                verif_key: head_chunk_vk.clone(),
            };
            let tail_chunk_preparer = ChunkPreparer {
                verif_key: tail_chunk_vk.clone(),
            };
            let agg_head_chunk_prover = AggChunkProver {
                priv_id,
                circuit_verif_key: head_chunk_vk.clone(),
                agg_proving_key: agg_head_chunk_pk.clone(),
            };
            let agg_tail_chunk_prover = AggChunkProver {
                priv_id,
                circuit_verif_key: tail_chunk_vk.clone(),
                agg_proving_key: agg_tail_chunk_pk.clone(),
            };
            let agg_head_chunk_verifier = AggChunkVerifier {
                circuit_verif_key: head_chunk_vk,
                agg_verif_key: agg_head_chunk_vk,
            };
            let agg_tail_chunk_verifier = AggChunkVerifier {
                circuit_verif_key: tail_chunk_vk,
                agg_verif_key: agg_tail_chunk_vk,
            };
            let snarkblock_verifier = SnarkblockVerifier {
                agg_chunk_verifiers: vec![agg_head_chunk_verifier, agg_tail_chunk_verifier],
                agg_iwf_verifier,
            };

            // Prepare all the head and tail chunks for verification. For brevity, we prepare 1 chunk and
            // repeat it.
            let mut prepared_head_chunks: Vec<PreparedChunk> = {
                let prepared_chunk = head_chunk_preparer
                    .prepare(&blocklist_head_chunk)
                    .expect("couldn't prepare chunk");
                vec![prepared_chunk; num_head_chunks]
            };
            let mut prepared_tail_chunks: Vec<PreparedChunk> = {
                let prepared_chunk = tail_chunk_preparer
                    .prepare(&blocklist_tail_chunk)
                    .expect("couldn't prepare chunk");
                vec![prepared_chunk; num_tail_chunks]
            };

            // Commit to the blocklist parts for verification
            let blocklist_head_com =
                BlocklistCom::from_prepared_chunks(&mut prepared_head_chunks, &agg_head_chunk_pk);
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
            let mut head_chunk_proofs: Vec<ChunkProof> = {
                let proof = head_chunk_prover
                    .prove(&mut rng, &blocklist_head_chunk)
                    .expect("couldn't prove chunk");
                vec![proof; num_head_chunks]
            };
            let mut tail_chunk_proofs: Vec<ChunkProof> = {
                let proof = tail_chunk_prover
                    .prove(&mut rng, &blocklist_tail_chunk)
                    .expect("couldn't prove chunk");
                vec![proof; num_tail_chunks]
            };

            for buffered in [true, false] {
                let buf_str = if buffered { "Buffered" } else { "Unbuffered" };
                c.bench_function(
                    &format!(
                        "{} e2e with {} many {}-elem head chunks",
                        buf_str, num_head_chunks, head_chunk_size
                    ),
                    |b| {
                        b.iter(|| {
                            if !buffered {
                                // If unbuffered, compute a head chunk. There is no tail
                                let head_chunk_proof = head_chunk_prover
                                    .prove(&mut rng, &blocklist_head_chunk)
                                    .expect("couldn't prove chunk");
                                *head_chunk_proofs.last_mut().unwrap() = head_chunk_proof;

                                // Now compute the aggregate
                                let agg_head_chunk_proof = agg_head_chunk_prover
                                    .prove(
                                        &mut rng,
                                        &mut head_chunk_proofs,
                                        &mut prepared_head_chunks,
                                    )
                                    .expect("couldn't prove HiCIAP over head chunks");

                                let _snarkblock_proof = SnarkblockProof::new(
                                    &mut rng,
                                    agg_iwf_proof.clone(),
                                    vec![agg_head_chunk_proof],
                                );
                            } else {
                                // If buffered, compute a tail chunk
                                let tail_chunk_proof = tail_chunk_prover
                                    .prove(&mut rng, &blocklist_tail_chunk)
                                    .expect("couldn't prove chunk");
                                *tail_chunk_proofs.last_mut().unwrap() = tail_chunk_proof;

                                // Now aggregate head and tail
                                let agg_head_chunk_proof = agg_head_chunk_prover
                                    .prove(
                                        &mut rng,
                                        &mut head_chunk_proofs,
                                        &mut prepared_head_chunks,
                                    )
                                    .expect("couldn't prove HiCIAP over head chunks");
                                let agg_tail_chunk_proof = agg_tail_chunk_prover
                                    .prove(
                                        &mut rng,
                                        &mut tail_chunk_proofs,
                                        &mut prepared_tail_chunks,
                                    )
                                    .expect("couldn't prove HiCIAP over tail chunks");

                                let _snarkblock_proof = SnarkblockProof::new(
                                    &mut rng,
                                    agg_iwf_proof.clone(),
                                    vec![agg_head_chunk_proof, agg_tail_chunk_proof],
                                );
                            }
                        })
                    },
                );
            }

            // Just make sure that we're still producing valid proofs. Make a buffered one and verify it
            let agg_head_chunk_proof = agg_head_chunk_prover
                .prove(&mut rng, &mut head_chunk_proofs, &mut prepared_head_chunks)
                .expect("couldn't prove HiCIAP over head chunks");
            let agg_tail_chunk_proof = agg_tail_chunk_prover
                .prove(&mut rng, &mut tail_chunk_proofs, &mut prepared_tail_chunks)
                .expect("couldn't prove HiCIAP over tail chunks");

            let snarkblock_proof = SnarkblockProof::new(
                &mut rng,
                agg_iwf_proof,
                vec![agg_head_chunk_proof, agg_tail_chunk_proof],
            );

            assert!(snarkblock_verifier
                .verify(
                    vec![blocklist_head_com, blocklist_tail_com],
                    &blocklist_elem,
                    snarkblock_proof
                )
                .unwrap());
        }
    }
}

criterion_group!(benches, full_attestation);
criterion_main!(benches);
