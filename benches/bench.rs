use snarkblock::ark_serialize::CanonicalSerialize;
use snarkblock::test_util::{rand_issuance, test_rng};
use snarkblock::{
    agg_chunk_setup, agg_iwf_setup, chunk_setup, issuance_and_wf_setup, AggChunkProver,
    AggChunkVerifier, AggIwfProver, AggIwfVerifier, BlocklistCom, Chunk, ChunkPreparer, ChunkProof,
    ChunkProver, IssuanceAndWfProver, PreparedChunk, PrivateId, SnarkblockProof,
    SnarkblockVerifier,
};

use std::{fs::File, io::Write};

use criterion::{criterion_group, criterion_main, Criterion};
use rayon::prelude::*;

const NUM_CHUNKS_TO_TEST: &[usize] = &[16 - 2, 64 - 2, 256 - 2, 1024 - 2, 4096 - 2, 16384 - 2];
const CHUNK_SIZES_TO_TEST: &[usize] = &[1024, 8192];
const NUM_PUBKEYS_TO_TEST: &[usize] = &[4, 16, 64];

fn iwf_proof(c: &mut Criterion) {
    let mut rng = test_rng();

    // Generate a fresh private ID and make a valid blocklist element
    let priv_id = PrivateId::gen(&mut rng);
    let blocklist_elem = priv_id.gen_blocklist_elem(&mut rng);

    for &num_pubkeys in NUM_PUBKEYS_TO_TEST {
        // Now that the number of pubkeys is set, do the issuance
        let (pubkeys, signers_pubkey_idx, sig, priv_id_opening) =
            rand_issuance(&mut rng, priv_id, num_pubkeys);

        // Set up the IWF provers
        let (iwf_pk, iwf_vk) = issuance_and_wf_setup(&mut rng, num_pubkeys);
        let (agg_iwf_pk, _) = agg_iwf_setup(&mut rng);

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

        c.bench_function(&format!("Proving IWF [np={}]", num_pubkeys), |b| {
            b.iter(|| {
                let base_proof = iwf_prover
                    .prove(&mut rng, blocklist_elem)
                    .expect("couldn't prove base IWF");
                let _agg_proof = agg_iwf_prover
                    .prove(&mut rng, &base_proof)
                    .expect("couldn't prove IWF HICIAP");
            })
        });
    }
}

// This measures the cost of doing up to 14 16-element chunk proofs in parallel, as well as the
// cost of doing just 1 chunk proof of larger sizes
fn chunk_proof(c: &mut Criterion) {
    let mut rng = test_rng();

    // Generate a fresh private ID
    let priv_id = PrivateId::gen(&mut rng);

    // Do the parallel experiments with the 16-elem chunks
    {
        let chunk_size = 16;
        let chunk = Chunk::gen_with_size(&mut rng, chunk_size);

        let (chunk_pk, _) = chunk_setup(&mut rng, chunk_size);
        let chunk_prover = ChunkProver {
            priv_id,
            proving_key: chunk_pk,
        };

        for num_chunks in 1..=14 {
            c.bench_function(
                &format!("Proving {} chunk(s) [cs={}]", num_chunks, chunk_size),
                |b| {
                    b.iter(|| {
                        // Do num_chunks chunk proofs in parallel
                        (0..num_chunks).into_par_iter().for_each(|_| {
                            let mut rng = test_rng();
                            chunk_prover
                                .prove(&mut rng, &chunk)
                                .expect("couldn't prove chunk");
                        })
                    })
                },
            );
        }
    }

    // We need a 256-sized chunk bench for the paper
    {
        let chunk_size = 256;
        let num_chunks = 1;
        let chunk = Chunk::gen_with_size(&mut rng, chunk_size);

        let (chunk_pk, _) = chunk_setup(&mut rng, chunk_size);
        let chunk_prover = ChunkProver {
            priv_id,
            proving_key: chunk_pk,
        };

        c.bench_function(
            &format!("Proving {} chunk(s) [cs={}]", num_chunks, chunk_size),
            |b| {
                b.iter(|| {
                    chunk_prover
                        .prove(&mut rng, &chunk)
                        .expect("couldn't prove chunk");
                })
            },
        );
    }

    // Do the experiments with just 1 chunk of varying size
    for &chunk_size in CHUNK_SIZES_TO_TEST {
        let num_chunks = 1;
        let chunk = Chunk::gen_with_size(&mut rng, chunk_size);

        let (chunk_pk, _) = chunk_setup(&mut rng, chunk_size);
        let chunk_prover = ChunkProver {
            priv_id,
            proving_key: chunk_pk,
        };

        c.bench_function(
            &format!("Proving {} chunk(s) [cs={}]", num_chunks, chunk_size),
            |b| {
                b.iter(|| {
                    chunk_prover
                        .prove(&mut rng, &chunk)
                        .expect("couldn't prove chunk");
                })
            },
        );
    }
}

/// This experiment constructs a blocklist and times how long it takes to prove IWF, the last
/// chunk, and the aggregates thereof. It also computes verification throughput.
///
/// The blocklist is split into head and tail. We call the tail the "buffer" and it consists of 14
/// chunks of size 16. For attestation, we condition on head chunk size and existence of the tail.
/// In the case that the tail exists, the "last chunk" proof is one of size 16. In the case that
/// the tail does not exist, the "last chunk" proof is one of the head chunk size.
///
/// For verification throughput, we measure the time it takes to do 256 buffered verifications in
/// parallel, using the parameters set above.
fn full_attestation(c: &mut Criterion) {
    let mut rng = test_rng();

    // We store snarkblock proof sizes and output them at the end of the bench.
    // The fields are
    //     buffered: bool, indicates whether or not a buffer was used in the blocklist
    //     num_chunks: usize, the number of chunks in the head portion of the blocklist (there is
    //         no tail in the unbuffered case)
    //     chunk_size: usize, the size of the head chunks of the blocklist (there is no tail in the
    //         unbuffered case)
    //     proof_size: The size of the resulting snarkblock proof, in bytes
    let mut proof_sizes: Vec<(bool, usize, usize, usize)> = Vec::new();

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

            // Prove the individual chunks. For brevity we just prove 1 chunk and repeat it
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
                let buf_str = if buffered { "buf" } else { "nobuf" };
                c.bench_function(
                    &format!(
                        "Proving 1 SB attestation [{},nc={},cs={},np={}]",
                        buf_str, num_head_chunks, head_chunk_size, num_pubkeys
                    ),
                    |b| {
                        b.iter(|| {
                            // First do the IWF proof
                            let agg_iwf_proof = {
                                let base_iwf_proof = iwf_prover
                                    .prove(&mut rng, blocklist_elem)
                                    .expect("couldn't prove base IWF");
                                agg_iwf_prover
                                    .prove(&mut rng, &base_iwf_proof)
                                    .expect("couldn't prove IWF HiCIAP")
                            };

                            // Now the aggregate chunk proof(s)
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
                                    agg_iwf_proof,
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
                                    agg_iwf_proof,
                                    vec![agg_head_chunk_proof, agg_tail_chunk_proof],
                                );
                            }
                        })
                    },
                );
            }

            // Now measure buffered verification throughput. Make the proof again
            let agg_head_chunk_proof = agg_head_chunk_prover
                .prove(&mut rng, &mut head_chunk_proofs, &mut prepared_head_chunks)
                .expect("couldn't prove HiCIAP over head chunks");
            let agg_tail_chunk_proof = agg_tail_chunk_prover
                .prove(&mut rng, &mut tail_chunk_proofs, &mut prepared_tail_chunks)
                .expect("couldn't prove HiCIAP over tail chunks");
            let agg_iwf_proof = {
                let base_iwf_proof = iwf_prover
                    .prove(&mut rng, blocklist_elem)
                    .expect("couldn't prove base IWF");
                agg_iwf_prover
                    .prove(&mut rng, &base_iwf_proof)
                    .expect("couldn't prove IWF HiCIAP")
            };

            let buffered_snarkblock_proof = SnarkblockProof::new(
                &mut rng,
                agg_iwf_proof.clone(),
                vec![agg_head_chunk_proof.clone(), agg_tail_chunk_proof],
            );

            // Do a throughput test by verifying 256 proofs in parallel
            c.bench_function(
                &format!(
                    "Verifying 256 SB proofs [buf,nc={},cs={},np={}]",
                    num_head_chunks, head_chunk_size, num_pubkeys
                ),
                |b| {
                    b.iter(|| {
                        (0..256).into_par_iter().for_each(|_| {
                            assert!(snarkblock_verifier
                                .verify(
                                    vec![blocklist_head_com.clone(), blocklist_tail_com.clone()],
                                    &blocklist_elem,
                                    buffered_snarkblock_proof.clone(),
                                )
                                .unwrap());
                        })
                    })
                },
            );

            // Do a latency test by verifying just 1 proof
            c.bench_function(
                &format!(
                    "Verifying 1 SB proof [buf,nc={},cs={},np={}]",
                    num_head_chunks, head_chunk_size, num_pubkeys
                ),
                |b| {
                    b.iter(|| {
                        assert!(snarkblock_verifier
                            .verify(
                                vec![blocklist_head_com.clone(), blocklist_tail_com.clone()],
                                &blocklist_elem,
                                buffered_snarkblock_proof.clone(),
                            )
                            .unwrap());
                    })
                },
            );

            // Finally, save the size of an unbuffered and buffered snarkblock proof. First
            // compute an unbuffered one
            let unbuffered_snarkblock_proof =
                SnarkblockProof::new(&mut rng, agg_iwf_proof, vec![agg_head_chunk_proof]);

            // Now save them
            proof_sizes.push((
                true, // Buffered
                num_head_chunks,
                head_chunk_size,
                buffered_snarkblock_proof.serialized_size(),
            ));
            proof_sizes.push((
                false, // Unbuffered
                num_head_chunks,
                head_chunk_size,
                unbuffered_snarkblock_proof.serialized_size(),
            ));
        }
    }

    output_proof_sizes(&proof_sizes);
}

/// Writes the given proof size data to snarkblock_proof_sizes.csv
/// The fields are
///     buffered: bool, indicates whether or not a buffer was used in the blocklist
///     num_chunks: usize, the number of chunks in the head portion of the blocklist (there is no
///         tail in the unbuffered case)
///     chunk_size: usize, the size of the head chunks of the blocklist (there is no tail in the
///         unbuffered case)
///     proof_size: The size of the resulting snarkblock proof, in bytes
fn output_proof_sizes(proof_sizes: &[(bool, usize, usize, usize)]) {
    // Print to console just in case writing fails
    println!("Writing proof sizes {:?}", proof_sizes);

    // Create the file nad write the header
    let mut f = File::create("snarkblock_proof_sizes.csv").expect("couldn't creat CSV file");
    writeln!(f, "buffered,num_chunks,chunk_size,proof_size_in_bytes")
        .expect("couldn't write header");

    // Write all the proof sizes
    for datum in proof_sizes {
        writeln!(f, "{},{},{},{}", datum.0 as u8, datum.1, datum.2, datum.3)
            .expect("couldn't write line");
    }
}

criterion_group!(benches, chunk_proof, iwf_proof, full_attestation);
criterion_main!(benches);
