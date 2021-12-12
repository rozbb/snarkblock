# SNARKBlock: Federated Anonymous Blocklisting from Hidden Common Input Aggregate Proofs

This repo is the Rust implementation of the SNARKBlock anonymous blocklisting system ([paper](https://eprint.iacr.org/2021/1577)). The core functionality of aggregate proofs is provided by the [`hiciap`](https://github.com/rozbb/hiciap) crate.

For example usage, see the `test_snarkblock` test in [`src/api.rs`](src/api.rs). To run benchmarks, execute `bash run_benches.sh` and view the results in `target/criterion/report/index.html`. The script assumes that the benchmarks are running on a modern amd64 architecture.

Warning
-------

This code has not been audited in any sense of the word. Use at your own peril.

License
-------

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
