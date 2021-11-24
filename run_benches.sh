#!/bin/bash

RUSTFLAGS="-C target-feature=+bmi2,+adx" cargo +nightly bench --features "parallel,benchmarking,asm" -- --sample-size 20
