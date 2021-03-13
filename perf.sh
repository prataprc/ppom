#! /usr/bin/env bash

exec > perf.out
exec 2>&1

set -o xtrace

PERF=$HOME/.cargo/target/release/perf

date; time cargo +nightly bench || exit $?

date; time cargo run --release --bin perf --features=perf -- --loads 1000000 --readers 2 --writers 1 --gets 10000 --dels 10000 --sets 10000 || exit $?
date; valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes $PERF --loads 1000000 --readers 2 --writers 1 --gets 10000 --dels 10000 --sets 10000 || exit $?
