#!/bin/sh
# Build and run the Plonky2 PCD prototype; results go to research/results/.
# Needs a nightly Rust toolchain (plonky2_field uses #![feature(specialization)]).
set -e
here=$(cd "$(dirname "$0")" && pwd)
out="$here/../results"
hops=${1:-16}
cargo +nightly build --release --manifest-path "$here/Cargo.toml"
"$here/target/release/sigil-plonky2-pcd" --no-zk --hops "$hops" > "$out/plonky2_pcd_nozk_${hops}hops.txt" 2>&1
"$here/target/release/sigil-plonky2-pcd" --hops "$hops" > "$out/plonky2_pcd_zk_${hops}hops.txt" 2>&1
grep RESULT "$out"/plonky2_pcd_*_"${hops}"hops.txt
