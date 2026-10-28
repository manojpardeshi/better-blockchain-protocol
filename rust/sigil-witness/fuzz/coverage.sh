#!/usr/bin/env bash
# Line/region coverage of rust/sigil-witness/src reached by each target's corpus.
#
#   fuzz/coverage.sh [target...]
#
# Needs `rustup component add llvm-tools-preview --toolchain nightly`.
set -euo pipefail
cd "$(dirname "$0")"
targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
    targets=(json_roundtrip locks_eval proofs_verify witness_ops witness_http_body)
fi
llvm="$(rustc +nightly --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin"
for t in "${targets[@]}"; do
    cargo +nightly fuzz coverage "$t" "corpus/$t" >/dev/null 2>&1
    bin="target/x86_64-unknown-linux-gnu/coverage/x86_64-unknown-linux-gnu/release/$t"
    prof="coverage/$t/coverage.profdata"
    echo "== $t"
    "$llvm/llvm-cov" report "$bin" -instr-profile="$prof" \
        -ignore-filename-regex='(\.cargo|rustc|proofs/|fuzz_targets/)' | tail -n 14
done
