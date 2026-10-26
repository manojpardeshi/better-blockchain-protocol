#!/usr/bin/env bash
# Run one or all fuzz targets for a while and print libFuzzer's final stats.
#
#   fuzz/run.sh [seconds] [target...]      (default: 60 s, every target)
#
# Needs a nightly toolchain and cargo-fuzz (`cargo install cargo-fuzz`). Seeds for the
# byte-level targets: `cargo run --release --manifest-path proofs/Cargo.toml --bin gen_seeds -- fuzz/corpus`.
# Crashes land in fuzz/artifacts/<target>/; reproduce with
#   cargo +nightly fuzz run -O <target> fuzz/artifacts/<target>/<file>
# Pass FUZZ_FLAGS=--no-default-features to stop skipping inputs that hit known bugs.
set -euo pipefail
cd "$(dirname "$0")"
secs="${1:-60}"
shift || true
targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
    targets=(json_roundtrip locks_eval proofs_verify witness_ops witness_http_body)
fi
mkdir -p logs
for t in "${targets[@]}"; do
    mkdir -p "corpus/$t"
    log="logs/$t.log"
    set +e
    cargo +nightly fuzz run ${FUZZ_FLAGS:-} -O "$t" "corpus/$t" -- \
        -max_total_time="$secs" -rss_limit_mb=4096 -print_final_stats=1 >"$log" 2>&1
    code=$?
    set -e
    echo "== $t (exit $code)"
    grep -E "^#[0-9]+" "$log" | tail -1 || true
    grep -E "stat::number_of_executed_units|stat::peak_rss_mb|panicked|SUMMARY|Test unit written" "$log" || true
done
