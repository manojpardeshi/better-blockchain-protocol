#!/usr/bin/env bash
# Model-check the Sigil witness protocol with TLC.
#
#   formal/check.sh                 run every config (safety + mutation test)
#   formal/check.sh MC.cfg ...      run only the given configs
#
# Downloads tla2tools.jar (pinned version + SHA-256) into a cache directory
# on first use; never commits it. Requires java >= 11 and curl.
# Configs named *mutant*.cfg are expected to FAIL with a Safety violation;
# all others must pass. Exit status is non-zero if any expectation is unmet.
set -euo pipefail

TLA_VERSION="1.8.0"
TLA_SHA256="15d103b7e5617780bcc904c0af12f1ad242e2b345c0301136c5be4588f17edac"
TLA_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CACHE="${TLA_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/sigil-tla}"
JAR="$CACHE/tla2tools-${TLA_VERSION}.jar"

sha256() {
    if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1
    else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

mkdir -p "$CACHE"
if [[ ! -f "$JAR" ]] || [[ "$(sha256 "$JAR")" != "$TLA_SHA256" ]]; then
    echo "Downloading tla2tools.jar v${TLA_VERSION} to $JAR"
    # curl uses the system CA bundle (or CURL_CA_BUNDLE); TLS is always verified.
    curl -fsSL --retry 3 -o "$JAR.part" "$TLA_URL"
    got="$(sha256 "$JAR.part")"
    if [[ "$got" != "$TLA_SHA256" ]]; then
        echo "SHA-256 mismatch for tla2tools.jar: got $got" >&2
        rm -f "$JAR.part"
        exit 2
    fi
    mv "$JAR.part" "$JAR"
fi

if [[ $# -gt 0 ]]; then
    CONFIGS=("$@")
else
    CONFIGS=(MC.cfg MC_all.cfg MC_lazy.cfg MC_mutant.cfg)
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

status=0
for cfg in "${CONFIGS[@]}"; do
    name="$(basename "$cfg" .cfg)"
    case "$cfg" in /*) cfgpath="$cfg" ;; *) cfgpath="$HERE/$cfg" ;; esac
    echo "=== TLC: $name ==="
    log="$WORK/$name.log"
    start=$(date +%s)
    set +e
    (cd "$HERE" && java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
        -workers auto -noGenerateSpecTE -cleanup \
        -metadir "$WORK/$name.states" -config "$cfgpath" MC.tla) >"$log" 2>&1
    rc=$?
    set -e
    secs=$(( $(date +%s) - start ))
    grep -E 'Error:|violated|states generated,|depth of the complete|Finished in' "$log" || true

    if [[ "$name" == *mutant* ]]; then
        if [[ $rc -ne 0 ]] && grep -q "Invariant Safety is violated" "$log"; then
            echo ">>> $name: counterexample found as expected (${secs}s)"
        else
            echo ">>> $name: FAIL - mutated model was NOT caught (rc=$rc)" >&2
            tail -40 "$log" >&2
            status=1
        fi
    else
        if [[ $rc -eq 0 ]] && grep -q "No error has been found" "$log"; then
            echo ">>> $name: OK, all invariants hold (${secs}s)"
        else
            echo ">>> $name: FAIL (rc=$rc)" >&2
            tail -200 "$log" >&2
            status=1
        fi
    fi
done
exit $status
