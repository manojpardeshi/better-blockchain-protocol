#!/usr/bin/env bash
# Machine-check the Sigil witness protocol.
#
#   formal/check.sh                 run the TLAPS proof + every default config
#   formal/check.sh MC.cfg ...      run only the given TLC configs (no TLAPS)
#   SIGIL_SKIP_TLAPS=1 formal/check.sh      skip the TLAPS proof
#   SIGIL_TLC_EXTRA="MC_proofs.cfg" formal/check.sh   add slow opt-in configs
#
# Two tools:
#   * TLAPS (tlapm) machine-checks formal/SigilProofs.tla: an UNBOUNDED proof
#     of the SPEC Section 8 safety theorem and both lemmas (Spec => []Safety)
#     for arbitrary numbers of witnesses, sigils, transitions, generations and
#     constellations. This is the real safety result.
#   * TLC exhaustively checks the bounded models (the original witness model,
#     the proof's own non-vacuity instance, charter rotation, owner-signed
#     expiry and deep confirmation) on small instances, with mutation tests.
#
# Module per config:
#   MC_multi*  -> MC_multi.tla      MC_proofs* -> MC_proofs.tla (needs TLAPS libs)
#   MC_rot*    -> MC_rot.tla        MC_expiry* -> SigilExpiry.tla
#   MC_deep*   -> SigilDeep.tla     everything else -> MC.tla
#
# Configs named *mutant* or *witness* are EXPECTED to report an invariant
# violation; all others must pass. Exit status is non-zero if any expectation
# is unmet. Downloads tla2tools.jar and (for the proof) tlapm, both pinned by
# SHA-256, into a cache directory; neither is committed. Requires java >= 11
# and curl. TLS is always verified (system CA bundle / CURL_CA_BUNDLE).
set -euo pipefail

TLA_VERSION="1.8.0"
TLA_SHA256="15d103b7e5617780bcc904c0af12f1ad242e2b345c0301136c5be4588f17edac"
TLA_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar"

# tlapm 1.6.0-pre, linux x86_64 (bundles Zenon, Z3 and Isabelle/TLA+).
TLAPM_VERSION="1.6.0-pre"
TLAPM_SHA256="b3c2554d3dd2198772ea8c814639a024fe9c390eac0ec25f4f444ad446a7dd28"
TLAPM_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_VERSION}/tlapm-${TLAPM_VERSION}-x86_64-linux-gnu.tar.gz"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CACHE="${TLA_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/sigil-tla}"
JAR="$CACHE/tla2tools-${TLA_VERSION}.jar"
TLAPM_DIR="$CACHE/tlapm-${TLAPM_VERSION}"
TLAPM="$TLAPM_DIR/tlapm/bin/tlapm"
STDLIB="$TLAPM_DIR/tlapm/lib/tlapm/stdlib"

sha256() {
    if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1
    else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

mkdir -p "$CACHE"
if [[ ! -f "$JAR" ]] || [[ "$(sha256 "$JAR")" != "$TLA_SHA256" ]]; then
    echo "Downloading tla2tools.jar v${TLA_VERSION} to $JAR"
    curl -fsSL --retry 3 -o "$JAR.part" "$TLA_URL"
    got="$(sha256 "$JAR.part")"
    if [[ "$got" != "$TLA_SHA256" ]]; then
        echo "SHA-256 mismatch for tla2tools.jar: got $got" >&2
        rm -f "$JAR.part"; exit 2
    fi
    mv "$JAR.part" "$JAR"
fi

status=0
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# ----------------------------------------------------------------- TLAPS proof
ensure_tlapm() {
    [[ -x "$TLAPM" ]] && return 0
    local tgz="$CACHE/tlapm-${TLAPM_VERSION}.tar.gz"
    echo "Downloading tlapm ${TLAPM_VERSION}"
    curl -fsSL --retry 3 -o "$tgz.part" "$TLAPM_URL" || return 1
    local got; got="$(sha256 "$tgz.part")"
    if [[ "$got" != "$TLAPM_SHA256" ]]; then
        echo "SHA-256 mismatch for tlapm: got $got" >&2; rm -f "$tgz.part"; return 1
    fi
    mv "$tgz.part" "$tgz"
    mkdir -p "$TLAPM_DIR"
    tar -xzf "$tgz" -C "$TLAPM_DIR" || return 1
    [[ -x "$TLAPM" ]]
}

# Only run the proof when invoked with no explicit config list.
if [[ $# -eq 0 && "${SIGIL_SKIP_TLAPS:-0}" != "1" ]]; then
    echo "=== TLAPS: SigilProofs.tla (unbounded safety proof) ==="
    if [[ "$(uname -s)-$(uname -m)" == "Linux-x86_64" ]] && ensure_tlapm; then
        start=$(date +%s)
        if (cd "$HERE" && "$TLAPM" -I "$STDLIB" --cache-dir "$WORK/tlapscache" \
                --strict SigilProofs.tla) >"$WORK/tlaps.log" 2>&1; then
            secs=$(( $(date +%s) - start ))
            grep -E 'obligations' "$WORK/tlaps.log" || true
            echo ">>> SigilProofs: OK, all obligations proved (${secs}s)"
        else
            echo ">>> SigilProofs: FAIL - proof did not check" >&2
            tail -40 "$WORK/tlaps.log" >&2
            status=1
        fi
    else
        echo ">>> TLAPS unavailable on this platform; skipping the proof" >&2
        echo "    (set SIGIL_SKIP_TLAPS=1 to silence, or run on Linux x86_64)" >&2
    fi
fi

# ----------------------------------------------------------------- TLC configs
if [[ $# -gt 0 ]]; then
    CONFIGS=("$@")
else
    CONFIGS=(MC.cfg MC_all.cfg MC_lazy.cfg MC_mutant.cfg
             MC_multi.cfg MC_multi_all.cfg MC_multi_mutant.cfg
             MC_proofs_witness.cfg MC_proofs_witness2.cfg
             MC_rot.cfg MC_rot_mutant.cfg MC_rot_sibling.cfg MC_rot_sibling4.cfg MC_rot_sibling_witness.cfg MC_rot_sibling_witness2.cfg
             MC_expiry.cfg MC_expiry_mutant.cfg MC_expiry_skew_mutant.cfg
             MC_deep.cfg MC_deep_mutant.cfg
             ${SIGIL_TLC_EXTRA:-})
fi

module_for() {   # map a config name to its TLA module
    case "$1" in
        MC_multi*)  echo MC_multi.tla ;;
        MC_proofs*) echo MC_proofs.tla ;;
        MC_rot*)    echo MC_rot.tla ;;
        MC_expiry*) echo SigilExpiry.tla ;;
        MC_deep*)   echo SigilDeep.tla ;;
        *)          echo MC.tla ;;
    esac
}

for cfg in "${CONFIGS[@]}"; do
    name="$(basename "$cfg" .cfg)"
    case "$cfg" in /*) cfgpath="$cfg" ;; *) cfgpath="$HERE/$cfg" ;; esac
    module="$(module_for "$name")"
    # MC_proofs* extend the TLAPS standard library (FiniteSetTheorems, TLAPS).
    libarg=()
    if [[ "$name" == MC_proofs* ]]; then
        if [[ -d "$STDLIB" ]] || ensure_tlapm; then
            libarg=("-DTLA-Library=$STDLIB")
        else
            echo "=== TLC: $name ===" ; echo ">>> $name: SKIP (needs TLAPS libraries)" >&2
            continue
        fi
    fi
    echo "=== TLC: $name ==="
    log="$WORK/$name.log"
    start=$(date +%s)
    set +e
    (cd "$HERE" && java -XX:+UseParallelGC "${libarg[@]}" -cp "$JAR" tlc2.TLC \
        -workers auto -noGenerateSpecTE -cleanup \
        -metadir "$WORK/$name.states" -config "$cfgpath" "$module") >"$log" 2>&1
    rc=$?
    set -e
    secs=$(( $(date +%s) - start ))
    grep -E 'Error:|violated|states generated,|depth of the complete|Finished in' "$log" || true

    case "$name" in
        *mutant*|*witness*)   # expected to find a counterexample
            if [[ $rc -ne 0 ]] && grep -q "Invariant .* is violated" "$log"; then
                echo ">>> $name: counterexample found as expected (${secs}s)"
            else
                echo ">>> $name: FAIL - expected a violation, found none (rc=$rc)" >&2
                tail -40 "$log" >&2
                status=1
            fi ;;
        *)                    # must hold
            if [[ $rc -eq 0 ]] && grep -q "No error has been found" "$log"; then
                echo ">>> $name: OK, all invariants hold (${secs}s)"
            else
                echo ">>> $name: FAIL (rc=$rc)" >&2
                tail -200 "$log" >&2
                status=1
            fi ;;
    esac
done
exit $status
