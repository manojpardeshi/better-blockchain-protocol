#!/usr/bin/env python3
"""Mutation testing of the verification harness: is the bounded refinement check able to
catch real bugs in the witness?

    python3 rust/sigil-witness/proofs/mutants.py [--work DIR] [names...]

For each mutant, copies rust/ to a scratch directory, applies one source edit to
sigil-witness/src (the original tree is never touched), and runs
tests/refinement_bfs.rs (reduced alphabet) of the copied proofs crate against it. A mutant is
"killed" when the run fails, and the first violation message is reported. Exit status 1 if
any mutant survives.
"""

import argparse
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
RUST = os.path.normpath(os.path.join(HERE, "..", ".."))

# name -> (file under sigil-witness/src, old, new, what it breaks)
MUTANTS = {
    "release-any-proof": (
        "witness.rs",
        "if !proves_dead(&header, &tid, proof, &self.registry, self.batch_verify) {",
        "if false && !proves_dead(&header, &tid, proof, &self.registry, self.batch_verify) {",
        "RELEASE accepts any death proof (TLA+ mutant AnyProof)",
    ),
    "proof-any-constellation": (
        "proofs.rs",
        '                    && str_is(seal, "constellation", home)\n',
        "",
        "seal-kind death proofs from any constellation (TLA+ mutant AnyConstellationProof)",
    ),
    "votes-proof-any-constellation": (
        "proofs.rs",
        '                    && other_tid(v)\n                    && str_is(v, "constellation", home))',
        "                    && other_tid(v))",
        "votes-kind death proofs from any constellation",
    ),
    "proof-same-tid": (
        "proofs.rs",
        "let other_tid = |v: &Json| v.get(\"tid\").and_then(Json::as_str).is_some_and(|t| t != tid);",
        "let other_tid = |v: &Json| v.get(\"tid\").and_then(Json::as_str).is_some();",
        "death proofs may consist of votes FOR the bound transition",
    ),
    "jump-while-bound": (
        "witness.rs",
        "            if rec.tid.is_some() {\n                return rejected(\"bound at an earlier generation; release it first\");",
        "            if false {\n                return rejected(\"bound at an earlier generation; release it first\");",
        "SPEND jumps generations while bound (re-binds without RELEASE)",
    ),
    "stale-accepted": (
        "witness.rs",
        "        if gen < rec.gen {\n            return rejected(\"stale generation\");",
        "        if gen + 1 < rec.gen {\n            return rejected(\"stale generation\");",
        "SPEND accepts the generation just below the record's",
    ),
    # Equivalent mutant: the slow-path Conflict branch is unreachable (the fast path answers
    # Conflict whenever a record exists at the request's generation with another tid; every
    # other way into the slow path rejects first or arrives unbound). Expected to survive.
    "conflict-revotes": (
        "witness.rs",
        "        if rec.tid.as_deref() != Some(tid.as_str()) {\n            return Err(Error::Conflict(rec.vote.clone()));\n        }",
        "        if rec.tid.as_deref() != Some(tid.as_str()) {\n            rec.tid = Some(tid.clone());\n            rec.vote = None;\n        }",
        "slow path re-binds instead of answering Conflict (only reachable when the fast path is skipped)",
    ),
    "fastpath-wrong-vote": (
        "witness.rs",
        "                    (Some(_), Some(v)) => return Ok(v.clone()),",
        "                    (Some(_), Some(_)) => return Ok(fresh),",
        "a repeated request gets a freshly signed vote instead of the stored one",
    ),
    "expiry-ignored": (
        "witness.rs",
        "            if now > expires {",
        "            if false && now > expires {",
        "binds on an expired authorisation (SPEC 5.1)",
    ),
    "release-keeps-vote": (
        "witness.rs",
        "        rec.vote = None;\n        rec.abstain = false;",
        "        rec.abstain = false;",
        "RELEASE forgets to clear the stored vote",
    ),
    "home-ignored": (
        "witness.rs",
        "        if req.get(\"home\").and_then(Json::as_str) != Some(self.cid.as_str()) {",
        "        if req.get(\"home\").and_then(Json::as_str).is_none() {",
        "votes on sigils homed at other constellations",
    ),
}


EQUIVALENT = {"conflict-revotes"}


def run(name, work, target_dir, no_model=False):
    path, old, new, what = MUTANTS[name]
    dst = os.path.join(work, name)
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(RUST, dst, ignore=shutil.ignore_patterns("target", "corpus", "artifacts", "logs", "coverage"))
    f = os.path.join(dst, "sigil-witness", "src", path)
    src = open(f).read()
    if src.count(old) != 1:
        return name, "NOT-APPLIED", f"pattern found {src.count(old)} times", 0.0
    open(f, "w").write(src.replace(old, new))
    t = time.time()
    p = subprocess.run(
        ["cargo", "test", "--release", "--test", "refinement_bfs", "--", "--nocapture"],
        cwd=os.path.join(dst, "sigil-witness", "proofs"),
        env=dict(os.environ, CARGO_TARGET_DIR=target_dir, **({"SIGIL_NO_MODEL": "1"} if no_model else {})),
        capture_output=True, text=True,
    )
    dt = time.time() - t
    out = p.stdout + p.stderr
    msg = next((l.strip() for l in out.splitlines()
                if any(k in l for k in ("SAFETY:", "REFINEMENT:", "MODEL:", "LIVENESS:", "assertion"))), "")
    if "error[" in out:
        return name, "BUILD-ERROR", next(l for l in out.splitlines() if "error[" in l), dt
    return name, "killed" if p.returncode != 0 else "SURVIVED", msg[:220] or what, dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", default=os.environ.get("TMPDIR", "/tmp") + "/sigil-mutants")
    ap.add_argument("--no-model", action="store_true", help="turn the transcription checks off (SIGIL_NO_MODEL=1)")
    ap.add_argument("names", nargs="*")
    args = ap.parse_args()
    os.makedirs(args.work, exist_ok=True)
    target_dir = os.path.join(args.work, "target")
    survived = 0
    for name in args.names or list(MUTANTS):
        name, status, msg, dt = run(name, args.work, target_dir, args.no_model)
        survived += status != "killed" and name not in EQUIVALENT
        print(f"{name:32} {status:12} {dt:6.1f}s  {MUTANTS[name][3]}\n{'':32} -> {msg}", flush=True)
    sys.exit(1 if survived else 0)


if __name__ == "__main__":
    main()
