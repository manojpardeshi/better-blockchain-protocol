"""Deliberately broken builds of the Rust witness, to show the chaos checks catch Rust bugs too.

``build(name, workdir)`` copies ``rust/`` (sources only) into ``workdir``, applies one
source mutation and builds ``sigil-witness`` there; the product tree is never touched.
Each mutation must match exactly once, so a refactor cannot silently disarm it.

* ``nopersist``: ``Witness::persist`` queues an empty batch, so records (votes, bindings)
  never reach the store and a SIGKILL makes the witness forget what it voted.
* ``noexpiry``: SPEND newly binds on an expired authorisation (SPEC §5.1 step 4).

Building takes a few minutes the first time (``workdir/target`` is reused afterwards), so
the tests that use these run only with ``SIGIL_CHAOS_RUST_MUTANTS=1``.
"""

import os
import shutil
import subprocess

from .cluster import ROOT

MUTATIONS = {
    "nopersist": ("src/witness.rs",
                  'self.store.submit(vec![("record".into(), sigil.to_string(), rec.to_json())])',
                  "{ let _ = (sigil, rec); self.store.submit(vec![]) }"),
    "noexpiry": ("src/witness.rs", "if now > expires {", "if false && now > expires {"),
}


def build(name: str, workdir: str) -> str:
    """Path of the mutated ``sigil-witness`` binary (built if needed)."""
    src = os.path.join(workdir, f"rust-{name}")
    if os.path.exists(src):
        shutil.rmtree(src)
    shutil.copytree(os.path.join(ROOT, "rust"), src, ignore=shutil.ignore_patterns("target", "fuzz", "proofs"))
    rel, old, new = MUTATIONS[name]
    path = os.path.join(src, "sigil-witness", rel)
    with open(path) as f:
        text = f.read()
    if text.count(old) != 1:
        raise RuntimeError(f"mutation {name}: {old!r} occurs {text.count(old)} times in {rel}")
    with open(path, "w") as f:
        f.write(text.replace(old, new))
    env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(workdir, "target"))
    subprocess.run(["cargo", "build", "--release", "--locked", "-p", "sigil-witness",
                    "--manifest-path", os.path.join(src, "Cargo.toml")], env=env, check=True,
                   capture_output=True)
    out = os.path.join(workdir, f"sigil-witness-{name}")
    shutil.copy2(os.path.join(workdir, "target", "release", "sigil-witness"), out)
    return out
