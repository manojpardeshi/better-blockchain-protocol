"""End-to-end integration tests: real Rust and Python witness processes over HTTP.

    cargo build --release --locked --manifest-path rust/Cargo.toml
    python -m unittest discover -s tests/integration -t .

These tests start dozens of processes and take minutes, so the default
``python -m unittest discover`` does not run them: this package's
``load_tests`` returns nothing unless the run asks for the integration suite,
by naming ``tests/integration`` (or ``tests.integration``) on the command line
or by setting ``SIGIL_INTEGRATION=1``. ``SIGIL_INTEGRATION=0`` turns them off
even when named. Without the Rust witness binary (``rust/target/release/
sigil-witness``, or ``$SIGIL_WITNESS_BIN``) every test is skipped.

See ``tests/integration/harness.py`` for the fixtures and the end-state
invariants every test checks.
"""

import os
import sys
import unittest


def enabled() -> bool:
    env = os.environ.get("SIGIL_INTEGRATION")
    if env is not None:
        return env.strip() not in ("", "0", "false", "no")
    return any("tests/integration" in a.replace(os.sep, "/") or "tests.integration" in a for a in sys.argv)


def load_tests(loader, standard_tests, pattern):
    if not enabled():
        return unittest.TestSuite()
    here = os.path.dirname(os.path.abspath(__file__))
    top = os.path.dirname(os.path.dirname(here))
    standard_tests.addTests(loader.discover(start_dir=here, pattern=pattern or "test*.py", top_level_dir=top))
    return standard_tests
