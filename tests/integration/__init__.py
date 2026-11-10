"""Integration tests: real Rust and Python witness processes over HTTP.

    cargo build --release --locked --manifest-path rust/Cargo.toml
    python -m unittest discover -s tests/integration -t .

These tests start dozens of processes and take minutes, so the default
``python -m unittest discover`` does not run them: this package's
``load_tests`` returns nothing unless the run asks for the integration suite,
by naming ``tests/integration`` (or ``tests.integration``) on the command line,
by starting discovery in this directory, or by setting ``SIGIL_INTEGRATION=1``.
``SIGIL_INTEGRATION=0`` turns them off even when named. Without the Rust
witness binary (``rust/target/release/sigil-witness``, or
``$SIGIL_WITNESS_BIN``) every test is skipped.

The suites:

* the end-to-end flows: ``tests/integration/test_*.py``, with the fixtures and
  end-state invariants of ``tests/integration/harness.py``;
* the fault-injection (chaos) suite: ``tests/integration/chaos/`` (see its
  ``test_chaos.py`` and ``run.py``).

The soak and compatibility tests (``test_soak``, ``test_store_compat``,
``test_wire_compat``, ``test_daemon_ops``, ``test_bugs_found``; fixtures in
``compat_harness.py``) take these environment variables:

* ``SIGIL_SOAK_SECONDS``  soak duration (default 180; e.g. 1800-3600 for a long run)
* ``SIGIL_SOAK_SAMPLE``   seconds between resource samples (default 10)
* ``SIGIL_SOAK_ROTATE``   seconds between rotations (default 60; 0 disables)
* ``SIGIL_SOAK_SERIES``   seconds between new asset series (default 120; bounds per-hop dossiers)
* ``SIGIL_SOAK_SUCCESSION_AT``  when the dead-man takeover happens, as a fraction of the run
  (default 0.5; negative disables)
* ``SIGIL_SOAK_SEED``, ``SIGIL_SOAK_MAX_DISK`` (bytes, default 4 GiB), ``SIGIL_SOAK_VERBOSE``
* ``SIGIL_SOAK_OUT``      write the soak's numbers (JSON) to this path
* ``SIGIL_WIRE_OUT``      write the wire comparison (cases, differences) to this path
* ``SIGIL_KEEP=1``        keep temp directories (for debugging)
"""

import inspect
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))


def _discovery_started_here() -> bool:
    """Did ``unittest`` discovery start in this directory (not merely pass through it)?"""
    for frame in inspect.stack():
        if frame.function == "_find_tests":
            start = frame.frame.f_locals.get("start_dir")
            # The innermost _find_tests frame is the directory being scanned: our parent
            # when discovery passes through, this directory when it started here.
            return start is not None and os.path.abspath(start) == HERE
    return False


def enabled() -> bool:
    env = os.environ.get("SIGIL_INTEGRATION")
    if env is not None:
        return env.strip() not in ("", "0", "false", "no")
    return (any("tests/integration" in a.replace(os.sep, "/") or "tests.integration" in a for a in sys.argv)
            or _discovery_started_here())


def load_tests(loader, standard_tests, pattern):
    if not enabled():
        return unittest.TestSuite()
    top = os.path.dirname(os.path.dirname(HERE))
    standard_tests.addTests(loader.discover(start_dir=HERE, pattern=pattern or "test*.py", top_level_dir=top))
    return standard_tests
