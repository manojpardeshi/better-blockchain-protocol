"""Soak and compatibility integration tests (multi-process; Rust and Python witnesses).

Run them with::

    cargo build --release --locked --manifest-path rust/Cargo.toml   # optional: Rust parts skip without it
    python -m unittest discover -s tests/integration -t .

They are kept out of the default ``python3 -m unittest discover``: the
``load_tests`` hook below returns nothing unless discovery was started in this
directory (or ``SIGIL_INTEGRATION=1`` is set). Environment variables:

* ``SIGIL_SOAK_SECONDS``  soak duration (default 180; e.g. 1800-3600 for a long run)
* ``SIGIL_SOAK_SAMPLE``   seconds between resource samples (default 10)
* ``SIGIL_SOAK_ROTATE``   seconds between rotations (default 60; 0 disables)
* ``SIGIL_SOAK_OUT``      write the soak's numbers (JSON) to this path
* ``SIGIL_WITNESS_BIN``   the Rust witness binary (default rust/target/release/sigil-witness)
* ``SIGIL_KEEP``          keep temp directories (for debugging)
"""

import inspect
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))


def _started_here() -> bool:
    """Was unittest discovery started in this directory (not at the repository root)?"""
    for frame in inspect.stack(0):
        if frame.function == "discover" and frame.filename.endswith(os.path.join("unittest", "loader.py")):
            start = frame.frame.f_locals.get("start_dir")
            if isinstance(start, str):
                return os.path.abspath(start) == HERE
    return False


def load_tests(loader: unittest.TestLoader, standard_tests, pattern):
    if os.environ.get("SIGIL_INTEGRATION") == "1" or _started_here():
        standard_tests.addTests(loader.discover(start_dir=HERE, pattern=pattern or "test*.py",
                                                top_level_dir=os.path.dirname(os.path.dirname(HERE))))
    return standard_tests
