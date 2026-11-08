"""Multi-process integration suites (real witness processes over HTTP).

They take minutes and need the Rust witness binary, so they are kept out of the default
``python3 -m unittest discover`` and run on their own:

    python -m unittest discover -s tests/integration -t .

``load_tests`` below makes that split: when discovery merely passes through this package
on its way down from the repository root it contributes nothing, and when discovery
*starts* here (``-s tests/integration``, or below) it loads the suites as usual. A module
can always be run directly, e.g. ``python -m unittest tests.integration.chaos.test_chaos``.
Set ``SIGIL_INTEGRATION=1`` to include the suites in a root-level discovery too.
"""

import inspect
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def _discovery_started_here() -> bool:
    for frame in inspect.stack():
        if frame.function == "_find_tests":
            start = frame.frame.f_locals.get("start_dir")
            # The innermost _find_tests frame is the directory being scanned: our parent
            # when discovery passes through, this directory when it started here.
            return start is not None and os.path.abspath(start) == HERE
    return False


def load_tests(loader, standard_tests, pattern):
    if os.environ.get("SIGIL_INTEGRATION") == "1" or _discovery_started_here():
        standard_tests.addTests(loader.discover(start_dir=HERE, pattern=pattern or "test*.py",
                                                top_level_dir=os.path.dirname(os.path.dirname(HERE))))
    return standard_tests
