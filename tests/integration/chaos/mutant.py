"""Deliberately broken Python witness daemons, to show the chaos checks have teeth.

    python -m tests.integration.chaos.mutant <mutation> run --key ... (witnessd run arguments)

The real ``sigil.witnessd`` runs with one method of the real ``Witness`` patched in memory
(the product source is never edited):

* ``nopersist``: records are never written to the store (votes and bindings live only in
  memory), so a SIGKILL makes the witness forget what it voted. SPEC §5 durability.
* ``noexpiry``: SPEND newly binds a sigil on an expired authorisation. SPEC §5.1 step 4.

``mutate_spend_source`` applies a one-line source mutation to ``Witness.spend`` and checks
that it matched exactly once, so a refactor of the product cannot silently disarm a mutant.
"""

import inspect
import sys
import textwrap

from sigil import witness as witness_mod
from sigil import witnessd

EXPIRY_CHECK = 'if int(self.clock()) > auth["unlock"]["expires"]:'


def mutate_spend_source(old: str, new: str) -> None:
    src = textwrap.dedent(inspect.getsource(witness_mod.Witness.spend))
    if src.count(old) != 1:
        raise SystemExit(f"mutant: {old!r} occurs {src.count(old)} times in Witness.spend")
    ns: dict = {}
    exec(compile(src.replace(old, new), witness_mod.__file__, "exec"), vars(witness_mod), ns)
    witness_mod.Witness.spend = ns["spend"]


def nopersist() -> None:
    real = witness_mod.Witness._persist

    def _persist(self, *entries):
        real(self, *(e for e in entries if e[0] != "record"))

    witness_mod.Witness._persist = _persist


def noexpiry() -> None:
    mutate_spend_source(EXPIRY_CHECK, "if False:")


MUTANTS = {"nopersist": nopersist, "noexpiry": noexpiry}


def main(argv: list) -> None:
    MUTANTS[argv[0]]()
    witnessd.main(argv[1:])


if __name__ == "__main__":
    main(sys.argv[1:])
