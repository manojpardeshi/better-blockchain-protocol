"""Byzantine witness behaviours used by the tests."""

from sigil.model import transition_id
from sigil.witness import Record, Rejected, Witness


class Equivocator(Witness):
    """Votes for anything it is asked, ignoring locks and prior votes."""

    def spend(self, req):
        h = req["header"]
        gen = next(g for s, g in h["inputs"] if s == req["sigil"])
        v = self._vote(req["sigil"], gen, transition_id(h))
        self.records.setdefault(req["sigil"], Record()).votes.append(v)
        return v

    def forge(self, sigil, gen, tid):
        return self._vote(sigil, gen, tid)


class Silent(Witness):
    """Never answers (models a crashed or censoring witness)."""

    def spend(self, req):
        raise Rejected("silent")
