"""A witness or standby member keeps the charter chains it learned in its store.

A new-version member restarted from a registry file that predates its own
version used to refuse to vote ("own charter version unknown") until someone
gossiped the chain to it again. The chains it learned by gossip, ADOPT or
STANDBY are now persisted and merged into the registry file's at start.
"""

import os
import sqlite3
import tempfile
import unittest

from sigil import KeyPair
from sigil.charter import Registry
from sigil.server import StandbyServer, WitnessServer
from sigil.store import WitnessStore
from sigil.succession import Standby, StandbyStore
from sigil.witness import Witness
from tests.test_succession import DEAD, Home


class CharterMemoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.stores = []
        self.addCleanup(lambda: [s.close() for s in self.stores])

    def path(self, name):
        return os.path.join(self.tmp.name, name + ".db")

    def wstore(self, name):
        s = WitnessStore(self.path(name))
        self.stores.append(s)
        return s

    def sstore(self, name):
        s = StandbyStore(self.path(name))
        self.stores.append(s)
        return s

    def stale(self, h):
        """A registry file written before the rotation: version 0 only."""
        reg = Registry()
        reg.add_chain(h.X, h.net.registry.chain(h.X)[:1])
        return reg

    def rotated_home(self):
        """A home rotated to durable new members (with a new committee); returns (home, keys)."""
        h = Home()
        keys = [KeyPair.generate() for _ in range(4)]
        by_pk = {k.pk: i for i, k in enumerate(keys)}

        def durable(kp, registry, clock, **kw):
            return Witness(kp, registry, clock, store=self.wstore(f"w{by_pk[kp.pk]}"), **kw)

        h.net.rotate(h.X, keys, witness_cls=durable, successor={"n": 4, "dead_man": DEAD})
        return h, keys

    def test_adopted_member_votes_after_restart_with_an_old_registry_file(self):
        h, keys = self.rotated_home()
        old = h.net.witnesses(h.X)[0]
        old.store.close()
        w = Witness(keys[0], self.stale(h), h.net.clock, store=self.wstore("w0"))
        self.assertEqual((w.cid, w.version), (h.X, 1))
        self.assertEqual(len(w.registry.chain(h.X)), 2)
        p, s = h.parcel("aa")
        r = h.req(h.hdr([(s, 0)], "1"), s, p)
        self.assertEqual(w.spend(dict(r, mirror=h.acks(r)))["version"], 1)

    def test_chain_learned_by_gossip_survives_restart(self):
        h, keys = self.rotated_home()
        # A member of version 0 that the rotation left out still learns version 1 by gossip.
        kp = KeyPair.generate()
        reg = self.stale(h)
        w = Witness(kp, reg, h.net.clock, store=self.wstore("gossiped"))
        srv = WitnessServer(w)
        self.addCleanup(srv.httpd.server_close)
        srv.dispatch("gossip", {"charters": {h.X: h.net.registry.chain(h.X)}})
        self.assertEqual(len(reg.chain(h.X)), 2)
        w.store.close()
        w2 = Witness(kp, self.stale(h), h.net.clock, store=self.wstore("gossiped"))
        self.assertEqual(len(w2.registry.chain(h.X)), 2)

    def test_standby_member_keeps_the_version_it_stands_by_for(self):
        h, keys = self.rotated_home()
        ck = KeyPair.generate()
        # The new committee is h.net.committees[X]; stand by with one of its keys, durably.
        member = h.net.committees[h.X][0]
        m = Standby(member.kp, h.net.registry, h.net.clock, store=self.sstore("s0"))
        m.enter(h.X, 1, [])
        m.store.close()
        m2 = Standby(member.kp, self.stale(h), h.net.clock, store=self.sstore("s0"))
        self.assertEqual((m2.cid, m2.version), (h.X, 1))
        w = h.net.witnesses(h.X)[0]
        self.assertTrue(m2.observe(w.heartbeat("c1"), "c1"))  # needs version 1's charter
        # And by gossip, through the standby server.
        reg = self.stale(h)
        m3 = Standby(ck, reg, h.net.clock, store=self.sstore("s-gossip"))
        srv = StandbyServer(m3)
        self.addCleanup(srv.httpd.server_close)
        srv.dispatch("gossip", {"charters": {h.X: h.net.registry.chain(h.X)}})
        m3.store.close()
        m4 = Standby(ck, self.stale(h), h.net.clock, store=self.sstore("s-gossip"))
        self.assertEqual(len(m4.registry.chain(h.X)), 2)

    def test_store_without_charters_and_a_bad_charter_row_still_load(self):
        h, keys = self.rotated_home()
        h.net.witnesses(h.X)[0].store.close()
        db = sqlite3.connect(self.path("w0"))
        db.execute("DELETE FROM log WHERE kind = 'charter'")
        db.commit()
        db.close()
        w = Witness(keys[0], self.stale(h), h.net.clock, store=self.wstore("w0"))
        self.assertEqual((w.cid, w.version), (h.X, 1))   # an old store: the old behaviour
        self.assertEqual(len(w.registry.chain(h.X)), 1)
        # A chain that does not verify is ignored (the registry file's stands).
        chain = h.net.registry.chain(h.X)
        w.store.append([("charter", h.X, [chain[0], dict(chain[1], sigs={})])])
        w.store.close()
        w2 = Witness(keys[0], self.stale(h), h.net.clock, store=self.wstore("w0"))
        self.assertEqual(len(w2.registry.chain(h.X)), 1)

    def test_only_chains_the_registry_file_names_are_kept(self):
        """Gossip of a constellation the registry file does not name is not persisted (the
        gossip cap must not become permanent), and stored rows for one are not restored."""
        h, keys = self.rotated_home()
        other = Home()
        kp = KeyPair.generate()
        w = Witness(kp, self.stale(h), h.net.clock, store=self.wstore("unrelated"))
        srv = WitnessServer(w)
        self.addCleanup(srv.httpd.server_close)
        srv.dispatch("gossip", {"charters": {other.X: other.net.registry.chain(other.X),
                                             h.X: h.net.registry.chain(h.X)}})
        rows = {k for kind, k, _v in w.store.db.execute("SELECT kind, key, value FROM log") if kind == "charter"}
        self.assertEqual(rows, {h.X})
        w.store.append([("charter", other.X, other.net.registry.chain(other.X))])   # as an older branch wrote
        w.store.close()
        w2 = Witness(kp, self.stale(h), h.net.clock, store=self.wstore("unrelated"))
        self.assertNotIn(other.X, w2.registry)
        self.assertEqual(len(w2.registry.chain(h.X)), 2)

    def test_corrupt_charter_row_does_not_stop_a_start(self):
        h, keys = self.rotated_home()
        h.net.witnesses(h.X)[0].store.close()
        s = self.wstore("w0")
        s.append([("charter", h.X, [{"body": "x", "sigs": {}}]), ("charter", "zz", {"a": 1})])
        s.close()
        w = Witness(keys[0], self.stale(h), h.net.clock, store=self.wstore("w0"))
        self.assertEqual((w.cid, w.version), (h.X, 1))


if __name__ == "__main__":
    unittest.main()
