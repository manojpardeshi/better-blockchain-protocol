"""Resource bounds (docs/AI_THREAT_MODEL.md §2.6, docs/WIRE.md "Admission control").

Regression tests for the denial-of-service gaps of the AI-adversary review: each fails on the
code before the fix (an open witness served every client without limit; one SPEND could pin
~800 KiB; one sigil's record could grow without bound; rotations multiplied evidence logs; one
gossip message could register a 14,000-witness charter; silent connections pinned threads
forever). Every refusal must be a clean Rejected that changes no witness state.
"""

import json
import os
import socket
import sqlite3
import tempfile
import time
import unittest
import urllib.error
import urllib.request
from dataclasses import asdict

from sigil import KeyPair, Network, locks, model
from sigil import ratelimit as RL
from sigil.charter import MAX_CHARTER_BYTES, MAX_WITNESSES, Registry, charter_body, constellation_id, verify_chain
from sigil.encoding import canonical
from sigil.gossip import GossipStore
from sigil.server import RemoteWitness, WitnessServer
from sigil.store import WitnessStore
from sigil.witness import MAX_AUTH_BYTES, MAX_GEN, MAX_PROOF_BYTES, Rejected, Witness

FAR = 4_000_000_000


def spend_req(c, owner, salt, inputs=None, memo="11" * 32):
    p = model.parcel(c, "x", 1, locks.sig(owner.pk), salt)
    s = model.sigil_of(p)
    h = {"inputs": inputs or [[s, 0]], "body": memo}
    u = locks.empty_unlock(FAR)
    u["sigs"][owner.pk] = locks.sign_unlock(owner, s, model.transition_id(h), FAR)
    return {"sigil": s, "header": h, "home": c, "lock": p["lock"], "salt": salt, "unlock": u}, p


def auth_len(r) -> int:
    return len(canonical({k: r[k] for k in ("home", "lock", "salt", "unlock", "header")}))


class RateLimiterTests(unittest.TestCase):
    def test_bucket_refill_retry_after_and_eviction(self):
        r = RL.RateLimiter(2.0, 3, max_clients=2)
        self.assertEqual([r.admit("a", 0.0) for _ in range(3)], [0, 0, 0])
        self.assertEqual(r.admit("a", 0.0), 1)          # empty: one token in 0.5 s, rounded up
        self.assertEqual(r.admit("a", 0.5), 0)
        r.admit("b", 1.0)
        r.admit("c", 1.0)                               # forgets a, the least recently seen
        self.assertEqual(len(r), 2)
        self.assertEqual(r.admit("a", 1.0), 0)          # a forgotten client starts full
        with self.assertRaises(ValueError):
            RL.RateLimiter(0, 1)
        with self.assertRaises(ValueError):
            RL.RateLimiter(1, 0)

    def test_client_keys_and_loopback(self):
        self.assertEqual(RL.client_key("10.1.2.3"), "10.1.2.3")
        self.assertEqual(RL.client_key("::ffff:10.1.2.3"), "10.1.2.3")
        self.assertEqual(RL.client_key("2001:db8:1:2:3:4:5:6"), "2001:db8:1:2::/64")
        self.assertEqual(RL.client_key("2001:db8:1:2:ffff::1"), RL.client_key("2001:db8:1:2::9"))
        for h in ("127.0.0.1", "127.9.9.9", "::1", "localhost"):
            self.assertTrue(RL.is_loopback(h), h)
        for h in ("0.0.0.0", "::", "10.0.0.1", "example.org", ""):
            self.assertFalse(RL.is_loopback(h), h)

    def test_connection_limiter(self):
        c = RL.ConnectionLimiter(3, 2)
        self.assertTrue(c.acquire("a") and c.acquire("a"))
        self.assertFalse(c.acquire("a"))
        self.assertTrue(c.acquire("b"))
        self.assertFalse(c.acquire("c"))
        c.release("a")
        self.assertTrue(c.acquire("c"))


class AdmissionOverHTTP(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.c = self.net.create_constellation("c", 4)
        self.w = self.net.witnesses(self.c)[0]
        self.servers = []

    def tearDown(self):
        for s in self.servers:
            s.stop()

    def serve(self, **kw) -> WitnessServer:
        s = WitnessServer(self.w, **kw).start()
        self.servers.append(s)
        return s

    def test_admission_control_is_the_default_off_loopback(self):
        """Before: every witness, wherever it listened, served every request."""
        public = self.serve(host="0.0.0.0")
        self.assertIsNotNone(public.limiter)
        self.assertEqual((public.limiter.rate, public.limiter.burst), (RL.DEFAULT_RATE, RL.DEFAULT_BURST))
        self.assertIsNone(self.serve().limiter)                         # loopback: tests, local testnets
        self.assertIsNone(self.serve(host="0.0.0.0", rate_limit=0).limiter)
        self.assertIsNotNone(self.serve(rate_limit=5).limiter)
        url = f"http://127.0.0.1:{public.httpd.server_address[1]}"
        codes = []
        for _ in range(RL.DEFAULT_BURST + 30):
            r = urllib.request.Request(url + "/v0/status", data=b'{"sigil": "x"}', method="POST")
            try:
                with urllib.request.urlopen(r, timeout=5) as resp:
                    codes.append(resp.status)
            except urllib.error.HTTPError as e:
                codes.append(e.code)
                e.close()
        self.assertIn(429, codes)
        self.assertGreaterEqual(codes.index(429), RL.DEFAULT_BURST)

    def test_a_limited_spend_is_a_clean_rejected_with_no_state_change(self):
        srv = self.serve(rate_limit=0.5, rate_burst=2)
        owner = KeyPair.generate()
        rw = RemoteWitness(srv.url)                                  # /v0/info takes one token
        rw.status("00" * 32)                                         # and this the other
        req, _ = spend_req(self.c, owner, "ab" * 16)
        with self.assertRaises(Rejected) as e:
            rw.spend(req)
        self.assertEqual(str(e.exception), "rate limited")
        self.assertNotIn(req["sigil"], self.w.records)
        r = urllib.request.Request(srv.url + "/v0/status", data=b'{"sigil": "x"}', method="POST")
        with self.assertRaises(urllib.error.HTTPError) as h:
            urllib.request.urlopen(r, timeout=5)
        self.assertEqual(h.exception.code, 429)
        self.assertGreaterEqual(int(h.exception.headers["Retry-After"]), 1)
        self.assertEqual(json.loads(h.exception.read()), {"error": "rejected", "message": "rate limited", "vote": None})
        # Rotation calls are never limited: the admin token decides.
        r = urllib.request.Request(srv.url + "/v0/freeze", data=b"{}", method="POST")
        with self.assertRaises(urllib.error.HTTPError) as h:
            urllib.request.urlopen(r, timeout=5)
        self.assertEqual(h.exception.code, 403)
        h.exception.close()

    def test_connections_are_capped_and_idle_ones_dropped(self):
        """Before: every silent connection pinned a handler thread forever."""
        from unittest import mock
        import sigil.server as S
        with mock.patch.object(S, "IDLE_TIMEOUT", 0.5), mock.patch.object(S, "MAX_CONNECTIONS", 6):
            srv = self.serve()
        host, port = srv.httpd.server_address[:2]
        socks = [socket.create_connection((host, port), timeout=5) for _ in range(9)]
        try:
            time.sleep(0.2)
            self.assertEqual(srv.httpd.conns._n, 6)
            time.sleep(1.0)
            self.assertEqual(srv.httpd.conns._n, 0)
            self.assertEqual(RemoteWitness(srv.url).status("x"), {"gen": 0, "tid": None, "votes": []})
        finally:
            for s in socks:
                s.close()


class StorageBounds(unittest.TestCase):
    def setUp(self):
        self.net = Network()
        self.c = self.net.create_constellation("c", 4)
        self.ws = self.net.witnesses(self.c)
        self.owner = KeyPair.generate()

    def test_authorisation_cap_is_exact_and_refusals_change_nothing(self):
        w = self.ws[0]
        base, _ = spend_req(self.c, self.owner, "e")
        n = MAX_AUTH_BYTES - auth_len(base) + 1
        fit, _ = spend_req(self.c, self.owner, "e" * n)
        big, _ = spend_req(self.c, self.owner, "e" * (n + 1))
        self.assertEqual(auth_len(fit), MAX_AUTH_BYTES)
        with self.assertRaisesRegex(Rejected, "authorisation too large"):
            w.spend(big)
        self.assertNotIn(big["sigil"], w.records)
        w.spend(fit)
        before = asdict(w.records[fit["sigil"]])
        with self.assertRaisesRegex(Rejected, "authorisation too large"):
            w.spend(dict(fit, unlock=dict(fit["unlock"], pad="0")))
        self.assertEqual(asdict(w.records[fit["sigil"]]), before)

    def test_binding_and_proof_caps(self):
        kreq, kp_ = spend_req(self.c, self.owner, "ab" * 16, memo="22" * 32)
        seal = model.seal_from_votes([w.spend(kreq) for w in self.ws])
        k = kreq["sigil"]
        proof = {"kind": "seal", "sigil": k, "gen": 0, "seal": seal,
                 "parcel": {"home": self.c, "lock": kp_["lock"], "salt": kp_["salt"]}}
        pad = len(canonical(dict(proof, junk="")))
        w = self.ws[0]
        s = None
        for g in range(MAX_GEN):
            p = model.parcel(self.c, "x", 1, locks.sig(self.owner.pk), "cd" * 16)
            s = model.sigil_of(p)
            req, _ = spend_req(self.c, self.owner, "cd" * 16, inputs=[[s, g], [k, 0]], memo="%064x" % g)
            w.spend(req)
            before = asdict(w.records[s])
            with self.assertRaisesRegex(Rejected, "death proof too large"):
                w.release(s, dict(proof, junk="0" * (MAX_PROOF_BYTES - pad + 1)))
            self.assertEqual(asdict(w.records[s]), before)
            self.assertEqual(w.release(s, dict(proof, junk="0" * (MAX_PROOF_BYTES - pad)) if g == 0 else proof), g + 1)
        req, _ = spend_req(self.c, self.owner, "cd" * 16, inputs=[[s, MAX_GEN], [k, 0]], memo="ff" * 32)
        before = asdict(w.records[s])
        with self.assertRaisesRegex(Rejected, "generation limit reached for this sigil"):
            w.spend(req)
        self.assertEqual(asdict(w.records[s]), before)

    def test_adopt_keeps_each_entry_once(self):
        req, _ = spend_req(self.c, self.owner, "ab" * 16)
        for w in self.ws:
            w.spend(req)
        lengths = []
        for _ in range(4):
            self.net.rotate(self.c, [KeyPair.generate() for _ in range(4)])
            lengths.append(len(self.net.witnesses(self.c)[0].records[req["sigil"]].log))
        # Before: 8, 32, 128, 512 (every signer handed over the same entries).
        self.assertEqual(lengths, [lengths[0]] * 4)
        self.assertLessEqual(lengths[0], 5)

    def test_junk_adopt_evidence_cannot_block_an_honest_owner(self):
        """A per-log count of bind entries would let a Byzantine predecessor freeze an
        honest coin by padding its evidence with junk binds; the cap reads the
        record's generation, which junk cannot raise."""
        from sigil.charter import charter_hash
        kp = KeyPair.generate()
        cur = self.net.registry.latest(self.c)
        nxt = charter_body(cur["name"], 1, [kp.pk], charter_hash(cur))
        sigs, snaps = {}, []
        for w in self.ws[:3]:
            sig, snap = w.freeze(nxt)
            sigs[w.pk] = sig
            snaps.append(snap)
        self.net.registry.add_chain(self.c, self.net.registry.chain(self.c) + [{"body": nxt, "sigs": sigs}])
        fresh, _ = spend_req(self.c, self.owner, "cd" * 16)
        junk = {fresh["sigil"]: [{"kind": "bind", "gen": i, "auth": None} for i in range(3 * MAX_GEN)]}
        a = Witness(kp, self.net.registry, self.net.clock)
        a.adopt(self.c, 1, snaps + [junk])
        self.assertEqual(a.records[fresh["sigil"]].log, [])  # unverifiable entries are dropped
        self.assertEqual(a.records[fresh["sigil"]].gen, 0)
        self.assertEqual(a.spend(fresh)["witness"], kp.pk)

    def test_store_keeps_one_row_per_key(self):
        """Before: every update appended the whole record again, so a sigil with L
        updates cost the sum of all its sizes on disk."""
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "w.db")
            kp = KeyPair.generate()
            reg = self.net.registry
            w = Witness(kp, reg, self.net.clock, store=WitnessStore(path))
            # Join a fresh one-member constellation so this witness is a member.
            body = charter_body("solo", 0, [kp.pk], None)
            cid = constellation_id(body)
            reg.add_chain(cid, [{"body": body, "sigs": {}}])
            w.join(cid, 0)
            owner = KeyPair.generate()
            kreq, kp_ = spend_req(cid, owner, "ab" * 16, memo="22" * 32)
            seal = model.seal_from_votes([w.spend(kreq)])
            proof = {"kind": "seal", "sigil": kreq["sigil"], "gen": 0, "seal": seal,
                     "parcel": {"home": cid, "lock": kp_["lock"], "salt": kp_["salt"]}}
            s = None
            for g in range(6):
                p = model.parcel(cid, "x", 1, locks.sig(owner.pk), "cd" * 16)
                s = model.sigil_of(p)
                req, _ = spend_req(cid, owner, "cd" * 16, inputs=[[s, g], [kreq["sigil"], 0]], memo="%064x" % g)
                w.spend(req)
                w.release(s, proof)
            w.store.close()
            db = sqlite3.connect(path)
            rows = db.execute("SELECT kind, key, COUNT(*) FROM log GROUP BY kind, key").fetchall()
            db.close()
            self.assertTrue(all(n == 1 for _, _, n in rows), rows)
            again = Witness(kp, reg, self.net.clock, store=WitnessStore(path))
            self.assertEqual(asdict(again.records[s]), asdict(w.records[s]))
            again.store.close()

    def test_store_written_before_compaction_still_loads(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "old.db")
            db = sqlite3.connect(path)
            db.execute("CREATE TABLE log (seq INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT NOT NULL, "
                       "key TEXT NOT NULL, value TEXT NOT NULL)")
            db.executemany("INSERT INTO log (kind, key, value) VALUES (?, ?, ?)",
                           [("pk", "", '"aa"'), ("stamp", "s1", "true"), ("record", "x", '{"gen":0}'),
                            ("record", "x", '{"gen":1}')])
            db.commit()
            db.close()
            st = WitnessStore(path)
            self.assertEqual(st.load()["records"]["x"], {"gen": 1})
            st.append([("record", "x", {"gen": 2})])
            self.assertEqual(st.load()["records"]["x"], {"gen": 2})
            self.assertEqual(st.load()["stamps"], {"s1"})
            st.close()


class CharterCaps(unittest.TestCase):
    def chain(self, n, name="g", sigs=None):
        body = {"name": name, "version": 0, "witnesses": ["%064x" % i for i in range(n)], "prev": None}
        return constellation_id(body), [{"body": body, "sigs": sigs or {}}]

    def test_verification_and_gossip_refuse_oversized_charters(self):
        """Before: one ~1 MiB gossip message registered a 14,000-witness charter."""
        with self.assertRaises(ValueError):
            charter_body("x", 0, ["%064x" % i for i in range(MAX_WITNESSES + 1)], None)
        cases = [(self.chain(14_000), False), (self.chain(MAX_WITNESSES + 1), False), (self.chain(MAX_WITNESSES), True),
                 (self.chain(4, name="n" * MAX_CHARTER_BYTES), False),
                 (self.chain(4, sigs={"%064x" % (10 ** 6 + i): "00" * 64 for i in range(400)}), False)]
        for (cid, chain), ok in cases:
            self.assertEqual(verify_chain(cid, chain), ok)
            self.assertEqual(GossipStore().merge({"charters": {cid: chain}})["charters"], int(ok))
            if ok:
                Registry().add_chain(cid, chain)
                self.assertLessEqual(len(canonical(chain[0])), MAX_CHARTER_BYTES)


class DaemonFlags(unittest.TestCase):
    def test_rate_limit_flags(self):
        from unittest import mock
        from sigil import witnessd
        seen = {}
        with mock.patch.object(witnessd, "run", lambda a: seen.update(vars(a))):
            witnessd.main(["run", "--key", "k", "--registry", "r", "--constellation", "c", "--store", "s"])
            self.assertEqual((seen["rate_limit"], seen["rate_burst"]), (None, RL.DEFAULT_BURST))
            witnessd.main(["run", "--key", "k", "--registry", "r", "--constellation", "c", "--store", "s",
                           "--rate-limit", "0", "--rate-burst", "7"])
            self.assertEqual((seen["rate_limit"], seen["rate_burst"]), (0, 7))


if __name__ == "__main__":
    unittest.main()
