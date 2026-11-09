"""Bugs found by the soak and compatibility suite, pinned as expected failures.

Each test asserts the correct behaviour and is marked ``unittest.expectedFailure`` until the
product code is fixed (this suite does not change product code). The docstrings give the
scenario, the impact and a suggested fix.
"""

import json
import os
import signal
import unittest

from sigil import Wallet, model, wallet_store
from sigil.charter import MAX_WITNESSES, charter_body, charter_hash
from sigil.server import RemoteNetwork

from tests.integration.harness import (Cluster, Daemon, http, make_tmpdir, new_constellation, requires_rust,
                                       write_token)


class _FreezeValidation:
    """FREEZE signs and irreversibly freezes for a successor body that is not a valid next charter.

    Scenario: ``POST /v0/freeze`` (operator call) with ``{"charter": body}`` where ``body["prev"]``
    is the hash of the witness's current charter but ``body`` is otherwise not a valid version
    ``v + 1``: ``version`` 2 (or 0), more than ``MAX_WITNESSES`` (128) witnesses, no witnesses,
    duplicate or non-hex keys, a malformed ``successor`` clause, or no ``name``. Both witnesses
    (``sigil/witness.py`` ``Witness.freeze`` and the Rust ``Witness::freeze``) check only
    ``prev``, then persist ``frozen = H(body)``, answer 200 with a signature on the body, and
    never vote again (also after a restart); every later FREEZE for the real successor is
    refused ("already frozen for a different successor charter").

    Impact: one bad operator request (a buggy rotation tool, a typo in a hand-made charter, or
    anyone holding the admin token, a bearer secret weaker than the witness key) permanently
    removes the witness from its constellation; f + 1 such witnesses block every rotation.
    The witness also signs a body that ``verify_chain`` can never accept. ``Standby.succeed``
    already refuses such bodies ("malformed charter body", "charter too large"), so the two
    roles disagree.

    Suggested fix: before persisting ``frozen``, require ``charter_body(next["name"],
    version + 1, next["witnesses"], prev, next.get("successor")) == next`` (which applies the
    128-witness, uniqueness and successor-clause checks), the same name as the current charter,
    and ``len(enc(next)) <= MAX_CHARTER_BYTES``; refuse otherwise (``rejected``), in both
    implementations.
    """

    KIND = "python"

    def bodies(self, cur: dict) -> dict:
        good = charter_body(cur["name"], 1, ["ab" * 32], charter_hash(cur))
        return {
            "version 2": dict(good, version=2),
            "version 0": dict(good, version=0),
            f"{MAX_WITNESSES + 1} witnesses": dict(good, witnesses=[f"{i:064x}" for i in range(MAX_WITNESSES + 1)]),
            "no witnesses": dict(good, witnesses=[]),
            "duplicate witnesses": dict(good, witnesses=["ab" * 32, "ab" * 32]),
            "malformed successor": dict(good, successor={"x": 1}),
        }

    def test_freeze_refuses_a_malformed_successor(self):
        d = make_tmpdir(self, f"freeze-{self.KIND}")
        token, tfile = write_token(d)
        c = new_constellation(d, "f", 4)
        os.makedirs(os.path.join(d, "logs"))
        with open(c["registry"]) as f:
            cur = json.load(f)[c["cid"]][0]["body"]
        accepted = []
        for i, (name, body) in enumerate(self.bodies(cur).items()):
            dmn = Daemon(self.KIND, c["keys"][0], c["registry"], c["cid"], os.path.join(d, f"s{i}.store"),
                         os.path.join(d, "logs", f"s{i}.log"), args=["--admin-token", tfile]).start()
            try:
                code, _, _ = http(dmn.url, "/v0/freeze", {"charter": body}, headers={"Authorization": f"Bearer {token}"})
                frozen = http(dmn.url, "/v0/info")[1]["ok"]["frozen"]
            finally:
                dmn.stop()
            if code == 200 or frozen:
                accepted.append(name)
        self.assertEqual(accepted, [], f"{self.KIND} froze for invalid successors: {accepted}")


class PythonFreezeValidation(_FreezeValidation, unittest.TestCase):
    __doc__ = _FreezeValidation.__doc__
    KIND = "python"
    test_freeze_refuses_a_malformed_successor = unittest.expectedFailure(
        _FreezeValidation.test_freeze_refuses_a_malformed_successor)


@requires_rust
class RustFreezeValidation(_FreezeValidation, unittest.TestCase):
    __doc__ = _FreezeValidation.__doc__
    KIND = "rust"
    test_freeze_refuses_a_malformed_successor = unittest.expectedFailure(
        _FreezeValidation.test_freeze_refuses_a_malformed_successor)


@requires_rust
class RustGetUnknownPath(unittest.TestCase):
    """The Rust witness answers ``GET /v0/<name>`` for any name but info/charters/proofs with
    HTTP 405 and an empty body, not a JSON error object.

    Scenario: ``GET /v0/nope`` or ``GET /v0/status`` on ``sigil-witness run`` or
    ``sigil-witness standby``. The router registers ``/v0/:method`` for POST only, so axum
    answers 405 Method Not Allowed itself before the JSON ``fallback`` runs. The Python
    daemons answer 404 ``{"error": "bad_request", "message": "unknown path", "vote": null}``
    (and the Rust witness does so too for paths outside ``/v0/``).

    Impact: low. WIRE.md says "Every reply is one JSON object"; a client that parses every
    reply (``RemoteWitness._get``) raises a JSON decode error instead of ``Rejected``. Only
    reachable with a wrong path, so it affects tooling and probes, not payments.

    Suggested fix: in ``server.rs`` add ``.route("/v0/:method", post(call).get(unknown))``
    (or a ``method_not_allowed_fallback``) answering 404 ``bad_request`` "unknown path",
    for both ``router_with_limits`` and ``standby_router``.
    """

    @unittest.expectedFailure
    def test_get_unknown_path_is_json(self):
        d = make_tmpdir(self, "get405")
        c = new_constellation(d, "g", 4)
        os.makedirs(os.path.join(d, "logs"))
        dmn = Daemon("rust", c["keys"][0], c["registry"], c["cid"], os.path.join(d, "w.redb"),
                     os.path.join(d, "logs", "w.log")).start()
        self.addCleanup(dmn.stop)
        for path in ("/v0/nope", "/v0/status"):
            self.assertEqual(http(dmn.url, path)[:2],
                             (404, {"error": "bad_request", "message": "unknown path", "vote": None}), path)


class LegacyWalletPreUpgradeAddress(unittest.TestCase):
    """A wallet saved before ``issued`` was persisted refuses payments to addresses it handed
    out before the upgrade.

    Scenario: a wallet directory whose ``state.json`` has no ``issued`` field (written before
    commit 91269ff) gives a payer a receiving address and is then reloaded by the current
    ``wallet_store.load``. ``load`` sets ``issued`` to the sigils of the parcels the wallet
    already *holds*, so the address handed out earlier is forgotten; when the payment arrives,
    ``Wallet.receive`` raises ``InvalidDossier("parcel is not addressed to us")``.

    Impact: medium for anyone upgrading with payments in flight. The payer's transition is
    already sealed, so the parcel is spent to a lock only this wallet can open, but the wallet
    will not take custody of it; the CLI ``receive`` fails and the value is stranded until
    someone edits ``state.json`` by hand. (The README tells users payments are handed over as
    files, possibly long after the address was given out.)

    Suggested fix: for a legacy ``state.json`` without ``issued``, also accept a parcel whose
    lock is ``sig(pk)`` for a ``pk`` in ``keys.json`` that no held or spent parcel uses yet
    (``address()`` makes one fresh key per address, so such a key identifies an address this
    wallet issued), or record ``issued`` lazily from ``keys.json`` on first load.
    """

    @unittest.expectedFailure
    def test_address_issued_before_upgrade_still_receives(self):
        d = make_tmpdir(self, "legacy-issued")
        c = Cluster(d)
        self.addCleanup(c.stop_all, signal.SIGKILL)
        X = c.create("orion", ["python"] * 4)
        c.start_all()
        net = RemoteNetwork(c.directory(), timeout=10)
        payer, old = Wallet("payer", net, X), Wallet("old", net, X)
        usd = payer.issue("USD", 100)
        payer.pay(old, usd, 10)
        addr = old.address()                 # handed to the payer before the upgrade
        wd = os.path.join(d, "old")
        wallet_store.save(old, wd)
        p = os.path.join(wd, "state.json")
        with open(p) as f:
            st = json.load(f)
        del st["issued"]                     # the format before 91269ff
        with open(p, "w") as f:
            json.dump(st, f)
        upgraded = wallet_store.load(wd, RemoteNetwork(c.directory(), timeout=10))
        refs, outs = payer.payment_outputs(usd, 5, addr)
        tid = payer.transact(refs, outs)
        upgraded.receive(payer.dossier.ancestry([tid]), [model.ref(tid, 0)])
        self.assertEqual(upgraded.balance(usd), 15)


class KillSwitchDust(unittest.TestCase):
    """Every atomic swap leaves each party a new, never-reused kill-switch parcel.

    Scenario (found by the soak: wallet holdings and ``state.json`` grow with the number of
    swaps): ``propose_swap`` calls ``Wallet.kill_switch()`` for both parties, which *issues a
    new asset* ("kill-switch", supply 1) every time, adds its sigil to ``kill_switches``
    forever, and the swap pays the unit back to a fresh address of the same party. That
    returned parcel is never used as a kill switch again (``kill_switch`` always issues), and
    no sigil is ever removed from ``kill_switches``. After N swaps a wallet holds N worthless
    1-unit parcels of N different assets, N genesis transitions in its dossier and N entries in
    ``kill_switches``, all saved on every ``wallet_store.save``.

    Impact: low. Unbounded growth of wallet state and of the dossiers handed to swap
    counter-parties, proportional to swaps made, not to value held; ``select`` and ``balance``
    scan the dust on every call. Measured in the 180 s soak: 130-210 holdings per wallet.

    Suggested fix: in ``kill_switch``, reuse an unpledged kill-switch parcel the wallet already
    holds (the unit returned by an earlier swap) and only issue when there is none; drop sigils
    from ``kill_switches`` once they are spent or no longer held.
    """

    @unittest.expectedFailure
    def test_swaps_do_not_accumulate_kill_switch_parcels(self):
        from sigil import Network
        from sigil.swap import atomic_swap
        net = Network()
        X = net.create_constellation("x", n=4)
        a, b = Wallet("a", net, X), Wallet("b", net, X)
        usd, gold = a.issue("USD", 1000), b.issue("GOLD", 1000)
        for _ in range(20):
            atomic_swap(a, usd, 1, b, gold, 1)
        dust = [h for h in a.holdings.values() if h["parcel"]["asset"] not in (usd, gold)]
        self.assertLessEqual(len(dust), 2, f"{len(dust)} kill-switch parcels after 20 swaps")
        self.assertLessEqual(len(a.kill_switches), 2)


if __name__ == "__main__":
    unittest.main()
