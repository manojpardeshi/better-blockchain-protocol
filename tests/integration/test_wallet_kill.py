"""The CLI wallet process killed mid-payment, against real Rust and Python witness processes.

``tests/test_wallet_crash.py`` enumerates every crash point in process. Here the wallet is a real
``python -m sigil.cli pay`` process that dies with ``os._exit`` (no cleanup, like SIGKILL) at its
k-th witness call (before it is sent) or at its k-th file write, for a spread of k, against a
mixed constellation with a successor committee. After each kill the next ``sigil pay`` settles
the interrupted payment (completing it and handing out its payment file, or dropping a pledge
that bound nothing), every payment file is received, and the global invariants hold: balances
equal verified parcels, supply conserved, nothing consumed twice.
"""

import glob
import os
import subprocess
import sys
import textwrap
import time

from tests.integration.harness import MIXED, ROOT, IntegrationCase, _env

WRAPPER = textwrap.dedent('''
    import os, sys
    K, WHAT = int(os.environ["SIGIL_KILL_AT"]), os.environ["SIGIL_KILL_WHAT"]
    n = [0]
    def tick():
        n[0] += 1
        if n[0] == K:
            os._exit(137)
    from sigil import server, wallet_store
    if WHAT == "call":
        orig = server.RemoteWitness._call
        def _call(self, method, body):
            if method in ("spend", "mirror", "status", "release", "note_release"):
                tick()
            return orig(self, method, body)
        server.RemoteWitness._call = _call
    else:
        orig_w = wallet_store._atomic_write
        def aw(*a, **kw):
            tick()
            return orig_w(*a, **kw)
        wallet_store._atomic_write = aw
    from sigil import cli
    sys.exit(cli.main(sys.argv[1:]))
''')


class WalletKilled(IntegrationCase):
    def test_cli_pay_killed_at_many_points(self):
        c = self.c
        X, idx = c.constellation("orion", MIXED, committee=["rust", "python", "rust", "python"], dead_man=600,
                                 start=False)
        c.start_all()
        d = {"constellations": c.directory(), "committees": c.committees()}
        import json
        with open(self.directory_file, "w") as f:
            json.dump(d, f)
        for who in ("alice", "bob"):
            self.cli(who, "init", "--home", X, "--name", who)
            state = os.path.join(self.wpath(who), "state.json")   # short pledges: the test waits them out
            with open(state) as f:
                st = json.load(f)
            st["pledge_ttl"], st["max_skew"] = 3, 1
            with open(state, "w") as f:
                json.dump(st, f)
        usd = self.cli("alice", "issue", "USD", "1000")["asset"]
        wrapper = self.file("killer.py")
        with open(wrapper, "w") as f:
            f.write(WRAPPER)
        points = [("call", k) for k in (1, 3, 6, 9, 12, 15, 18)] + [("write", k) for k in (1, 2, 3, 4, 5, 6, 7, 9)]
        killed = 0
        for what, k in points:
            out = self.file(f"pay-{what}-{k}.json")
            addr = self.address_file("bob")
            cmd = [sys.executable, wrapper, "--wallet", self.wpath("alice"), "--directory", self.directory_file,
                   "pay", addr, usd, "7", "--out", out]
            p = subprocess.run(cmd, cwd=ROOT, env=dict(_env(), SIGIL_KILL_AT=str(k), SIGIL_KILL_WHAT=what),
                               capture_output=True, text=True, timeout=120)
            killed += p.returncode == 137
            if p.returncode not in (0, 137):
                w = self.load_wallet("alice")
                self.fail(f"{what} {k}: {p.stderr} pledged={w.pledged} pending={list(w.pending)}")
            if p.returncode == 137:
                time.sleep(5)      # the interrupted pledge expires; the next pay settles it
        self.assertGreater(killed, 8)
        # Settle: time passes past every authorisation's expiry; alice pays once more (which
        # settles and hands out what was interrupted); bob receives every payment file.
        time.sleep(1)
        self._settle_and_receive(usd)
        alice, bob = self.load_wallet("alice"), self.load_wallet("bob")
        self.assertEqual(alice.balance(usd) + bob.balance(usd), 1000)
        live = {h["sigil"] for h in alice.holdings.values()} & set(alice.pledged)
        self.assertEqual(live, set(), "a pledge was left unsettled")
        self.check_invariants({"alice": alice, "bob": bob})

    def _settle_and_receive(self, usd):
        alice = self.load_wallet("alice")
        expires = max((e for _g, _t, e in alice.pledged.values()), default=0)
        while time.time() <= expires + alice.max_skew + 1:
            time.sleep(1)
        for _ in range(3):
            pay, _r = self.cli_pay("alice", "bob", usd, 1)
        for path in sorted(glob.glob(self.file("pay-*.json*"))):
            if os.path.getsize(path):
                self.cli("bob", "receive", path)
