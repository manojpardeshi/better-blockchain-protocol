"""CLI and daemon operability: clean start/stop, bad configs, SIGTERM under load, docker-compose.

* Both daemons (``python -m sigil.witnessd`` and ``sigil-witness``), witness and standby, stop
  on SIGTERM and SIGINT with exit code 0, a final ``stopped`` line, the port released and a
  store that reopens with the same identity.
* SIGTERM while clients are spending: every vote a client received is still there after the
  restart (persist before answering, SPEC §5), and nothing else is.
* Bad configurations make the daemon exit non-zero promptly, without serving, and say what
  is wrong (the last line of its output names the problem).
* ``docker compose config`` accepts docker-compose.yml (skipped without docker).
"""

import json
import os
import shutil
import signal
import socket
import subprocess
import threading
import time
import unittest

from sigil import locks, model
from sigil.crypto import KeyPair

from tests.integration.harness import (ROOT, Daemon, daemon_cmd, free_port, http, make_tmpdir, new_constellation,
                                       requires_rust, run_cli, rust_available, witnessd, write_token)

KINDS = ["python"] + (["rust"] if rust_available() else [])


def port_free(port: int) -> bool:
    with socket.socket() as s:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)   # as the daemons bind (TIME_WAIT is fine)
        try:
            s.bind(("127.0.0.1", port))
            return True
        except OSError:
            return False


class Spender:
    """Signs spend requests for fresh sigils of one constellation."""

    def __init__(self, cid: str):
        self.cid = cid
        self.owner = KeyPair.from_seed(os.urandom(32))
        self.exp = int(time.time()) + 3600

    def request(self, tag: str) -> dict:
        p = model.parcel(self.cid, "x", 1, locks.sig(self.owner.pk), os.urandom(16).hex())
        s = model.sigil_of(p)
        h = {"inputs": [[s, 0]], "body": model.body_hash({"tag": tag})}
        u = locks.empty_unlock(self.exp)
        u["sigs"][self.owner.pk] = locks.sign_unlock(self.owner, s, model.transition_id(h), self.exp)
        return {"sigil": s, "header": h, "home": self.cid, "lock": p["lock"], "salt": p["salt"], "unlock": u}


class DaemonLifecycleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = cls.d = make_tmpdir(cls, "ops")
        cls.token, cls.tfile = write_token(d)
        cls.c = new_constellation(d, "ops", 4, committee=4, dead_man=60)
        os.makedirs(os.path.join(d, "logs"))

    def daemon(self, kind: str, role: str = "witness", idx: int = 0, store: str | None = None, args=()) -> Daemon:
        c = self.c
        key = (c["committee"] if role == "standby" else c["keys"])[idx]
        ext = "redb" if kind == "rust" else "db"
        store = store or os.path.join(self.d, f"{role}-{kind}-{os.urandom(3).hex()}.{ext}")
        dmn = Daemon(kind, key, c["registry"], c["cid"], store, store + ".log", role=role,
                     args=["--admin-token", self.tfile, *args])
        self.addCleanup(lambda: dmn.proc and dmn.stop(signal.SIGKILL))
        return dmn

    def test_clean_stop_on_sigterm_and_sigint(self):
        for kind in KINDS:
            for role in ("witness", "standby"):
                for sig in (signal.SIGTERM, signal.SIGINT):
                    with self.subTest(kind=kind, role=role, sig=sig.name):
                        dmn = self.daemon(kind, role).start()
                        pk = http(dmn.url, "/v0/info")[1]["ok"]["pk"]
                        t = time.monotonic()
                        code = dmn.stop(sig)
                        self.assertEqual(code, 0)
                        self.assertLess(time.monotonic() - t, 10)
                        log = open(dmn.log).read()
                        self.assertEqual(log.strip().splitlines()[-1], "stopped", log[-300:])
                        self.assertNotIn("Traceback", log)
                        self.assertTrue(port_free(dmn.port), "port still bound after exit")
                        dmn.start()                                   # same store, same identity
                        self.assertEqual(http(dmn.url, "/v0/info")[1]["ok"]["pk"], pk)
                        dmn.stop()

    def test_sigterm_under_load_keeps_every_answered_vote(self):
        for kind in KINDS:
            with self.subTest(kind=kind):
                dmn = self.daemon(kind, args=())
                # A plain witness of a constellation without a committee: votes need no acks.
                c2 = new_constellation(os.path.join(self.d, f"load-{kind}"), "load", 4)
                dmn.registry, dmn.cid, dmn.key = c2["registry"], c2["cid"], c2["keys"][0]
                dmn.start()
                sp = Spender(c2["cid"])
                reqs = [sp.request(str(i)) for i in range(400)]
                got: dict = {}
                lock = threading.Lock()
                started = threading.Event()

                def client(chunk):
                    for r in chunk:
                        started.set()
                        try:
                            code, body, _ = http(dmn.url, "/v0/spend", {"request": r}, timeout=5)
                        except OSError:
                            return
                        if code == 200:
                            with lock:
                                got[r["sigil"]] = body["ok"]

                threads = [threading.Thread(target=client, args=(reqs[i::4],)) for i in range(4)]
                for t in threads:
                    t.start()
                started.wait(10)
                deadline = time.monotonic() + 10
                while len(got) < 40 and time.monotonic() < deadline:
                    time.sleep(0.005)
                self.assertEqual(dmn.stop(signal.SIGTERM), 0)
                for t in threads:
                    t.join(30)
                self.assertGreater(len(got), 0)
                dmn.start()
                for s, vote in got.items():
                    st = http(dmn.url, "/v0/status", {"sigil": s})[1]["ok"]
                    self.assertEqual(st["votes"], [vote], f"{kind}: an answered vote was lost on SIGTERM")
                # Nothing beyond what clients sent was invented, and unanswered ones are either absent or bound.
                bound = sum(1 for r in reqs if http(dmn.url, "/v0/status", {"sigil": r["sigil"]})[1]["ok"]["tid"])
                self.assertGreaterEqual(bound, len(got))
                self.assertLessEqual(bound, len(reqs))
                dmn.stop()


class BadConfigTests(unittest.TestCase):
    """Each bad configuration: non-zero exit within 15 s, nothing served, and a last output
    line naming the problem."""

    @classmethod
    def setUpClass(cls):
        d = cls.d = make_tmpdir(cls, "cfg")
        cls.c = new_constellation(d, "cfg", 4)
        # A second constellation whose genesis also names key 0 (store-constellation mix-up).
        k0pub = cls.c["keys"][0][:-5] + ".pub"
        others = [os.path.join(d, "keys", f"other-{i}.json") for i in range(3)]
        for k in others:
            witnessd("keygen", "--out", k)
        cls.other_cid = witnessd("genesis", "--name", "other", "--out", cls.c["registry"],
                                 "--keys", k0pub, *(k[:-5] + ".pub" for k in others))

        def w(name, text):
            p = os.path.join(d, name)
            with open(p, "w") as f:
                f.write(text)
            return p

        with open(cls.c["keys"][0]) as f:
            seed = json.load(f)["seed"]
        with open(cls.c["registry"]) as f:
            reg = json.load(f)
        reg[cls.c["cid"]][0]["body"]["name"] = "tampered"
        cls.files = {
            "bad_json": w("bad.json", "{nope"),
            "mismatch": w("mismatch.json", json.dumps({"seed": seed, "pk": "ab" * 32})),
            "empty_token": w("empty.token", "\n"),
            "garbage": w("garbage.store", "this is not a database" * 100),
            "tampered": w("tampered.json", json.dumps(reg)),
        }
        cls.outsider = os.path.join(d, "outsider.json")
        witnessd("keygen", "--out", cls.outsider)
        cls.listener = socket.socket()
        cls.listener.bind(("127.0.0.1", 0))
        cls.listener.listen()
        cls.addClassCleanup(cls.listener.close)
        cls.bound = {}
        for kind in KINDS:   # a store that belongs to key 0 of cfg
            st = os.path.join(d, f"bound-{kind}.{'redb' if kind == 'rust' else 'db'}")
            Daemon(kind, cls.c["keys"][0], cls.c["registry"], cls.c["cid"], st, st + ".log").start().stop()
            cls.bound[kind] = st

    def run_daemon(self, kind, *, sub="run", key=None, registry=None, cid=None, store=None, port=None, extra=()):
        ext = "redb" if kind == "rust" else "db"
        store = store or os.path.join(self.d, f"{kind}-{os.urandom(4).hex()}.{ext}")
        port = port or free_port()
        args = [sub, "--key", key or self.c["keys"][0], "--registry", registry or self.c["registry"],
                "--constellation", cid or self.c["cid"], "--store", store, "--port", str(port), *extra]
        try:
            out = run_cli(daemon_cmd(kind, *args), timeout=15)
        except subprocess.TimeoutExpired:
            return None, "", port
        text = (out.stderr.strip() or out.stdout.strip()).splitlines()
        return out.returncode, (text[-1] if text else ""), out.stderr

    def cases(self, kind: str) -> dict:
        d, f = self.d, self.files
        return {
            "missing key file": (dict(key=os.path.join(d, "nope.json")), "nope.json"),
            "malformed key file": (dict(key=f["bad_json"]), ""),
            "key seed does not match pk": (dict(key=f["mismatch"]), "does not match"),
            "missing registry": (dict(registry=os.path.join(d, "nope-reg.json")), "nope-reg.json"),
            "tampered registry": (dict(registry=f["tampered"]), "invalid charter chain"),
            "constellation not in registry": (dict(cid="ab" * 32), "not in"),
            "key not a member": (dict(key=self.outsider), "not a member"),
            "store of another key": (dict(key=self.c["keys"][1], store=self.bound[kind]), "different witness key"),
            "store of another constellation": (dict(cid=self.other_cid, store=self.bound[kind]), "constellation"),
            "empty admin token": (dict(extra=("--admin-token", f["empty_token"])), "empty admin token"),
            "missing admin token": (dict(extra=("--admin-token", os.path.join(d, "nope.token"))), "nope.token"),
            "port in use": (dict(port=self.listener.getsockname()[1]), "in use"),
            "unresolvable host": (dict(extra=("--host", "999.1.1.1")), ""),
            "zero burst": (dict(extra=("--rate-limit", "5", "--rate-burst", "0")), "burst"),
            "store directory missing": (dict(store=os.path.join(d, "nodir", "x.store")), ""),
            "garbage store": (dict(store=f["garbage"]), ""),
            "standby key not in committee": (dict(sub="standby"), "successor committee"),
        }

    def test_bad_configs_exit_with_a_clear_error(self):
        for kind in KINDS:
            for name, (kw, hint) in self.cases(kind).items():
                with self.subTest(kind=kind, case=name):
                    code, last, _ = self.run_daemon(kind, **kw)
                    self.assertIsNotNone(code, "daemon kept running")
                    self.assertNotEqual(code, 0, last)
                    self.assertTrue(last, "no error message")
                    self.assertIn(hint.lower(), last.lower())


class DaemonConfigFindings(BadConfigTests):
    """Operability bugs in config handling (expected failures; see each test)."""

    test_bad_configs_exit_with_a_clear_error = None

    @unittest.expectedFailure
    def test_python_config_errors_without_traceback(self):
        """The Python daemon reports most bad configurations with a raw traceback.

        Scenario: ``python -m sigil.witnessd run`` with a missing or malformed key file, a
        missing registry or admin-token file, a store of another key, a port in use, an
        unresolvable host, an unopenable or corrupt store, a tampered registry. It exits 1
        with a ~10-line Python traceback (FileNotFoundError, JSONDecodeError, ValueError,
        OSError, sqlite3.DatabaseError ...). Only a few checks use ``SystemExit(msg)`` (not a
        member, constellation not in registry, empty token). The Rust daemon prints one line
        ``sigil-witness: <problem>`` for all of them.

        Impact: low (operability). The exception text is on the last line, but operators and
        supervisors (systemd, docker logs) see a crash dump, and some messages lose context
        (``unable to open database file`` without the path; ``Name or service not known``
        without the host).

        Suggested fix: in ``witnessd.main``, catch ``(OSError, ValueError, sqlite3.Error)``
        around ``run``/``standby`` setup and ``raise SystemExit(f"sigil.witnessd: {path}: {e}")``,
        as the Rust ``main`` does.
        """
        tracebacks = []
        for name, (kw, _hint) in self.cases("python").items():
            _code, _last, stderr = self.run_daemon("python", **kw)
            if isinstance(stderr, str) and "Traceback" in stderr:
                tracebacks.append(name)
        self.assertEqual(tracebacks, [])

    def _rate_case(self, kind: str):
        """Start on 0.0.0.0 with each bad value: the daemon must refuse to start; if it starts,
        show it has no admission control (150 requests from one client, no 429)."""
        unlimited = []
        for value in ("-1", "nan", "-inf"):
            ext = "redb" if kind == "rust" else "db"
            store = os.path.join(self.d, f"rate-{kind}-{os.urandom(3).hex()}.{ext}")
            dmn = Daemon(kind, self.c["keys"][0], self.c["registry"], self.c["cid"], store, store + ".log",
                         host="0.0.0.0", args=[f"--rate-limit={value}"])
            try:
                dmn.start()
            except (RuntimeError, TimeoutError):
                continue   # refused: correct
            try:
                codes = {http(dmn.url, "/v0/status", {"sigil": "00" * 32})[0] for _ in range(150)}
            finally:
                dmn.stop(signal.SIGKILL)
            if 429 not in codes:
                unlimited.append(value)
        self.assertEqual(unlimited, [], f"{kind} served without a rate limit on 0.0.0.0 for --rate-limit {unlimited}")

    @unittest.expectedFailure
    def test_python_refuses_negative_or_nan_rate_limit(self):
        """A negative or NaN ``--rate-limit`` silently turns admission control off.

        Scenario: ``witnessd run --host 0.0.0.0 --rate-limit -1`` (or ``nan``, ``-inf``).
        ``WitnessServer`` builds a limiter only ``if rate_limit > 0``, so any non-positive
        value means "no limit"; only ``0`` is documented to do that (WIRE.md "Admission
        control"). The same holds for ``standby``. The Rust daemon behaves the same
        (``if rate > 0.0``) for ``--rate-limit=-1``; with a space, clap happens to reject
        ``-1`` as an unknown flag.

        Impact: low. A typo in a deployment config fails open: a witness on a public address
        serves every client without a limit (resource exhaustion, AI_THREAT_MODEL §2.6).

        Suggested fix: reject ``rate_limit < 0`` and non-finite values at argument parsing
        (``argparse`` type / clap ``value_parser`` with a range), keeping ``0`` as "off".
        """
        self._rate_case("python")

    @requires_rust
    @unittest.expectedFailure
    def test_rust_refuses_negative_or_nan_rate_limit(self):
        """As ``test_python_refuses_negative_or_nan_rate_limit``, for ``sigil-witness run``."""
        self._rate_case("rust")


class DockerComposeTests(unittest.TestCase):
    def test_compose_file_validates(self):
        docker = shutil.which("docker")
        if docker is None:
            self.skipTest("docker not installed")
        if subprocess.run([docker, "compose", "version"], capture_output=True).returncode != 0:
            self.skipTest("docker compose not available")
        out = subprocess.run([docker, "compose", "-f", os.path.join(ROOT, "docker-compose.yml"), "config",
                              "--format", "json"], capture_output=True, text=True, cwd=ROOT, timeout=60)
        self.assertEqual(out.returncode, 0, out.stderr)
        cfg = json.loads(out.stdout)
        witnesses = {n: s for n, s in cfg["services"].items() if n.startswith("witness")}
        self.assertEqual(len(witnesses), 4)
        for name, svc in witnesses.items():
            cmd = " ".join(svc["command"])
            # Published on loopback only, so the documented --rate-limit 0 is safe (WIRE.md).
            self.assertTrue(all(p.get("host_ip") == "127.0.0.1" for p in svc["ports"]), (name, svc["ports"]))
            self.assertIn("--rate-limit 0", cmd, name)
            self.assertIn("--store /data/", cmd, name)
            self.assertEqual(svc.get("stop_signal"), "SIGTERM", name)
        self.assertTrue(os.path.exists(os.path.join(ROOT, "testnet", "docker-init.sh")))


if __name__ == "__main__":
    unittest.main()
