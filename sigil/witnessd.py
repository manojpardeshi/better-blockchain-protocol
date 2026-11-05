"""The witness daemon: one witness, one durable store, served over HTTP.

    python -m sigil.witnessd keygen  --out key.json
    python -m sigil.witnessd genesis --name orion --keys k1.pub k2.pub k3.pub k4.pub --out registry.json \\
                                     [--committee m1.pub m2.pub m3.pub m4.pub --dead-man SECONDS]
    python -m sigil.witnessd run     --key key.json --registry registry.json --constellation <cid> \\
                                     --store data.db [--host 127.0.0.1] [--port 7000] [--stamps] \\
                                     [--admin-token FILE] [--adopt] [--rate-limit R] [--rate-burst B]
    python -m sigil.witnessd standby --key key.json --registry registry.json --constellation <cid> \\
                                     --store standby.db [--host 127.0.0.1] [--port 7100] [--wait] \\
                                     [--admin-token FILE] [--members URL ...] [--probe-every S] \\
                                     [--rate-limit R] [--rate-burst B]

``keygen`` writes the private key (mode 0600) and its public key next to it
(``key.pub``). ``genesis`` builds charter version 0 from public keys and
writes a charter registry (docs/WIRE.md). ``run`` verifies the registry,
restores the witness from its store (or joins the constellation on first
start) and serves it until SIGTERM or SIGINT.

A fresh store joins charter version 0 directly. A later version is only ever
entered by ADOPT (SPEC §5.4), with the evidence of its predecessors: start a
new member with ``--adopt`` and it waits, voting on nothing, until an operator
sends ``/v0/adopt`` (``RemoteNetwork.rotate`` does). The rotation calls
(``/v0/freeze``, ``/v0/adopt``) need the token in ``--admin-token FILE``;
without it they are disabled.

A witness listening on a non-loopback ``--host`` limits each client to
``--rate-limit`` requests per second (default 20, bursts of ``--rate-burst``,
default 100; docs/WIRE.md "Admission control"); ``--rate-limit 0`` disables it.
On loopback there is no limit unless ``--rate-limit`` asks for one.

``standby`` serves a member of a successor committee (SPEC §5.5): it mirrors
bindings for clients, probes the version's members for heartbeats
(``--members``, every ``--probe-every`` seconds) and signs a successor when
asked cooperatively or once the dead-man period has passed (``/v0/standby``,
``/v0/succeed`` and ``/v0/probe`` need ``--admin-token``). A fresh store stands
by for version 0 at once; with ``--wait`` it waits for the handover of a later
version (docs/WIRE.md "Succession").

Every vote is made durable before it is sent (SPEC §5), so the daemon may be
killed at any moment, even with SIGKILL, and restarted on the same store.
"""

import argparse
import json
import os
import signal
import sys
import threading
import time

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from .charter import Registry, charter_body, constellation_id, successor_clause
from .crypto import KeyPair
from .ratelimit import DEFAULT_BURST, DEFAULT_RATE
from .server import StandbyServer, WitnessServer
from .stamps import StampMint
from .store import WitnessStore
from .succession import Standby, StandbyStore
from .witness import Witness


# ------------------------------------------------------------------- files

def _write_private(path: str, obj: dict) -> None:
    """Write JSON readable only by its owner, never briefly world-readable."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as f:
        json.dump(obj, f)
    os.chmod(path, 0o600)  # the file may have existed with looser permissions


def _write_json(path: str, obj) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, path)


def pub_path(key_path: str) -> str:
    return os.path.splitext(key_path)[0] + ".pub"


def generate_key(out: str) -> KeyPair:
    """Write a fresh Ed25519 key to ``out`` (0600) and its public key to ``*.pub``."""
    seed = os.urandom(32)
    kp = KeyPair(Ed25519PrivateKey.from_private_bytes(seed))
    _write_private(out, {"seed": seed.hex(), "pk": kp.pk})
    with open(pub_path(out), "w") as f:
        f.write(kp.pk + "\n")
    return kp


def load_key(path: str) -> KeyPair:
    with open(path) as f:
        data = json.load(f)
    kp = KeyPair(Ed25519PrivateKey.from_private_bytes(bytes.fromhex(data["seed"])))
    if data.get("pk", kp.pk) != kp.pk:
        raise ValueError(f"{path}: public key does not match seed")
    return kp


def read_pk(arg: str) -> str:
    """A public key given as hex, a ``.pub`` file or a key file."""
    if not os.path.exists(arg):
        bytes.fromhex(arg)
        return arg.lower()
    with open(arg) as f:
        text = f.read().strip()
    return json.loads(text)["pk"] if text.startswith("{") else text


def genesis(name: str, pks: list, committee: list | None = None, dead_man: int | None = None) -> tuple[str, dict]:
    """Charter version 0 of a new constellation: returns ``(cid, registry entry)``.

    ``committee`` (public keys) and ``dead_man`` (seconds) give it a successor
    committee (SPEC §5.5).
    """
    succ = successor_clause(committee, dead_man) if committee else None
    body = charter_body(name, 0, pks, None, succ)
    return constellation_id(body), [{"body": body, "sigs": {}}]


def load_registry(path: str) -> Registry:
    """Load a charter registry file, verifying every chain (invalid ones are fatal)."""
    with open(path) as f:
        chains = json.load(f)
    reg = Registry()
    for cid, chain in chains.items():
        reg.add_chain(cid, chain)
    return reg


def load_mint(path: str, bits: int = 2048) -> StampMint:
    """The stamp-signing key, created on first use and kept across restarts.

    A new key after a restart would invalidate every stamp sold before it.
    """
    if not os.path.exists(path):
        mint = StampMint(bits)
        _write_private(path, {k: format(v, "x") for k, v in mint.numbers().items()})
        return mint
    with open(path) as f:
        k = json.load(f)
    # Redeemed serials come back from the witness store.
    return StampMint.from_numbers(int(k["n"], 16), int(k["e"], 16), int(k["d"], 16))


# --------------------------------------------------------------------- run

def load_admin_token(path: str | None) -> str | None:
    """The operator token for the rotation calls (``None``: rotation calls disabled)."""
    if path is None:
        return None
    with open(path) as f:
        token = f.read().strip()
    if not token:
        raise SystemExit(f"{path}: empty admin token")
    return token


def build_witness(key: str, registry: str, cid: str, store: str, stamps: bool = False,
                  adopt: bool = False) -> Witness:
    kp = load_key(key)
    reg = load_registry(registry)
    if cid not in reg:
        raise SystemExit(f"constellation {cid} is not in {registry}")
    mint = load_mint(store + ".stamps.json") if stamps else None
    w = Witness(kp, reg, lambda: int(time.time()), stamp_mint=mint, store=WitnessStore(store))
    if w.cid is None and not adopt:
        # First start: join version 0. A later version must be entered by ADOPT,
        # which brings the predecessors' bindings; joining it bare could vote a
        # second transition for a sigil the constellation already consumed.
        chain = reg.chain(cid)
        if not any(kp.pk in c["body"]["witnesses"] for c in chain):
            raise SystemExit(f"{kp.pk[:12]} is not a member of {cid[:12]}")
        if len(chain) > 1:
            raise SystemExit(f"{cid[:12]} has rotated past version 0: a fresh store joins a later "
                             "version only by ADOPT (start with --adopt)")
        w.join(cid, 0)
    elif w.cid is not None and w.cid != cid:
        raise SystemExit(f"store {store} belongs to constellation {w.cid}, not {cid}")
    return w


def build_standby(key: str, registry: str, cid: str, store: str, wait: bool = False) -> Standby:
    """A successor-committee member (SPEC §5.5), restored from its store.

    A fresh store stands by for version 0 at once if the key is in version 0's
    committee and the constellation has not rotated; otherwise (or with ``wait``)
    it waits for ``/v0/standby`` with the handover of a later version.
    """
    kp = load_key(key)
    reg = load_registry(registry)
    if cid not in reg:
        raise SystemExit(f"constellation {cid} is not in {registry}")
    m = Standby(kp, reg, lambda: int(time.time()), store=StandbyStore(store))
    if m.cid is None and not wait:
        chain = reg.chain(cid)
        succ = chain[0]["body"].get("successor")
        if succ is None or kp.pk not in succ["committee"]:
            raise SystemExit(f"{kp.pk[:12]} is not in the successor committee of {cid[:12]} version 0")
        if len(chain) > 1:
            raise SystemExit(f"{cid[:12]} has rotated past version 0: start with --wait for /v0/standby")
        m.enter(cid, 0, [])
    elif m.cid is not None and m.cid != cid:
        raise SystemExit(f"store {store} belongs to constellation {m.cid}, not {cid}")
    return m


def standby(args) -> None:
    token = load_admin_token(args.admin_token)
    m = build_standby(args.key, args.registry, args.constellation, args.store, args.wait)
    server = StandbyServer(m, args.host, args.port, admin_token=token, members=args.members,
                           probe_every=args.probe_every, rate_limit=args.rate_limit,
                           rate_burst=args.rate_burst).start()
    stop = threading.Event()
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, lambda *_: stop.set())
    where = f"{m.cid[:12]} v{m.version}" if m.cid else f"(awaiting STANDBY into {args.constellation[:12]})"
    print(f"standby {m.pk[:12]} for {where} listening on {server.url}", flush=True)
    stop.wait()
    server.stop()
    with server._lock:
        m.store.close()
    print("stopped", flush=True)


def run(args) -> None:
    token = load_admin_token(args.admin_token)
    w = build_witness(args.key, args.registry, args.constellation, args.store, args.stamps, args.adopt)
    server = WitnessServer(w, args.host, args.port, admin_token=token, rate_limit=args.rate_limit,
                           rate_burst=args.rate_burst).start()
    stop = threading.Event()
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, lambda *_: stop.set())
    if w.cid is None:
        print(f"witness {w.pk[:12]} awaiting ADOPT into {args.constellation[:12]} listening on {server.url}",
              flush=True)
    else:
        print(f"witness {w.pk[:12]} of {w.cid[:12]} v{w.version} listening on {server.url}", flush=True)
    stop.wait()
    server.stop()
    with server._lock:  # wait for an in-flight call to finish its write
        w.store.close()
    print("stopped", flush=True)


# --------------------------------------------------------------------- cli

def main(argv=None) -> None:
    p = argparse.ArgumentParser(prog="python -m sigil.witnessd", description="Sigil witness daemon")
    sub = p.add_subparsers(dest="cmd", required=True)

    k = sub.add_parser("keygen", help="generate a witness key")
    k.add_argument("--out", required=True)

    g = sub.add_parser("genesis", help="create a constellation from witness public keys")
    g.add_argument("--name", required=True)
    g.add_argument("--keys", nargs="+", required=True, help="public keys: .pub files, key files or hex")
    g.add_argument("--out", required=True, help="registry file (merged into if it exists)")
    g.add_argument("--committee", nargs="+", help="successor committee public keys (SPEC 5.5)")
    g.add_argument("--dead-man", type=int, help="dead-man period in seconds (with --committee)")

    sb = sub.add_parser("standby", help="serve a successor-committee member (SPEC 5.5)")
    sb.add_argument("--key", required=True)
    sb.add_argument("--registry", required=True)
    sb.add_argument("--constellation", required=True)
    sb.add_argument("--store", required=True)
    sb.add_argument("--host", default="127.0.0.1")
    sb.add_argument("--port", type=int, default=7100)
    sb.add_argument("--admin-token", metavar="FILE",
                    help="file holding the operator token that authorises /v0/standby, /v0/succeed, /v0/probe")
    sb.add_argument("--wait", action="store_true",
                    help="on a fresh store, wait for /v0/standby into a later charter version")
    sb.add_argument("--members", nargs="*", default=[], help="member URLs to probe for heartbeats")
    sb.add_argument("--probe-every", type=float, help="probe the members every this many seconds")
    sb.add_argument("--rate-limit", type=float, metavar="R", default=None,
                    help=f"requests per second per client (0: no limit; default {DEFAULT_RATE:g} on a "
                         "non-loopback host, none on loopback)")
    sb.add_argument("--rate-burst", type=int, metavar="B", default=DEFAULT_BURST,
                    help=f"requests a client may burst above the rate (default {DEFAULT_BURST})")

    r = sub.add_parser("run", help="serve a witness")
    r.add_argument("--key", required=True)
    r.add_argument("--registry", required=True)
    r.add_argument("--constellation", required=True)
    r.add_argument("--store", required=True)
    r.add_argument("--host", default="127.0.0.1")
    r.add_argument("--port", type=int, default=7000)
    r.add_argument("--stamps", action="store_true", help="require a stamp with every spend")
    r.add_argument("--admin-token", metavar="FILE",
                   help="file holding the operator token that authorises /v0/freeze and /v0/adopt")
    r.add_argument("--adopt", action="store_true",
                   help="on a fresh store, do not join: wait for /v0/adopt into a later charter version")
    r.add_argument("--rate-limit", type=float, metavar="R", default=None,
                   help=f"requests per second per client (0: no limit; default {DEFAULT_RATE:g} on a "
                        "non-loopback host, none on loopback)")
    r.add_argument("--rate-burst", type=int, metavar="B", default=DEFAULT_BURST,
                   help=f"requests a client may burst above the rate (default {DEFAULT_BURST})")

    args = p.parse_args(argv)
    if args.cmd == "keygen":
        print(generate_key(args.out).pk)
    elif args.cmd == "genesis":
        if bool(args.committee) != (args.dead_man is not None):
            raise SystemExit("--committee and --dead-man go together")
        cid, chain = genesis(args.name, [read_pk(a) for a in args.keys],
                             [read_pk(a) for a in args.committee] if args.committee else None, args.dead_man)
        reg = {}
        if os.path.exists(args.out):
            with open(args.out) as f:
                reg = json.load(f)
        reg[cid] = chain
        _write_json(args.out, reg)
        print(cid)
    elif args.cmd == "standby":
        standby(args)
    else:
        run(args)


if __name__ == "__main__":
    main(sys.argv[1:])
