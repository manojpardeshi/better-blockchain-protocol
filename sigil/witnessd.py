"""The witness daemon: one witness, one durable store, served over HTTP.

    python -m sigil.witnessd keygen  --out key.json
    python -m sigil.witnessd genesis --name orion --keys k1.pub k2.pub k3.pub k4.pub --out registry.json
    python -m sigil.witnessd run     --key key.json --registry registry.json --constellation <cid> \\
                                     --store data.db [--host 127.0.0.1] [--port 7000] [--stamps]

``keygen`` writes the private key (mode 0600) and its public key next to it
(``key.pub``). ``genesis`` builds charter version 0 from public keys and
writes a charter registry (docs/WIRE.md). ``run`` verifies the registry,
restores the witness from its store (or joins the constellation on first
start) and serves it until SIGTERM or SIGINT.

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

from .charter import Registry, charter_body, constellation_id
from .crypto import KeyPair
from .server import WitnessServer
from .stamps import StampMint
from .store import WitnessStore
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


def genesis(name: str, pks: list) -> tuple[str, dict]:
    """Charter version 0 of a new constellation: returns ``(cid, registry entry)``."""
    body = charter_body(name, 0, pks, None)
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

def build_witness(key: str, registry: str, cid: str, store: str, stamps: bool = False) -> Witness:
    kp = load_key(key)
    reg = load_registry(registry)
    if cid not in reg:
        raise SystemExit(f"constellation {cid} is not in {registry}")
    mint = load_mint(store + ".stamps.json") if stamps else None
    w = Witness(kp, reg, lambda: int(time.time()), stamp_mint=mint, store=WitnessStore(store))
    if w.cid is None:
        # First start: join the newest charter version that lists us.
        chain = reg.chain(cid)
        version = max((c["body"]["version"] for c in chain if kp.pk in c["body"]["witnesses"]), default=None)
        if version is None:
            raise SystemExit(f"{kp.pk[:12]} is not a member of {cid[:12]}")
        w.join(cid, version)
    elif w.cid != cid:
        raise SystemExit(f"store {store} belongs to constellation {w.cid}, not {cid}")
    return w


def run(args) -> None:
    w = build_witness(args.key, args.registry, args.constellation, args.store, args.stamps)
    server = WitnessServer(w, args.host, args.port).start()
    stop = threading.Event()
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, lambda *_: stop.set())
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

    r = sub.add_parser("run", help="serve a witness")
    r.add_argument("--key", required=True)
    r.add_argument("--registry", required=True)
    r.add_argument("--constellation", required=True)
    r.add_argument("--store", required=True)
    r.add_argument("--host", default="127.0.0.1")
    r.add_argument("--port", type=int, default=7000)
    r.add_argument("--stamps", action="store_true", help="require a stamp with every spend")

    args = p.parse_args(argv)
    if args.cmd == "keygen":
        print(generate_key(args.out).pk)
    elif args.cmd == "genesis":
        cid, chain = genesis(args.name, [read_pk(a) for a in args.keys])
        reg = {}
        if os.path.exists(args.out):
            with open(args.out) as f:
                reg = json.load(f)
        reg[cid] = chain
        _write_json(args.out, reg)
        print(cid)
    else:
        run(args)


if __name__ == "__main__":
    main(sys.argv[1:])
