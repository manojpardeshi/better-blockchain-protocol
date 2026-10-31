"""Save and load a Wallet's state to a directory.

Layout of a wallet directory::

    keys.json     secret key seeds (pk -> hex seed), mode 0600
    state.json    name, home, deep_threshold, pledge_ttl, max_skew, trust policy,
                  holdings, pledged, pending transitions, issued addresses,
                  stamps, confirmed
    dossier.json  the wallet's dossier (Dossier.to_json)

BACK UP THE WALLET DIRECTORY. In Sigil there is no ledger to restore from:
the dossier *is* the money (the proof that your parcels exist) and the seeds
are what unlock it. Lose either and the funds are gone. Keep the directory
private: anyone with keys.json and dossier.json can spend your parcels.

Every file is written atomically (temp file + fsync + ``os.replace``), keys
before state, so a crash leaves either the old or the new version of each
file. Save after *every* operation that changes state, and in particular
before handing a payment to anyone (a pledge must never be forgotten).
"""

import json
import os
import tempfile
from collections import defaultdict

from .crypto import KeyPair
from .validate import Dossier
from .wallet import Wallet

KEYS, STATE, DOSSIER = "keys.json", "state.json", "dossier.json"


def _atomic_write(path: str, data: str, mode: int = 0o600) -> None:
    d = os.path.dirname(os.path.abspath(path))
    fd, tmp = tempfile.mkstemp(dir=d, prefix=".tmp-")
    try:
        os.fchmod(fd, mode)
        with os.fdopen(fd, "w") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except FileNotFoundError:
            pass
        raise


def exists(wallet_dir: str) -> bool:
    return os.path.exists(os.path.join(wallet_dir, STATE))


def save(wallet: Wallet, wallet_dir: str) -> None:
    os.makedirs(wallet_dir, mode=0o700, exist_ok=True)
    missing = set(wallet.keys) - set(wallet.seeds)
    if missing:
        raise ValueError("wallet holds keys without stored seeds; they cannot be persisted")
    _atomic_write(os.path.join(wallet_dir, KEYS), json.dumps(wallet.seeds, sort_keys=True), 0o600)
    _atomic_write(os.path.join(wallet_dir, DOSSIER), wallet.dossier.to_json(), 0o600)
    state = {
        "version": 1,
        "name": wallet.name,
        "home": wallet.home,
        "deep_threshold": wallet.deep_threshold,
        "pledge_ttl": wallet.pledge_ttl,
        "max_skew": wallet.max_skew,
        # The trust policy is a security decision: losing it on reload would
        # make the wallet accept money from any constellation a payer names.
        "trusted": sorted(wallet.policy.trusted) if wallet.policy.trusted is not None else None,
        "convicted": sorted(wallet.policy.convicted),
        "holdings": wallet.holdings,
        "pledged": {s: list(v) for s, v in wallet.pledged.items()},
        "pending": wallet.pending,
        "completed": wallet.completed,
        "issued": sorted(wallet.issued),
        "stamps": {pk: list(v) for pk, v in wallet.stamps.items() if v},
        "confirmed": sorted(list(c) for c in wallet._confirmed),
    }
    _atomic_write(os.path.join(wallet_dir, STATE), json.dumps(state, sort_keys=True), 0o600)


def load(wallet_dir: str, network) -> Wallet:
    with open(os.path.join(wallet_dir, STATE)) as f:
        state = json.load(f)
    with open(os.path.join(wallet_dir, KEYS)) as f:
        seeds = json.load(f)
    with open(os.path.join(wallet_dir, DOSSIER)) as f:
        dossier = Dossier.from_json(f.read())
    if "trusted" not in state:
        # Wallets saved before the trust policy was persisted: fall back to
        # the default (home plus the configured constellations), never to "any".
        trusted = None
    elif state["trusted"] is None:
        raise ValueError("state.json has no trust policy; refusing to trust every constellation")
    else:
        trusted = set(state["trusted"])
    w = Wallet(state["name"], network, state["home"], deep_threshold=state["deep_threshold"],
               trusted=trusted, pledge_ttl=state.get("pledge_ttl", 600), max_skew=state.get("max_skew", 120))
    w.policy.convicted = set(state.get("convicted", []))
    for pk, seed in seeds.items():
        kp = KeyPair.from_seed(bytes.fromhex(seed))
        if kp.pk != pk:
            raise ValueError("keys.json is corrupt: seed does not match its public key")
        w.keys[pk], w.seeds[pk] = kp, seed
    w.dossier = dossier
    w.holdings = state["holdings"]
    # Pledges are (gen, tid, expires). Older wallets stored (gen, tid): those
    # authorisations carry no expiry, which current witnesses refuse to newly
    # bind, so expires=0 is safe (release still needs every witness's status).
    w.pledged = {s: tuple(v) if len(v) == 3 else (v[0], v[1], 0)
                 for s, v in state["pledged"].items()}
    w.pending = state.get("pending", {})
    w.completed = state.get("completed", [])
    # Older wallets did not record issued addresses: accept the ones we hold.
    w.issued = set(state.get("issued", [h["sigil"] for h in w.holdings.values()]))
    w.stamps = defaultdict(list, {pk: list(v) for pk, v in state["stamps"].items()})
    w._confirmed = {tuple(c) for c in state["confirmed"]}
    return w
