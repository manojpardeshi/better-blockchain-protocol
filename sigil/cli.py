"""Command-line wallet for a real Sigil network.

    python -m sigil.cli --wallet DIR --directory directory.json <command> ...

Commands (all print JSON on stdout):

    init --home CID [--name N] [--deep-threshold X]   create a wallet
    address [--home CID]                 a fresh receiving address (give it to a payer)
    issue NAME SUPPLY [--home CID]       create a new asset; prints its id
    balance [ASSET]                      balances (of one asset, or all)
    assets                               assets held, with names
    pay ADDRESS_FILE ASSET AMOUNT --out PAYMENT_FILE
                                         seal a payment; writes the file the payee needs
    receive PAYMENT_FILE [--deep]        verify a payment file and take custody
    export-dossier                       the whole dossier

Payments are holder-to-holder file hand-offs: no server stores them. A
payment file is ``{"dossier": <ancestry dossier>, "refs": [ref, ...]}``.

Receiving is idempotent: receiving a payment whose parcels are already held
is a no-op (reported as ``"already": true``). A parcel that has since been
spent is rejected, because its sigil is bound at the witnesses.

The wallet directory holds money (see sigil/wallet_store.py): back it up.
"""

import argparse
import json
import sys

from . import model, wallet_store
from .validate import Dossier, InvalidDossier
from .wallet import SealFailed, Wallet


class CliError(Exception):
    pass


def _network(path: str):
    from .server import RemoteNetwork
    with open(path) as f:
        d = json.load(f)
    return RemoteNetwork(d.get("constellations", d))


def _load(args) -> Wallet:
    if not wallet_store.exists(args.wallet):
        raise CliError(f"no wallet at {args.wallet} (run init)")
    return wallet_store.load(args.wallet, _network(args.directory))


def _asset_name(w: Wallet, asset: str) -> str | None:
    base = asset.removeprefix(model.MINT_PREFIX)
    tx = w.dossier.transitions.get(base)
    g = tx and tx["body"].get("genesis")
    return g["name"] if g else None


def _balances(w: Wallet) -> dict:
    return {a: w.balance(a) for a in sorted({h["parcel"]["asset"] for h in w.holdings.values()})}


def cmd_init(args):
    if wallet_store.exists(args.wallet):
        raise CliError(f"wallet already exists at {args.wallet}")
    net = _network(args.directory)
    if args.home not in net.registry:
        raise CliError("home constellation not in the directory (or its charter could not be verified)")
    w = Wallet(args.name, net, args.home, deep_threshold=args.deep_threshold)
    wallet_store.save(w, args.wallet)
    return {"wallet": args.wallet, "name": w.name, "home": w.home}


def cmd_address(args):
    w = _load(args)
    a = w.address(args.home)
    wallet_store.save(w, args.wallet)  # the key must be stored before the address leaves
    return a


def cmd_issue(args):
    w = _load(args)
    asset = w.issue(args.name, args.supply, args.home)
    wallet_store.save(w, args.wallet)
    return {"asset": asset, "name": args.name, "supply": args.supply}


def cmd_balance(args):
    w = _load(args)
    if args.asset:
        return {args.asset: w.balance(args.asset)}
    return _balances(w)


def cmd_assets(args):
    w = _load(args)
    return [{"asset": a, "name": _asset_name(w, a), "balance": b} for a, b in _balances(w).items()]


def cmd_pay(args):
    w = _load(args)
    with open(args.address) as f:
        addr = json.load(f)
    if not isinstance(addr, dict) or not {"home", "lock", "salt"} <= set(addr):
        raise CliError("address file must hold {home, lock, salt}")
    if args.amount <= 0:
        raise CliError("amount must be positive")
    refs, outputs = w.payment_outputs(args.asset, args.amount, addr)
    header, body, _ = w.prepare(refs, outputs)
    unlocks = w.authorise(header, body)
    wallet_store.save(w, args.wallet)  # persist the pledge before any witness sees it
    try:
        w.seal(header, body, unlocks)
    except SealFailed:
        for s, _g in header["inputs"]:
            w.unpledge_if_unbound(s)
        wallet_store.save(w, args.wallet)
        raise
    tid = w.finalise(header, body, unlocks)
    wallet_store.save(w, args.wallet)
    payment = {"dossier": json.loads(w.dossier.ancestry([tid]).to_json()), "refs": [model.ref(tid, 0)]}
    with open(args.out, "w") as f:
        json.dump(payment, f, sort_keys=True)
    return {"tid": tid, "out": args.out, "asset": args.asset, "amount": args.amount,
            "balance": w.balance(args.asset)}


def cmd_receive(args):
    w = _load(args)
    try:
        with open(args.payment) as f:
            obj = json.load(f)
        dossier = Dossier.from_json(json.dumps(obj["dossier"]))
        refs = list(obj["refs"])
        ids = [model.parcel_id(r) for r in refs]
    except (ValueError, KeyError, TypeError) as e:
        raise CliError(f"malformed payment file: {e}") from e
    new = [r for r, i in zip(refs, ids) if i not in w.holdings]
    if not new:
        return {"already": True, "received": []}
    try:
        got = w.receive(dossier, new, deep=True if args.deep else None)
    except (KeyError, TypeError, ValueError) as e:
        raise InvalidDossier(f"malformed payment: {e}") from e
    wallet_store.save(w, args.wallet)
    return {"already": False,
            "received": [{"asset": p["asset"], "amount": p["amount"], "home": p["home"]} for p in got]}


def cmd_export_dossier(args):
    return json.loads(_load(args).dossier.to_json())


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="sigil", description="Sigil command-line wallet")
    p.add_argument("--wallet", required=True, help="wallet directory (BACK IT UP)")
    p.add_argument("--directory", required=True, help="network directory JSON (docs/WIRE.md)")
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("init"); s.set_defaults(fn=cmd_init)
    s.add_argument("--home", required=True); s.add_argument("--name", default="wallet")
    s.add_argument("--deep-threshold", type=int, default=None)
    s = sub.add_parser("address"); s.set_defaults(fn=cmd_address); s.add_argument("--home")
    s = sub.add_parser("issue"); s.set_defaults(fn=cmd_issue)
    s.add_argument("name"); s.add_argument("supply", type=int); s.add_argument("--home")
    s = sub.add_parser("balance"); s.set_defaults(fn=cmd_balance); s.add_argument("asset", nargs="?")
    s = sub.add_parser("assets"); s.set_defaults(fn=cmd_assets)
    s = sub.add_parser("pay"); s.set_defaults(fn=cmd_pay)
    s.add_argument("address"); s.add_argument("asset"); s.add_argument("amount", type=int)
    s.add_argument("--out", required=True)
    s = sub.add_parser("receive"); s.set_defaults(fn=cmd_receive)
    s.add_argument("payment"); s.add_argument("--deep", action="store_true")
    s = sub.add_parser("export-dossier"); s.set_defaults(fn=cmd_export_dossier)
    return p


def main(argv=None, out=None) -> int:
    """Run one command. Returns 0 on success, 1 on error (message on stderr as JSON)."""
    out = out or sys.stdout
    args = parser().parse_args(argv)
    try:
        result = args.fn(args)
    except (CliError, InvalidDossier, SealFailed, ValueError, OSError) as e:
        print(json.dumps({"error": type(e).__name__, "message": str(e)}), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True, indent=2), file=out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
