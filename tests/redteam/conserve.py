"""Payment-level fuzzer over the real ``sigil.Wallet``: S3, S4, S5.

Random honest wallets make random valid payments (with the wallet's own coin
selection and change) and occasional atomic swaps on an in-process network
with a Byzantine minority and injected crashes. After each operation the
fuzzer checks:

    S3  no honest wallet ever holds two live pledges for one (sigil, gen)
        with different tids (an honest wallet never equivocates)
    S4  value is conserved: for every asset, the sum of balances over all
        honest wallets equals the supply issued, never more
    S5  every parcel an honest wallet holds is addressed to a key it owns

``cache_attack`` is a separate, deliberately malicious flow that a *payer*
can run with no special privileges; it is used by the BUG-1 regression and is
not part of the honest fuzz run.
"""

import random

from sigil import Network, Wallet, locks, model
from sigil.swap import atomic_swap
from sigil.wallet import SealFailed


class ConserveViolation(Exception):
    pass


def _issued(wallets):
    """Supply issued per asset, from genesis transitions seen by any wallet."""
    out = {}
    for w in wallets:
        for tx in w.dossier.transitions.values():
            g = tx["body"].get("genesis")
            if g is not None:
                out[model.transition_id(tx["header"])] = g["supply"]
    return out


def _check(wallets, assets):
    for w in wallets:
        # S5: every holding is addressed to a key we own.
        for h in w.holdings.values():
            if not locks.keys_in(h["parcel"]["lock"]) & set(w.keys):
                raise ConserveViolation(f"S5: {w.name} holds a parcel it cannot unlock")
        # S3: no two distinct live pledges at one (sigil, gen).
        by_sg = {}
        for s, (gen, tid, _exp) in w.pledged.items():
            key = (s, gen)
            if key in by_sg and by_sg[key] != tid:
                raise ConserveViolation(f"S3: {w.name} equivocated at {key}")
            by_sg[key] = tid
    # S4: conservation per asset across all honest wallets.
    issued = _issued(wallets)
    for a, supply in issued.items():
        held = sum(w.balance(a) for w in wallets)
        if held > supply:
            raise ConserveViolation(f"S4: {held} of {a[:12]} held but only {supply} issued")


def fuzz(seed, steps, *, n_wallets=5, n=4):
    rng = random.Random(seed)
    net = Network()
    cids = [net.create_constellation(f"c{i}", n) for i in range(2)]
    wallets = [Wallet(f"w{i}", net, rng.choice(cids)) for i in range(n_wallets)]
    assets = []
    for w in wallets[:2]:
        a = w.issue(f"A{w.name}", 1_000_000)
        assets.append(a)
    stats = {"payments": 0, "swaps": 0, "fails": 0}
    for _ in range(steps):
        kind = rng.random()
        payer = rng.choice(wallets)
        payee = rng.choice([w for w in wallets if w is not payer])
        asset = rng.choice(assets)
        bal = payer.balance(asset)
        if bal <= 0:
            continue
        amount = rng.randint(1, bal)
        try:
            if kind < 0.85:
                payer.pay(payee, asset, amount, home=rng.choice(cids))
                stats["payments"] += 1
            else:
                other = rng.choice([a for a in assets if a != asset] or assets)
                ob = payee.balance(other)
                if ob <= 0:
                    continue
                atomic_swap(payer, asset, amount, payee, other, rng.randint(1, ob))
                stats["swaps"] += 1
        except (ValueError, SealFailed):
            stats["fails"] += 1
        _check(wallets, assets)
    return None, stats


def run(seeds, steps, **kw):
    agg = {"payments": 0, "swaps": 0, "fails": 0, "seeds": 0}
    for seed in range(seeds):
        try:
            _, stats = fuzz(seed, steps, **kw)
        except ConserveViolation as e:
            return {"seed": seed, "detail": str(e)}, agg
        for k, v in stats.items():
            agg[k] += v
        agg["seeds"] += 1
    return None, agg


# --------------------------------------------------------------- BUG-1 flow

def cache_attack():
    """A malicious payer inflates a warm recipient's balance (BUG-1).

    Returns (issued_supply, credited_amount). A sound validator would credit
    at most ``issued_supply``. Uses only the public pay/receive API and a
    dossier the payer fully controls; the genesis tid it abuses is public.
    """
    import copy
    net = Network()
    c = net.create_constellation("c", 4)
    issuer, mallory, bob = Wallet("i", net, c), Wallet("m", net, c), Wallet("b", net, c)
    usd = issuer.issue("USD", 1000)
    issuer.pay(mallory, usd, 100)
    issuer.pay(bob, usd, 10)                 # bob verifies & caches the public genesis tid
    k = mallory.fresh_key()
    fake = model.parcel(c, usd, 10 ** 9, locks.sig(k.pk), "ab" * 16)
    g = copy.deepcopy(issuer.dossier.transitions[usd])
    g["body"]["outputs"].append(dict(fake, asset=""))   # an output from thin air
    mallory.dossier.transitions[usd] = g
    mallory.dossier.add_charters(net.registry, [c])
    r = model.ref(usd, len(g["body"]["outputs"]) - 1)
    mallory.holdings[model.parcel_id(r)] = {"ref": r, "parcel": fake,
                                            "sigil": model.sigil_of(fake), "gen": 0}
    mallory.pay(bob, usd, 10 ** 9 - 1)
    return 1000, bob.balance(usd)
