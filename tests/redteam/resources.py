"""Resource-exhaustion probes: measure amplification ratios an adversary gets
for CPU, memory and storage per request.

Each probe returns a dict of measurements. The unittest wrapper asserts only
loose sanity bounds (so timing jitter never breaks the build); the runner
prints the full numbers for a human to read.
"""

import json
import time
from unittest import mock

from sigil import KeyPair, Network, locks, model
from sigil import crypto
from sigil.gossip import GossipStore
from sigil.witness import Rejected


def spend_cpu_amplification():
    """Ed25519 verifications forced by one SPEND, per byte of request.

    A sig/multi lock tree with many leaves and many keys makes a single
    (ultimately rejected) SPEND perform O(#nodes x #keys) signature checks.
    Without stamps (the default, and the Rust witness refuses stamps) there is
    no rate limit on this.
    """
    net = Network()
    c = net.create_constellation("c", 4)
    w = net.witnesses(c)[0]
    out = []
    for nodes, npk in ((1, 1), (63, 60), (1, 3000), (20, 200)):
        kps = [KeyPair.generate() for _ in range(npk)]
        leaf = locks.multi(1, [k.pk for k in kps]) if npk > 1 else locks.sig(kps[0].pk)
        lk = leaf if nodes == 1 else locks.any_of(*[leaf for _ in range(nodes)])
        salt = "00" * 16
        p = model.parcel(c, "x", 1, lk, salt)
        s = model.sigil_of(p)
        hd = {"inputs": [[s, 0]], "body": "11" * 32}
        un = locks.empty_unlock(4_000_000_000)
        # Signatures over the wrong message: each is checked, each fails.
        un["sigs"] = {k.pk: k.sign("unlock", {"x": 1}) for k in kps}
        req = {"sigil": s, "header": hd, "home": c, "lock": lk, "salt": salt, "unlock": un}
        count = [0]
        base = crypto.verify

        def counting(*a, **k):
            count[0] += 1
            return base(*a, **k)

        with mock.patch("sigil.locks.verify", counting):
            t = time.perf_counter()
            try:
                w.spend(req)
            except Rejected:
                pass
            dt = time.perf_counter() - t
        nbytes = len(json.dumps({"request": req}))
        out.append({"nodes": nodes, "keys": npk, "bytes": nbytes, "verifies": count[0],
                    "ms": round(dt * 1000, 1),
                    "verifies_per_KiB": round(count[0] / (nbytes / 1024), 1),
                    "ms_per_MiB": round(dt / nbytes * (1 << 20), 1)})
    return out


def gossip_store_growth():
    """Registry growth a single unauthenticated gossip message can force.

    Genesis charters need no signatures, so one ~1 MiB message can register a
    constellation with a very large witness list. The per-store constellation
    cap (10 000) bounds the count, not the size of any one.
    """
    from sigil.charter import charter_body, constellation_id
    store = GossipStore()
    big = ["%064x" % i for i in range(14000)]
    body = charter_body("x", 0, big, None)
    msg = {"charters": {constellation_id(body): [{"body": body, "sigs": {}}]}}
    nbytes = len(json.dumps(msg))
    before = len(store.registry.ids())
    accepted = store.merge(msg)
    return {"msg_bytes": nbytes, "witnesses_in_one_charter": len(big),
            "accepted": accepted, "registry_grew_by": len(store.registry.ids()) - before}


def storage_per_spend():
    """Bytes of durable witness state one accepted SPEND can pin.

    The witness logs the full authorisation (salt, header, unlock) per bind.
    Without stamps there is no cost to the requester, and logs never compact.
    """
    net = Network()
    c = net.create_constellation("c", 4)
    w = net.witnesses(c)[0]
    owner = KeyPair.generate()
    salt = "cd" * 16
    big_memo_salt = "ee" * 400_000  # ~800 KiB salt, within the 1 MiB body cap
    p = model.parcel(c, "x", 1, locks.sig(owner.pk), big_memo_salt)
    s = model.sigil_of(p)
    hd = {"inputs": [[s, 0]], "body": "11" * 32}
    un = locks.empty_unlock(4_000_000_000)
    un["sigs"] = {owner.pk: locks.sign_unlock(owner, s, model.transition_id(hd), 4_000_000_000)}
    req = {"sigil": s, "header": hd, "home": c, "lock": p["lock"], "salt": big_memo_salt, "unlock": un}
    req_bytes = len(json.dumps(req))
    w.spend(req)
    stored = len(json.dumps(w.records[s].log))
    return {"request_bytes": req_bytes, "stored_bytes": stored,
            "ratio": round(stored / req_bytes, 2)}
