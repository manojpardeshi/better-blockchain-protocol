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
from sigil.encoding import canonical
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

    Genesis charters need no signatures, so before the charter caps one ~1 MiB
    message registered a constellation of 14,000 witnesses (or a ~900 KiB name,
    or 1 MiB of ignored signatures). Now a charter names at most
    ``MAX_WITNESSES`` and encodes to at most ``MAX_CHARTER_BYTES`` (SPEC §3.7),
    so such messages are dropped and the largest charter one message can
    register is bounded.
    """
    from sigil import charter as C
    from sigil.charter import constellation_id

    def offer(witnesses, name="x", sigs=None):
        store = GossipStore()
        body = {"name": name, "version": 0, "witnesses": witnesses, "prev": None}
        cid = constellation_id(body)
        msg = {"charters": {cid: [{"body": body, "sigs": sigs or {}}]}}
        accepted = store.merge(msg)["charters"]
        return len(json.dumps(msg)), accepted, len(json.dumps(store.registry.chain(cid)))

    big = ["%064x" % i for i in range(14000)]
    nbytes, accepted, _ = offer(big)
    cap = getattr(C, "MAX_WITNESSES", None)
    largest = offer(big[:cap])[2] if cap else None
    junk = offer(big[:4], sigs={"%064x" % i: "00" * 64 for i in range(4000)})
    long_name = offer(big[:4], name="n" * 900_000)
    return {"msg_bytes": nbytes, "witnesses_in_one_charter": len(big), "accepted": accepted,
            "max_witnesses": cap, "largest_accepted_charter_bytes": largest,
            "junk_sigs_msg_bytes": junk[0], "junk_sigs_accepted": junk[1],
            "long_name_msg_bytes": long_name[0], "long_name_accepted": long_name[1]}


def _owner_spend(c, owner, salt, inputs_extra=(), gen=0, expires=4_000_000_000, memo="11" * 32):
    p = model.parcel(c, "x", 1, locks.sig(owner.pk), salt)
    s = model.sigil_of(p)
    hd = {"inputs": [[s, gen], *inputs_extra], "body": memo}
    un = locks.empty_unlock(expires)
    un["sigs"] = {owner.pk: locks.sign_unlock(owner, s, model.transition_id(hd), expires)}
    return {"sigil": s, "header": hd, "home": c, "lock": p["lock"], "salt": salt, "unlock": un}, p


def _stored(w, s) -> int:
    """Bytes of the record the witness keeps (and rewrites) for sigil ``s``."""
    from dataclasses import asdict
    r = w.records.get(s)
    return len(canonical(asdict(r))) if r is not None else 0


def storage_per_spend():
    """Bytes of durable witness state one SPEND can pin.

    The witness logs the full authorisation (salt, header, unlock) of every
    binding. Before ``MAX_AUTH_BYTES`` an ~800 KiB salt (within the 1 MiB body
    cap) was stored whole. Now such a SPEND is a clean Rejected that changes
    nothing, and the largest SPEND a witness accepts pins a bounded record.
    """
    from sigil import witness as W
    net = Network()
    c = net.create_constellation("c", 4)
    w = net.witnesses(c)[0]
    owner = KeyPair.generate()
    big, _ = _owner_spend(c, owner, "ee" * 400_000)  # ~800 KiB salt, within the 1 MiB body cap
    req_bytes = len(json.dumps(big))
    rejected = False
    try:
        w.spend(big)
    except Rejected:
        rejected = True
    stored_big = _stored(w, big["sigil"])
    cap = getattr(W, "MAX_AUTH_BYTES", None)
    largest = None
    if cap is not None:
        lo, hi = 0, cap  # the longest salt whose SPEND is accepted
        while lo < hi:
            mid = (lo + hi + 1) // 2
            r, _ = _owner_spend(c, owner, "e" * mid)
            ok = len(canonical({k: r[k] for k in ("home", "lock", "salt", "unlock", "header")})) <= cap
            lo, hi = (mid, hi) if ok else (lo, mid - 1)
        r, _ = _owner_spend(c, owner, "e" * lo)
        w.spend(r)
        largest = {"request_bytes": len(json.dumps(r)), "stored_bytes": _stored(w, r["sigil"])}
    return {"request_bytes": req_bytes, "rejected": rejected, "stored_bytes": stored_big,
            "ratio": round(stored_big / req_bytes, 2), "largest_accepted": largest}


def sigil_log_growth(cycles: int = 40):
    """How far one owner can grow one sigil's record by bind/release cycles.

    The owner seals a kill switch ``k`` once; every header ``{[s, g], [k, 0]}``
    is then dead by that one seal, so it can bind ``s`` at g = 0, 1, 2, ... and
    release each binding with the same proof, padded with ~800 KiB of junk.
    Before the caps every cycle added an authorisation and the padded proof to
    the record (which is rewritten whole on every update); now RELEASE refuses
    proofs over ``MAX_PROOF_BYTES`` and a sigil is newly bound only below
    generation ``MAX_GEN``.
    """
    from sigil import witness as W
    net = Network()
    c = net.create_constellation("c", 4)
    ws = net.witnesses(c)
    owner = KeyPair.generate()
    kreq, kpar = _owner_spend(c, owner, "ab" * 16, memo="22" * 32)
    seal = model.seal_from_votes([x.spend(kreq) for x in ws])
    k = kreq["sigil"]
    w = ws[0]
    proof = {"kind": "seal", "sigil": k, "gen": 0, "seal": seal,
             "parcel": {"home": c, "lock": kpar["lock"], "salt": kpar["salt"]}}
    padded_proof = dict(proof, junk="00" * 400_000)
    binds = padded = 0
    s = None
    for g in range(cycles):
        req, _ = _owner_spend(c, owner, "cd" * 16, inputs_extra=[[k, 0]], gen=g, memo="%064x" % g)
        s = req["sigil"]
        try:
            w.spend(req)
        except Rejected:
            break
        binds += 1
        try:
            w.release(s, padded_proof)
            padded += 1
        except Rejected:
            w.release(s, proof)
    return {"cycles_tried": cycles, "binds": binds, "padded_proofs_stored": padded,
            "padded_proof_bytes": len(json.dumps(padded_proof)),
            "record_bytes": _stored(w, s), "max_gen": getattr(W, "MAX_GEN", None)}


def rotation_log_growth(rotations: int = 6):
    """Evidence log length of one bound sigil after repeated rotations (n = 4).

    ADOPT takes the union of the freezing quorum's snapshots. Before it dropped
    repeats, every honest predecessor handed over the same entries, so each
    rotation multiplied a sigil's log by the number of signers.
    """
    net = Network()
    c = net.create_constellation("c", 4)
    owner = KeyPair.generate()
    req, _ = _owner_spend(c, owner, "ab" * 16)
    for x in net.witnesses(c):
        x.spend(req)
    lengths = []
    for _ in range(rotations):
        net.rotate(c, [KeyPair.generate() for _ in range(4)])
        lengths.append(len(net.witnesses(c)[0].records[req["sigil"]].log))
    return {"rotations": rotations, "log_lengths": lengths}


def rate_limit_burst(requests: int = 600):
    """Back-to-back requests one client gets through a witness with the open-network default.

    Before admission control a witness on a public address served every request.
    Now a non-loopback listener limits each client to ``DEFAULT_RATE`` per second
    with bursts of ``DEFAULT_BURST``; the rest are answered 429 ``rejected``
    before the witness sees them. (Served on loopback here with the public
    default passed explicitly.)
    """
    import urllib.error
    import urllib.request

    import sigil.server as S
    net = Network()
    c = net.create_constellation("c", 4)
    w = net.witnesses(c)[0]
    try:
        srv = S.WitnessServer(w, port=0, rate_limit=S.DEFAULT_RATE)
    except (TypeError, AttributeError):
        srv = S.WitnessServer(w, port=0)
    srv.start()
    ok = refused = 0
    t = time.perf_counter()
    try:
        for _ in range(requests):
            body = json.dumps({"sigil": "00" * 32}).encode()
            r = urllib.request.Request(srv.url + "/v0/status", data=body, method="POST")
            try:
                with urllib.request.urlopen(r, timeout=5) as resp:
                    resp.read()
                ok += 1
            except urllib.error.HTTPError as e:
                refused += e.code == 429
    finally:
        srv.stop()
    return {"requests": requests, "seconds": round(time.perf_counter() - t, 2), "served": ok,
            "refused_429": refused}


def idle_connections(n: int = 300, hold: float = 2.0):
    """Silent connections a witness keeps open (each pins a handler thread in the reference).

    Before, every accepted connection got a thread that waited for its request
    forever. Now at most ``MAX_CONNECTIONS`` are open at once (the rest are
    closed unread) and each is dropped after ``IDLE_TIMEOUT`` seconds of
    silence (patched to ``hold`` seconds here).
    """
    import contextlib
    import socket
    import threading

    import sigil.server as S
    net = Network()
    c = net.create_constellation("c", 4)
    w = net.witnesses(c)[0]
    patch = mock.patch.object(S, "IDLE_TIMEOUT", hold) if hasattr(S, "IDLE_TIMEOUT") else contextlib.nullcontext()
    with patch:
        srv = S.WitnessServer(w, port=0).start()
    host, port = srv.httpd.server_address[:2]
    socks = []
    before = threading.active_count()

    def open_count() -> int:
        """Connections the server still holds: not readable (no EOF, no reset) within 0.2 s."""
        import select
        done = set()
        ready, _, _ = select.select(socks, [], [], 0.2)
        for s in ready:
            try:
                if not s.recv(1):
                    done.add(s)
            except OSError:
                done.add(s)
        return len(socks) - len(done)

    try:
        for _ in range(n):
            socks.append(socket.create_connection((host, port), timeout=5))
        time.sleep(0.3)
        peak_threads = threading.active_count() - before
        open_now = open_count()
        time.sleep(hold + 0.5)
        open_later = open_count()
        return {"connections": n, "peak_handler_threads": peak_threads, "open_at_once": open_now,
                "open_after_idle": open_later, "max_connections": getattr(S, "MAX_CONNECTIONS", None)}
    finally:
        for s in socks:
            s.close()
        srv.stop()
