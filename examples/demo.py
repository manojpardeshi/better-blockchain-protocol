"""A guided tour of Sigil. Run with:  python3 examples/demo.py"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sigil import InvalidDossier, Network, SealFailed, Wallet, locks, model  # noqa: E402
from sigil.proofs import verify_equivocation  # noqa: E402
from sigil.swap import atomic_swap  # noqa: E402
from sigil.wallet import request_seal  # noqa: E402
from tests.adversary import Equivocator  # noqa: E402
from tests.test_security import manual_spend  # noqa: E402


def say(title):
    print(f"\n\033[1m== {title}\033[0m")


net = Network()
orion = net.create_constellation("orion", 4, byzantine={3: Equivocator})
lyra = net.create_constellation("lyra", 7)
print(f"constellation orion {orion[:10]}  4 witnesses (1 byzantine), quorum 3")
print(f"constellation lyra  {lyra[:10]}  7 witnesses, quorum 5")
print("No genesis block, no chain, no validators, no native token. Just two groups of notaries.")

alice, bob, carol = Wallet("alice", net, orion), Wallet("bob", net, lyra), Wallet("carol", net, orion)

say("1. Anyone can create an asset; its id is the hash of its genesis transition")
usd = alice.issue("USD", 1_000_000)
print(f"alice issued USD ({usd[:10]}), balance {alice.balance(usd):,}")

say("2. Payment: one round-trip to the sender's witnesses, then hand the dossier to the payee")
t0 = time.perf_counter()
alice.pay(bob, usd, 250_000)               # bob chose to keep it in lyra
dt = (time.perf_counter() - t0) * 1000
print(f"alice -> bob 250,000 (orion -> lyra) final in {dt:.1f} ms. No block to wait for, no confirmations.")
bob.pay(carol, usd, 40_000)
print(f"bob -> carol 40,000 (lyra -> orion). balances: alice {alice.balance(usd):,}  bob {bob.balance(usd):,}  carol {carol.balance(usd):,}")

say("3. Witnesses are blind")
w = net.witnesses(orion)[0]
sample = next(iter(w.records.values())).log[0]["auth"]["header"]
print(f"what a witness saw: inputs={[(s[:8], g) for s, g in sample['inputs']]} body={sample['body'][:12]}…")
print("no asset, no amount, no recipient, no graph.")

say("4. Blind witnesses will seal nonsense. Holders refuse it.")
refs, _ = carol.select(usd, 40_000)
addr = bob.address()
tid = carol.transact(refs, [model.parcel(lyra, usd, 9_999_999, addr["lock"], addr["salt"])])
try:
    bob.receive(carol.dossier.ancestry([tid]), [model.ref(tid, 0)])
except InvalidDossier as e:
    print(f"bob rejects carol's inflated parcel: {e}")

say("5. Double spending: the owner can only destroy their own parcel, and byzantine witnesses convict themselves")
mallory = Wallet("mallory", net, orion)
alice.pay(mallory, usd, 1_000)
refs, _ = mallory.select(usd, 1_000)
a, c = alice.address(), carol.address()
*_, r1 = manual_spend(mallory, refs, [model.parcel(orion, usd, 1_000, a["lock"], a["salt"])])
*_, r2 = manual_spend(mallory, refs, [model.parcel(orion, usd, 1_000, c["lock"], c["salt"])])
ws = net.witnesses(orion)
v1 = [ws[0].spend(r1[0]), ws[1].spend(r1[0]), ws[3].spend(r1[0])]
v2 = [ws[2].spend(r2[0]), ws[3].spend(r2[0])]
print(f"spend #1 got {len(v1)} votes (sealed), spend #2 got {len(v2)} votes (quorum is 3: impossible)")
proof = {"a": v1[2], "b": v2[1]}
print(f"byzantine witness signed both -> equivocation proof valid: {verify_equivocation(proof)}")
for wl in (alice, bob, carol):
    wl.policy.convict(proof)
print("every holder now ignores that witness's votes; its bond can be claimed by whoever holds the proof.")

say("6. Atomic swap across two constellations that never talk to each other")
gold = bob.issue("GOLD", 100, lyra)
atomic_swap(alice, usd, 5_000, bob, gold, 3)
print(f"alice: {alice.balance(gold)} GOLD, bob: +5,000 USD. Either both legs happen or neither.")

say("7. Time without a chain: locks are checked against witness clocks")
k = carol.fresh_key()
unlock_at = net.clock() + 86_400
addr = carol.address(lock=locks.all_of(locks.sig(k.pk), locks.after(unlock_at)))
refs, outs = alice.payment_outputs(usd, 777, addr)
tid = alice.transact(refs, outs)
carol.receive(alice.dossier.ancestry([tid]), [model.ref(tid, 0)])
held = next(h for h in carol.holdings.values() if h["parcel"]["lock"]["op"] == "all")
out = [model.parcel(orion, usd, 777, carol.address()["lock"], "x")]
try:
    carol.transact([held["ref"]], out)
except SealFailed:
    print("carol's time-locked parcel cannot move yet")
net.clock.advance(86_400)
carol.transact([held["ref"]], out)
print("one day later (by the witnesses' clocks) it moves")

say("8. Membership changes without a chain: lyra rotates its entire witness set")
from sigil import KeyPair  # noqa: E402
net.rotate(lyra, [KeyPair.generate() for _ in range(7)])
bob.pay(alice, usd, 1_000)
print(f"lyra is now at charter v{net.registry.latest(lyra)['version']}; bob's parcels kept working.")

say("summary")
print("ordering: none.  global state: none.  blocks: none.  fees: blind stamps.  finality: one round-trip.")
