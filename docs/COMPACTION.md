# Bounding protocol state: settlement, checkpoints and delta dossiers

Status: design note for SPEC §3.12, §5.7 and §6.1 (normative text lives in SPEC.md).
Formal check: `formal/MC_ckpt*.cfg` (docs/VERIFICATION.md §2b).

## 1. The problem, measured

Soak runs (docs/VERIFICATION.md §4c; 30- and 45-minute runs, four constellations,
rotation every 60 s) showed three kinds of growth:

| | what grows | measured |
|---|---|---|
| (a) | a witness keeps every sigil's record, with its whole evidence log, forever; a rotation hands all of it over | handover 3.7 MB → 70 MB, rotation 0.85 s → 3.5–6 s; the Python store costs 4.2 KB and the Rust store 10.5 KB per sealed input |
| (b) | the dossier a payment carries holds the coin's whole ancestry | up to 4 MB / 1,177 transitions per hop, ~3.2 KB per transition; on average only **10 %** of a hop's transitions were new to the payee |
| (c) | Rust witness memory per record | ~3× Python's; a restart peaks at ~1.9× steady state |

What a record holds today (one-input payment, *n* = 4): `header` 157 B, `vote` 484 B,
the `bind` log entry 682 B (it repeats the header inside the owner's authorisation),
`votes` 486 B (the same vote again): ~2 KB. A FREEZE snapshot carries the bind entry
and a vote entry per sigil (~1.2 KB), and every freezing member sends its own copy.
Records of multi-input transitions repeat the whole header in every input's record.

## 2. What cannot be dropped

**A consumed sigil cannot be forgotten.** A witness never sees outputs, so it cannot
tell a sigil it forgot from one it never met. If an honest witness, or every successor
version, forgets that `s` was consumed by a complete `T` at generation `g`, the owner of
`s` (adversarial in the model) signs `T'` at `g' > g`; the witnesses vote it, and `T`
and `T'` are both complete: a double spend that no receiver of `T'` can detect from its
own dossier. `formal/MC_ckpt_forget_mutant.cfg` is exactly this compaction, and TLC
finds the double spend. So the witness state of a home is Θ(consumed sigils of that
home) for any design in this trust model; what can be bounded is the cost **per**
consumed sigil, and what has to be carried, verified and stored at a rotation.

Forgetting would need consumed sigils to expire: parcels that must be re-spent within
*K* versions of their creation, the witness checking the creation version from evidence
in the spend request. That changes what a coin is (money that dies if its holder is
offline), so it is rejected here.

**A seal is not a tombstone.** "Once a seal for `(s, g, t)` is known, the record can
shrink to `(s, g, t, seal)`" is wrong as stated: `t` can have *another* input sealed to
a different transition, which is a death proof for `t` (SPEC §3.9), and then `s` is
legitimately released and spent again at `g + 1`. That is how kill switches recover a
stalled multi-party transition (§9). A record may become final only when `t` is
**complete**: every input of `t` sealed (Lemma 2 contrapositive: a complete transition
never has a death proof, so its inputs are never released). The certificate of that is
one seal per input, with each input's parcel to show the seal comes from that input's
home.

**Per-sigil tombstones save little.** A seal with *q* = 3 votes is ~950 B; the bind entry
it would replace is 680 B and needs one signature check instead of three. Re-encoding a
consumed sigil's evidence as a seal makes the handover no smaller and its verification
three times slower. The constant only falls if one signature covers many sigils.

**Votes for keys not in the next version.** A snapshot's `vote` entries are only read by
an adopter whose own key signed them. Nothing changes if a freezer omits them when its
key is not in the next charter; this is a 40 % cut of an ordinary handover with no
safety question, but it does not bound anything, so it is left as an implementation
option, not part of this design.

## 3. The design

Three mechanisms. The first two bound (a); the third is the safe part of (b).

### 3.1 Settlement (SPEC §3.12, §5.7)

A **settlement certificate** for transition `t` is its header and, for each input
`[s_k, g_k]`, the input's `parcel = {home, lock, salt}` and a valid seal for
`(s_k, g_k, t)` from `parcel.home`. It proves `t` complete. Any holder of the dossier
has one; the reference wallet sends it to every witness of every input's home right
after a transition completes (`SETTLE`).

A witness that verifies a certificate marks the record of every input homed with it
**settled** at `(g_k, t)`: it never votes again on that sigil (it returns a vote it
already holds for exactly `(g_k, t)`), never releases it, and keeps its log for the
next handover. Settling is pure abstention, so it is safe whatever the certificate
says; the certificate is checked so that an honest witness never settles a sigil whose
transition could still die (liveness: the owner's kill-switch recovery).

### 3.2 Checkpoints in the charter (SPEC §3.7, §5.4, §5.5, §5.7)

A charter body MAY carry `checkpoint = H("checkpoint", S)`, where `S` is a set of
`[sigil, gen, tid]` entries, one per sigil, sorted. Version *v*+1's checkpoint `S` is
what the rotation driver offers; a member freezes for that charter only if

* every entry of `S` matches a record it holds settled (liveness: with a quorum of
  signers at least one honest member checked each entry, so `S` lists only sigils whose
  transition really is complete), and
* every record it holds *because of an earlier checkpoint* is in `S` (the **extension
  rule**: `S_v ⊆ S_{v+1}`; this one is for safety).

Its snapshot then omits every sigil in `S`. The adopter receives `S` once (from the
driver), checks its hash against the new charter, which a quorum signed, and records
each entry as **checkpointed**: settled at `(g, t)`, with no log, header or votes other
than its own vote for exactly `(g, t)`. Standby members get the checkpoint set with
their STANDBY handover, require the extension rule before signing a successor, and a
dead-man successor carries exactly the dead version's checkpoint (the committee cannot
check new settlements).

Choosing `S`: the driver asks each live member for its settled records (`/v0/settled`)
and offers the previous checkpoint plus the entries every answering member holds
settled; settled sets only grow, so each of those members will accept. A member that
refuses does not freeze; nothing changes.

### 3.3 Delta dossiers (SPEC §6.1)

A payer MAY omit, from the dossier it hands over, every transition the payee already
holds in its own dossier (and their ancestry), the payee having said which it holds.
The payee verifies against the union of its own dossier and what it received, its own
copies winning, so its policy (trust, convicted keys, deep confirmation, which runs on
the whole ancestry exactly as before) is applied unchanged. No new trust: everything
omitted was verified by the payee itself and is still in its possession, so it can
still prove the coin to the next payee.

## 4. Why it is safe

**Settlement and checkpointed records only remove votes.** A settled record never
creates a vote and never releases. Every behaviour of a witness with settled records is
a behaviour of the same witness without them that declines those requests, which the
rotation and succession specs (and SPEC §5, "Refusing is safe") allow at every step.

**Omitting evidence is replaced by something stronger.** The rotation argument (§8)
needs, for every seal of version *v*, one honest member of the freezing quorum whose
snapshot holds the binding. With a checkpoint, that member's snapshot either holds the
binding (sigil not in `S`) or the sigil is in `S`, and every adopter of *v*+1 records it
checkpointed, which never votes. `S` reaches the adopter intact because its hash is in
the charter a quorum signed, and ADOPT refuses to run without the matching set.

**The extension rule keeps it that way.** A checkpointed record has no log. If a later
charter dropped its sigil from `S`, its holder would hand over nothing and the next
version would see the sigil as fresh: the owner could spend it again
(`formal/MC_ckpt_noextend_mutant.cfg`, a double spend across three versions). Honest
members refuse to freeze (and honest standby members to sign) for such a charter, and a
quorum of signers contains an honest one.

**Refinement.** Map each compacted run to a run of the uncompacted rotation/succession
spec (SigilRotProofs, SigilSuccProofs) in which the same witnesses hold full logs. For a
sigil not in any checkpoint so far the records and logs coincide (by induction over
versions: the extension rule means a sigil never leaves `S`, so a sigil outside `S_{v+1}`
was outside `S_v` and its evidence was handed over in full). For a sigil in a checkpoint
the abstract witness takes no step on it, which the abstract spec allows. Every vote of
the compacted run is therefore a vote of the abstract run, and the theorems (no double
consumption, one seal per `(s, g)` across versions, no honest equivocation) are
properties of the vote set: they carry over. TLC checks the same on a three-version
instance with the real rule and finds the counterexamples of the unsafe ones (§5).

**Byzantine predecessors.** A lying freezer can omit (covered as before) or add
evidence for a checkpointed sigil (ignored: checkpointed wins). It cannot shrink `S`:
the set is fixed by the charter hash. A Byzantine driver can offer any `S`; honest
members refuse a bad one, and a charter needs a quorum.

**Long range.** A checkpoint is only as good as the charter chain it sits in. Registries
accept extensions only, never forks, so retired keys cannot forge a checkpoint into a
chain a witness or holder already holds. A checkpoint entry makes the current members
report `(g, t)` bound, which deep confirmation (§9) reads; the chain that carries it is
the same chain deep confirmation already trusts.

## 5. What it costs and what is left

Measured (600 s soak, docs/BENCHMARKS.md "State growth under load"): rotation time stays at
0.5–0.7 s instead of rising from 0.85 s to 2.5 s by the ninth rotation; the handover at the
ninth rotation is 99.8 KB (708 checkpointed sigils); the new members' stores shrink about 7–9×;
a payment hop carries 193 KB on average (median 10 KB) instead of 1.35 MB (median 1.15 MB),
while a fresh holder still receives the whole history (3.5 MB on average in that run).

* **Per consumed sigil after one checkpointed rotation:** ~135 B in `S` (one copy per
  adopter, not one per freezer), one hash for the whole set instead of 1–3 signature
  checks per entry, a ~150 B record. The total is still linear in consumed sigils (§2),
  with a ~30× smaller constant on the handover.
* **Settling costs** one request per witness of each input home per transition, and the
  witness checks *q* signatures per input. It is optional for holders: an unsettled
  sigil just keeps its full record and is handed over as today.
* **Long-lived constellations that never rotate** do not compact (only a charter can
  carry a checkpoint). Rotating to the same keys compacts them.
* **Lost death-proof material.** A checkpointed sigil keeps no votes at the successor,
  so a counter-party of an owner who equivocated on it cannot build a *votes* death proof
  from STATUS; it needs the seal (or its own kill switch, as §9 already recommends).
* **(b) for fresh payees is not solved.** A payee that holds none of the history still
  gets all of it. A dossier that stops at a **checkpoint of outputs** ("these unspent
  outputs have valid histories", signed by a quorum the payee trusts) would bound it, but
  it is a new trust assumption, not a reorganisation of an existing one: witnesses never
  see outputs or validate histories today, a corrupt quorum of a home can only seal
  double spends of parcels whose owners collude, and a quorum attesting validity could
  mint value alone. It would also show witnesses the outputs they attest. An opt-in
  "notary" mode is possible and is left open, with recursive proofs (§10) as the
  trust-free answer.
