---- MODULE SigilRotProofs ----
(***************************************************************************)
(* An UNBOUNDED, machine-checked (TLAPS) proof of the Sigil safety theorem *)
(* (docs/SPEC.md Section 8) UNDER CHARTER ROTATION (SPEC Sections 5.1,     *)
(* 5.2, 5.4): any number of charter versions of the home, witnesses per    *)
(* version (keys may be re-used across versions), sigils, transitions and  *)
(* generations.                                                             *)
(*                                                                         *)
(* What is modelled, per honest key w (one witness process per key; a new *)
(* process for a re-used key starts only once the old one has stopped and  *)
(* brings all the votes it cast, as Network.rotate / RemoteNetwork.rotate  *)
(* do):                                                                     *)
(*   * it runs in one version kv[w] at a time and only moves forward; it   *)
(*     may stay unfrozen in an old version forever (an ex-member that      *)
(*     keeps voting there), FREEZE in it (snapshot of its log), and ADOPT  *)
(*     any later version it is a member of, frozen or not;                 *)
(*   * per sigil the Record of sigil/witness.py: gen, tid (a tid, NoTid or *)
(*     Contested), candidates, abstain, and the log (bind and release      *)
(*     entries);                                                            *)
(*   * SPEND (5.1 step 4), RELEASE (5.2 step 3-4), the contested RELEASE   *)
(*     (5.2 step 2), the contested RELEASE that a SEAL for the one         *)
(*     remaining candidate settles (W9, witness.py _sealed_candidate),     *)
(*     FREEZE and ADOPT (5.4), including own-vote abstention.              *)
(* ADOPT reads the union of the snapshots of the HONEST members of a       *)
(* freezing quorum F of the previous version (F's honest members froze),   *)
(* plus whatever its Byzantine members may add: bind entries for any       *)
(* transition (the owner is adversarial and signs anything), release       *)
(* entries only with a valid death proof, seal entries only with a valid   *)
(* seal.  The adopter's own earlier votes are all its votes (a re-used key *)
(* brings its votes, SPEC 5.4).  Quorum intersection between every seal    *)
(* (or against-quorum) of a version and every freezing quorum of it is     *)
(* PROVED (HonestInBothQuorums), not assumed.                              *)
(*                                                                         *)
(* THE ADOPT RULE PROVED HERE is the one sigil/witness.py and the Rust     *)
(* witness implement (Witness.adopt, _sealed_candidate):                   *)
(*   LoneOK: a lone live binding <<g, t>> is inherited only if every other *)
(*     kept binding, dead or alive, is at a LOWER generation (or at most   *)
(*     at g when the evidence holds a valid seal for <<g, t>>: W9) and     *)
(*     every vote the adopter's own key cast on the sigil is at most at g; *)
(*     otherwise the record is contested with the live bindings as         *)
(*     candidates (or unbound past the evidence and the own votes);        *)
(*   ResolveContested: a seal (any version) for the one candidate left     *)
(*     settles a contested record only if every other candidate is killed  *)
(*     and at most at its generation g, the record's gen is at most g + 1  *)
(*     ("top <= g + 1") and the key's own votes are at most at g           *)
(*     (ResolveOK).                                                        *)
(* The first sibling rule (inherit when nothing else is bound AT g) is     *)
(* unsafe (docs/VERIFICATION.md Bugs 3 and 4; MC_rotp_sibling_mutant.cfg). *)
(*                                                                         *)
(* Cryptography is idealised as in SigilProofs.tla: only w creates votes   *)
(* carrying wit |-> w; seals and death proofs are checked against the      *)
(* public vote set.  One home constellation (its charter chain is the      *)
(* constant Members); FREEZE binding one successor makes that chain the    *)
(* only one a holder can verify (theorem OneSuccessor).  Every version,    *)
(* retired ones included, has at most f Byzantine members, and a key is    *)
(* honest or Byzantine for the whole run (static corruption).              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS
    Honest,     \* honest keys
    Byz,        \* Byzantine keys (may sign any vote for themselves)
    Vers,       \* the charter versions of the home (Nat: an unbounded chain)
    Members,    \* Vers -> SUBSET Witnesses : the members of each version
    Quorum,     \* Vers -> Nat : q of each version
    Sigils,
    Tids,
    Header      \* Tids -> header (a set of <<sigil, gen>> pairs)

Witnesses == Honest \cup Byz

Vote(v, w, s, g, t) == [ver |-> v, wit |-> w, sgl |-> s, gnr |-> g, trn |-> t]

NoTid     == CHOOSE x : x \notin Tids
Contested == CHOOSE x : x \notin Tids \cup {NoTid}

ASSUME HonestByzDisjoint == Honest \cap Byz = {}
ASSUME VersType          == Vers \subseteq Nat /\ 0 \in Vers
ASSUME MembersType       == Members \in [Vers -> SUBSET Witnesses]
ASSUME MembersFinite     == \A v \in Vers : IsFiniteSet(Members[v])
ASSUME MembersNonempty   == \A v \in Vers : Members[v] # {}
ASSUME QuorumType        == Quorum \in [Vers -> Nat]
ASSUME TidsNoTid         == NoTid \notin Tids
ASSUME ContestedFresh    == Contested \notin Tids /\ Contested # NoTid

(* SPEC Section 8: every version of the home is fault-bounded.             *)
Faults(n) == (n - 1) \div 3
FaultBounded(v) ==
    LET n == Cardinality(Members[v])
    IN  /\ Quorum[v] = n - Faults(n)
        /\ Cardinality(Members[v] \cap Byz) <= Faults(n)
ASSUME VersionsFaultBounded == \A v \in Vers : FaultBounded(v)

ValidHeader(h) ==
    /\ h # {}
    /\ \A p \in h : p \in Sigils \X Nat
    /\ \A p, qq \in h : p[1] = qq[1] => p = qq
ASSUME HeaderType == Header \in [Tids -> {h \in SUBSET (Sigils \X Nat) : ValidHeader(h)}]

SigilsOf(t) == { p[1] : p \in Header[t] }
GenOf(t, s) == CHOOSE g \in Nat : <<s, g>> \in Header[t]

-----------------------------------------------------------------------------
VARIABLES
    votes,  \* every vote ever cast, honest and Byzantine (public, monotone)
    act,    \* act[w]: honest key w runs in some version
    kv,     \* kv[w]:  the version w runs in
    adv,    \* adv[w]: (ghost) every version w has run in
    frz,    \* frz[w]: w froze in version kv[w]
    gen,    \* gen[w][s]  : Record.gen
    bnd,    \* bnd[w][s]  : Record.tid -- a tid, NoTid or Contested
    cand,   \* cand[w][s] : Record.candidates, <<g, t>> pairs
    abst,   \* abst[w][s] : Record.abstain
    lg,     \* lg[w][s]   : the bind entries <<g, t>> of w's log
    ld,     \* ld[w][s]   : the tids of the release entries of w's log
    fr,     \* fr[v]      : the honest keys that froze in version v
    sb,     \* sb[v][w][s]: the bind entries of the snapshot w handed over when it froze in v
    sd,     \* sd[v][w][s]: the release entries of that snapshot
    hev     \* hev[v][w][s]: (ghost) the bind evidence w adopted for version v

vars == <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev>>

(* Seals and death proofs, over a vote set V (they only grow with V).      *)
VotersV(V, v, s, g, t)  == { w \in Members[v] : Vote(v, w, s, g, t) \in V }
AgainstV(V, v, s, g, t) == { w \in Members[v] :
                                \E u \in Tids : u # t /\ Vote(v, w, s, g, u) \in V }
SealedInV(V, v, s, g, t) == Cardinality(VotersV(V, v, s, g, t)) >= Quorum[v]
(* Holders accept a seal from any version of the home (SPEC 6.4).          *)
SealedV(V, s, g, t) == \E v \in Vers : SealedInV(V, v, s, g, t)
(* SPEC 3.9: a seal for another tid, or q votes of ONE version for other   *)
(* tids, at an input of t.                                                  *)
DeathProofV(V, t) ==
    \E p \in Header[t] :
        \/ \E u \in Tids : u # t /\ SealedV(V, p[1], p[2], u)
        \/ \E v \in Vers : Cardinality(AgainstV(V, v, p[1], p[2], t)) >= Quorum[v]
CompleteV(V, t) == \A p \in Header[t] : SealedV(V, p[1], p[2], t)

Voters(v, s, g, t)   == VotersV(votes, v, s, g, t)
Against(v, s, g, t)  == AgainstV(votes, v, s, g, t)
SealedIn(v, s, g, t) == SealedInV(votes, v, s, g, t)
Sealed(s, g, t)      == SealedV(votes, s, g, t)
DeathProof(t)        == DeathProofV(votes, t)
Complete(t)          == CompleteV(votes, t)

HV(v, w, s, g, t) == Vote(v, w, s, g, t) \in votes

(* The adopter's own earlier votes on s, as <<g, t>> pairs.                *)
Own(w, s) == { <<x.gnr, x.trn>> : x \in { y \in votes : y.wit = w /\ y.sgl = s } }

(* A NORMAL honest vote for t at (s, g) in v: every bind w adopted as      *)
(* evidence for v is this one, or at a lower generation and dead.  A       *)
(* NORMAL quorum: a quorum of v voting t at (s, g) whose honest members    *)
(* all voted normally.  (Votes that are not normal are those the W9 rules *)
(* allow, re-voting a tid already sealed at its generation.)               *)
NormalVoteV(V, Hv, v, w, s, g, t) ==
    \A b \in Hv[v][w][s] : (b[1] = g /\ b[2] = t) \/ (b[1] < g /\ DeathProofV(V, b[2]))
NormalQuorumV(V, Hv, v, Q, s, g, t) ==
    /\ Q \subseteq Members[v]
    /\ Cardinality(Q) >= Quorum[v]
    /\ \A x \in Q : /\ Vote(v, x, s, g, t) \in V
                    /\ x \in Honest => NormalVoteV(V, Hv, v, x, s, g, t)
NSealedV(V, Hv, s, g, t) ==
    \E v \in Vers : \E Q \in SUBSET Members[v] : NormalQuorumV(V, Hv, v, Q, s, g, t)

NormalVote(v, w, s, g, t)      == NormalVoteV(votes, hev, v, w, s, g, t)
NormalQuorum(v, Q, s, g, t)    == NormalQuorumV(votes, hev, v, Q, s, g, t)
NSealed(s, g, t)               == NSealedV(votes, hev, s, g, t)

-----------------------------------------------------------------------------
(* ADOPT's decision for one sigil, from the bind evidence EB, the dead tids *)
(* ED, the binds with a valid seal in the evidence ES, and the adopter's    *)
(* own votes O; ng is the generation used when contested or unbound.       *)
Alive(EB, ED) == { b \in EB : b[2] \notin ED }

(* THE lone rule (witness.py Witness.adopt, `lone = top and all(og <= g    *)
(* for og, _ in own)`): every other kept binding is below b's generation,  *)
(* or at it when the evidence holds a valid seal for b; and the adopter's  *)
(* own votes are at most at b's generation.                                *)
LoneOK(EB, ES, O, b) ==
    /\ \A b2 \in EB : b2 # b => (b2[1] < b[1] \/ (b \in ES /\ b2[1] = b[1]))
    /\ \A o \in O : o[1] <= b[1]

IsLone(EB, ED, ES, O, b) == Alive(EB, ED) = {b} /\ LoneOK(EB, ES, O, b)
HasLone(EB, ED, ES, O)   == \E b \in EB : IsLone(EB, ED, ES, O, b)
TheLone(EB, ED, ES, O)   == CHOOSE b \in EB : IsLone(EB, ED, ES, O, b)

(* witness.py: gen = max over kept binds of (g+1 if dead else g), for an   *)
(* unbound record raised past the own votes.  The spec allows any gen at   *)
(* least that (a jump of an unbound record is abstention).                  *)
GenOK(EB, ED, O, ng) ==
    /\ \A b \in EB : b[1] <= ng /\ (b[2] \in ED => b[1] < ng)
    /\ Alive(EB, ED) = {} => \A o \in O : o[1] < ng

NewRec(EB, ED, ES, O, ng) ==
    IF HasLone(EB, ED, ES, O)
    THEN [g |-> TheLone(EB, ED, ES, O)[1], t |-> TheLone(EB, ED, ES, O)[2], c |-> {},
          a |-> \E o \in O : o[1] = TheLone(EB, ED, ES, O)[1] /\ o[2] # TheLone(EB, ED, ES, O)[2]]
    ELSE IF Alive(EB, ED) # {}
         THEN [g |-> ng, t |-> Contested, c |-> Alive(EB, ED), a |-> FALSE]
         ELSE [g |-> ng, t |-> NoTid, c |-> {}, a |-> FALSE]

(* Contested RELEASE: gen rises past the killed candidate; once none is    *)
(* left, past the own votes (witness.py _release_contested).               *)
CandGenOK(g0, c, rest, O, ng) ==
    /\ ng >= g0
    /\ ng > c[1]
    /\ rest = {} => \A o \in O : o[1] < ng

(* W9 (witness.py _sealed_candidate): a seal for candidate b settles a     *)
(* contested record only if no later generation is passed over: `top <= g *)
(* + 1`, i.e. the other candidates (killed) are at most at b's generation  *)
(* and the record's gen is at most b's generation + 1 ...                  *)
ResolveTop(w, s, b) ==
    /\ \A c \in cand[w][s] \ {b} : c[1] <= b[1]
    /\ gen[w][s] <= b[1] + 1
(* ... and only if the key's own votes are at most at b's generation       *)
(* (`all(v["gen"] <= g for v in rec.votes)`).                              *)
ResolveOK(w, s, b) == \A o \in Own(w, s) : o[1] <= b[1]

(* The evidence ADOPT of v+1 reads for sigil s: the union of the snapshots *)
(* of the honest members of the freezing quorum F of v, plus what F's       *)
(* Byzantine members add.  (UNION and \cup have the same precedence: the    *)
(* parentheses are needed.)                                                 *)
EvB(v, F, XB, s) == (UNION { sb[v][h][s] : h \in F \cap Honest }) \cup XB[s]
EvD(v, F, XD, s) == (UNION { sd[v][h][s] : h \in F \cap Honest }) \cup XD[s]

-----------------------------------------------------------------------------
InitRecords ==
    /\ act = [w \in Honest |-> w \in Members[0]]
    /\ kv  = [w \in Honest |-> 0]
    /\ adv = [w \in Honest |-> IF w \in Members[0] THEN {0} ELSE {}]
    /\ frz = [w \in Honest |-> FALSE]
    /\ gen  = [w \in Honest |-> [s \in Sigils |-> 0]]
    /\ bnd  = [w \in Honest |-> [s \in Sigils |-> NoTid]]
    /\ cand = [w \in Honest |-> [s \in Sigils |-> {}]]
    /\ abst = [w \in Honest |-> [s \in Sigils |-> FALSE]]
    /\ lg   = [w \in Honest |-> [s \in Sigils |-> {}]]
    /\ ld   = [w \in Honest |-> [s \in Sigils |-> {}]]
    /\ fr   = [v \in Vers |-> {}]
    /\ sb   = [v \in Vers |-> [w \in Honest |-> [s \in Sigils |-> {}]]]
    /\ sd   = [v \in Vers |-> [w \in Honest |-> [s \in Sigils |-> {}]]]
    /\ hev  = [v \in Vers |-> [w \in Honest |-> [s \in Sigils |-> {}]]]

Init == votes = {} /\ InitRecords

(* SPEC 5.1 step 4 (the owner is adversarial: every request may arrive).   *)
Spend(w, s, t) ==
    /\ act[w] /\ ~frz[w]
    /\ s \in SigilsOf(t)
    /\ LET g == GenOf(t, s) IN
        /\ \/ g >= gen[w][s] /\ bnd[w][s] = NoTid
           \/ g = gen[w][s] /\ bnd[w][s] = t /\ ~abst[w][s]
        /\ gen'   = [gen EXCEPT ![w][s] = g]
        /\ bnd'   = [bnd EXCEPT ![w][s] = t]
        /\ lg'    = [lg  EXCEPT ![w][s] = @ \cup {<<g, t>>}]
        /\ votes' = votes \cup {Vote(kv[w], w, s, g, t)}
    /\ UNCHANGED <<act, kv, adv, frz, cand, abst, ld, fr, sb, sd, hev>>

(* SPEC 5.2 steps 3-4.                                                      *)
Release(w, s) ==
    /\ act[w] /\ ~frz[w]
    /\ bnd[w][s] \in Tids
    /\ DeathProof(bnd[w][s])
    /\ gen'  = [gen  EXCEPT ![w][s] = @ + 1]
    /\ bnd'  = [bnd  EXCEPT ![w][s] = NoTid]
    /\ abst' = [abst EXCEPT ![w][s] = FALSE]
    /\ ld'   = [ld   EXCEPT ![w][s] = @ \cup {bnd[w][s]}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, cand, lg, fr, sb, sd, hev>>

(* SPEC 5.2 step 2: drop a candidate proven dead.                           *)
ReleaseCand(w, s, c, ng) ==
    /\ act[w] /\ ~frz[w]
    /\ bnd[w][s] = Contested
    /\ c \in cand[w][s]
    /\ DeathProof(c[2])
    /\ ng \in Nat
    /\ CandGenOK(gen[w][s], c, cand[w][s] \ {c}, Own(w, s), ng)
    /\ gen'  = [gen  EXCEPT ![w][s] = ng]
    /\ cand' = [cand EXCEPT ![w][s] = @ \ {c}]
    /\ bnd'  = [bnd  EXCEPT ![w][s] = IF cand[w][s] \ {c} = {} THEN NoTid ELSE Contested]
    /\ ld'   = [ld   EXCEPT ![w][s] = @ \cup {c[2]}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, abst, lg, fr, sb, sd, hev>>

(* W9 (witness.py _release_contested with _sealed_candidate): a SEAL (any  *)
(* version) for candidate b, every other candidate dead, ResolveTop and    *)
(* ResolveOK: bind the record to b at its generation.  (The code kills the *)
(* other candidates with that same seal, so they are AT b's generation;    *)
(* the spec allows any death proofs, a superset.)                          *)
ResolveContested(w, s, b) ==
    /\ act[w] /\ ~frz[w]
    /\ bnd[w][s] = Contested
    /\ b \in cand[w][s]
    /\ Sealed(s, b[1], b[2])
    /\ \A c \in cand[w][s] \ {b} : DeathProof(c[2])
    /\ ResolveTop(w, s, b)
    /\ ResolveOK(w, s, b)
    /\ gen'  = [gen  EXCEPT ![w][s] = b[1]]
    /\ bnd'  = [bnd  EXCEPT ![w][s] = b[2]]
    /\ cand' = [cand EXCEPT ![w][s] = {}]
    /\ abst' = [abst EXCEPT ![w][s] = \E o \in Own(w, s) : o[1] = b[1] /\ o[2] # b[2]]
    /\ ld'   = [ld   EXCEPT ![w][s] = @ \cup { c[2] : c \in cand[w][s] \ {b} }]
    /\ UNCHANGED <<votes, act, kv, adv, frz, lg, fr, sb, sd, hev>>

(* SPEC 5.4 FREEZE: stop voting and releasing in this version; hand over   *)
(* the log.                                                                 *)
Freeze(w) ==
    /\ act[w] /\ ~frz[w]
    /\ frz' = [frz EXCEPT ![w] = TRUE]
    /\ fr'  = [fr  EXCEPT ![kv[w]] = @ \cup {w}]
    /\ sb'  = [sb  EXCEPT ![kv[w]][w] = lg[w]]
    /\ sd'  = [sd  EXCEPT ![kv[w]][w] = ld[w]]
    /\ UNCHANGED <<votes, act, kv, adv, gen, bnd, cand, abst, lg, ld, hev>>

(* SPEC 5.4 ADOPT of version v from a freezing quorum F of v-1.  XB, XD,   *)
(* XS: what Byzantine members of F may add (any bind; releases with a      *)
(* death proof; seals that verify).  The new log is the evidence.          *)
Adopt(w, v, F, XB, XD, XS, NG) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ w \in Members[v]
    /\ act[w] => kv[w] < v
    /\ F \subseteq Members[v - 1]
    /\ Cardinality(F) >= Quorum[v - 1]
    /\ F \cap Honest \subseteq fr[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ XD \in [Sigils -> SUBSET Tids]
    /\ XS \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    /\ \A s \in Sigils : \A b \in XS[s] : Sealed(s, b[1], b[2])
    /\ NG \in [Sigils -> Nat]
    /\ \A s \in Sigils : GenOK(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), Own(w, s), NG[s])
    /\ gen'  = [gen  EXCEPT ![w] = [s \in Sigils |->
                    NewRec(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), XS[s], Own(w, s), NG[s]).g]]
    /\ bnd'  = [bnd  EXCEPT ![w] = [s \in Sigils |->
                    NewRec(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), XS[s], Own(w, s), NG[s]).t]]
    /\ cand' = [cand EXCEPT ![w] = [s \in Sigils |->
                    NewRec(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), XS[s], Own(w, s), NG[s]).c]]
    /\ abst' = [abst EXCEPT ![w] = [s \in Sigils |->
                    NewRec(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), XS[s], Own(w, s), NG[s]).a]]
    /\ lg'   = [lg   EXCEPT ![w] = [s \in Sigils |-> EvB(v - 1, F, XB, s)]]
    /\ ld'   = [ld   EXCEPT ![w] = [s \in Sigils |-> EvD(v - 1, F, XD, s)]]
    /\ hev'  = [hev  EXCEPT ![v][w] = [s \in Sigils |-> EvB(v - 1, F, XB, s)]]
    /\ act'  = [act  EXCEPT ![w] = TRUE]
    /\ kv'   = [kv   EXCEPT ![w] = v]
    /\ adv'  = [adv  EXCEPT ![w] = @ \cup {v}]
    /\ frz'  = [frz  EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<votes, fr, sb, sd>>

ByzVote(b, v, s, g, t) ==
    /\ votes' = votes \cup {Vote(v, b, s, g, t)}
    /\ UNCHANGED <<act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev>>

(* The evidence Byzantine members of a freezing quorum may add (checked in *)
(* Adopt).  TLC instances override these with small sets.                  *)
ForgeBinds == [Sigils -> SUBSET (Nat \X Tids)]
ForgeDead  == [Sigils -> SUBSET Tids]
ForgeSeals == [Sigils -> SUBSET (Nat \X Tids)]

HonestNext ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : Release(w, s)
    \/ \E w \in Honest, s \in Sigils, c \in Nat \X Tids, ng \in Nat : ReleaseCand(w, s, c, ng)
    \/ \E w \in Honest, s \in Sigils, b \in Nat \X Tids : ResolveContested(w, s, b)
    \/ \E w \in Honest : Freeze(w)
    \/ \E w \in Honest, v \in Vers, F \in SUBSET Witnesses,
          XB \in ForgeBinds, XD \in ForgeDead, XS \in ForgeSeals, NG \in [Sigils -> Nat] :
            Adopt(w, v, F, XB, XD, XS, NG)

Next ==
    \/ HonestNext
    \/ \E b \in Byz, v \in Vers, s \in Sigils, g \in Nat, t \in Tids : ByzVote(b, v, s, g, t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* The properties.                                                          *)
Safety ==
    \A t1, t2 \in Tids :
        (t1 # t2 /\ Complete(t1) /\ Complete(t2))
            => SigilsOf(t1) \cap SigilsOf(t2) = {}

OneSealAcrossVersions ==
    \A s \in Sigils, g \in Nat, t1, t2 \in Tids :
        (Sealed(s, g, t1) /\ Sealed(s, g, t2)) => t1 = t2

DeathProofsSound == \A t \in Tids : DeathProof(t) => ~Complete(t)

HonestNoEquiv ==
    \A w \in Honest, s \in Sigils, g \in Nat, v1, v2 \in Vers, t1, t2 \in Tids :
        (HV(v1, w, s, g, t1) /\ HV(v2, w, s, g, t2)) => t1 = t2

-----------------------------------------------------------------------------
(* The inductive invariant.                                                 *)
TypeOK ==
    /\ votes \subseteq [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids]
    /\ act \in [Honest -> BOOLEAN]
    /\ kv  \in [Honest -> Vers]
    /\ adv \in [Honest -> SUBSET Vers]
    /\ frz \in [Honest -> BOOLEAN]
    /\ gen  \in [Honest -> [Sigils -> Nat]]
    /\ bnd  \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]]
    /\ cand \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]
    /\ abst \in [Honest -> [Sigils -> BOOLEAN]]
    /\ lg   \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]
    /\ ld   \in [Honest -> [Sigils -> SUBSET Tids]]
    /\ fr   \in [Vers -> SUBSET Honest]
    /\ sb   \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]
    /\ sd   \in [Vers -> [Honest -> [Sigils -> SUBSET Tids]]]
    /\ hev  \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]

(* An honest vote is cast by a running member, in a version it ran in.     *)
VotesShape ==
    \A x \in votes : x.wit \in Honest =>
        /\ act[x.wit]
        /\ x.ver \in adv[x.wit]
        /\ x.wit \in Members[x.ver]

AdvShape ==
    \A w \in Honest :
        /\ act[w] => /\ kv[w] \in adv[w]
                     /\ \A v \in adv[w] : v <= kv[w]
                     /\ w \in Members[kv[w]]
        /\ ~act[w] => adv[w] = {}

NoEquiv == HonestNoEquiv

ContestedSilent ==
    \A w \in Honest, s \in Sigils : (act[w] /\ bnd[w][s] = Contested) =>
        \A g \in Nat, t \in Tids : ~HV(kv[w], w, s, g, t)

AbstBound ==
    \A w \in Honest, s \in Sigils : (act[w] /\ abst[w][s]) => bnd[w][s] \in Tids

(* Votes the key cast in EARLIER versions never let it equivocate now.      *)
OldVotes ==
    \A w \in Honest, s \in Sigils, v \in Vers, g \in Nat, t \in Tids :
        (act[w] /\ HV(v, w, s, g, t) /\ v < kv[w]) =>
            \/ bnd[w][s] = Contested
            \/ g < gen[w][s]
            \/ g = gen[w][s] /\ bnd[w][s] \in Tids /\ (bnd[w][s] = t \/ abst[w][s])

(* A vote in the current version is the binding at gen, or below gen and   *)
(* dead.                                                                    *)
CurVote ==
    \A w \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (act[w] /\ HV(kv[w], w, s, g, t)) =>
            \/ g < gen[w][s] /\ DeathProof(t)
            \/ g = gen[w][s] /\ bnd[w][s] = t

(* The release discipline, timeless: within one version a key moved past a *)
(* generation where it voted t only after t was proven dead.               *)
RelDisc ==
    \A w \in Honest, s \in Sigils, v \in Vers, g1, g2 \in Nat, t1, t2 \in Tids :
        (HV(v, w, s, g1, t1) /\ HV(v, w, s, g2, t2) /\ g1 < g2) => DeathProof(t1)

(* Every logged bind is passed and dead, or the binding at gen, or a        *)
(* candidate, or (W9) a dead sibling of a binding that is normally sealed.  *)
LogOK ==
    \A w \in Honest, s \in Sigils : act[w] =>
        \A b \in lg[w][s] :
            \/ DeathProof(b[2]) /\ b[1] < gen[w][s]
            \/ b[1] = gen[w][s] /\ bnd[w][s] = b[2]
            \/ bnd[w][s] = Contested /\ b \in cand[w][s] /\ b[1] <= gen[w][s]
            \/ /\ b[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b[2])
               /\ NSealed(s, gen[w][s], bnd[w][s])

LogDead ==
    \A w \in Honest, s \in Sigils : act[w] => \A t \in ld[w][s] : DeathProof(t)

SnapDead ==
    \A v \in Vers, w \in Honest, s \in Sigils : \A t \in sd[v][w][s] : DeathProof(t)

VoteLogged ==
    \A w \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (act[w] /\ HV(kv[w], w, s, g, t)) => <<g, t>> \in lg[w][s]

FrozenAdv == \A v \in Vers, h \in Honest : h \in fr[v] => v \in adv[h]

FrozenStays == \A w \in Honest : (act[w] /\ w \in fr[kv[w]]) => frz[w]

(* A frozen key's snapshot holds the bind behind each vote it cast there.  *)
SnapVotes ==
    \A v \in Vers, h \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (h \in fr[v] /\ HV(v, h, s, g, t)) => <<g, t>> \in sb[v][h][s]

EvLogged == \A w \in Honest, s \in Sigils : act[w] => hev[kv[w]][w][s] \subseteq lg[w][s]

SnapEv == \A v \in Vers, h \in Honest, s \in Sigils : h \in fr[v] => hev[v][h][s] \subseteq sb[v][h][s]

(* The evidence any key adopted for v2 holds the snapshots of a freezing   *)
(* quorum of EVERY earlier version v1 (logs accumulate along the chain).   *)
Lineage ==
    \A w \in Honest, v2 \in Vers, v1 \in Vers : (v2 \in adv[w] /\ v1 < v2) =>
        \E F \in SUBSET Members[v1] :
            /\ Cardinality(F) >= Quorum[v1]
            /\ F \cap Honest \subseteq fr[v1]
            /\ \A h \in F \cap Honest, s \in Sigils : sb[v1][h][s] \subseteq hev[v2][w][s]

(* Every honest vote is normal, or re-votes a tid normally sealed there.   *)
VoteJust ==
    \A w \in Honest, s \in Sigils, v \in Vers, g \in Nat, t \in Tids :
        HV(v, w, s, g, t) => NormalVote(v, w, s, g, t) \/ NSealed(s, g, t)

(* Every seal is backed by a normal quorum (the first seal of a tid at a    *)
(* generation forms before any W9 re-vote of it).                          *)
SealedNormal ==
    \A s \in Sigils, g \in Nat, t \in Tids : Sealed(s, g, t) => NSealed(s, g, t)

Inv ==
    /\ TypeOK
    /\ VotesShape
    /\ AdvShape
    /\ NoEquiv
    /\ ContestedSilent
    /\ AbstBound
    /\ OldVotes
    /\ CurVote
    /\ RelDisc
    /\ LogOK
    /\ LogDead
    /\ SnapDead
    /\ VoteLogged
    /\ FrozenAdv
    /\ FrozenStays
    /\ SnapVotes
    /\ EvLogged
    /\ SnapEv
    /\ Lineage
    /\ VoteJust
    /\ SealedNormal

-----------------------------------------------------------------------------
(* ===================  PART A: static facts  ============================= *)

LEMMA FaultArith ==
    ASSUME NEW n \in Nat, n >= 1, NEW f \in Nat, f = (n - 1) \div 3
    PROVE  n > 3 * f
BY SMT

(* Quorum intersection with Byzantine members, PROVED from the fault bound  *)
(* of version v: any two quorum-sized subsets of v share an HONEST member.  *)
LEMMA HonestInBothQuorums ==
    ASSUME NEW v \in Vers, NEW A, NEW B,
           A \subseteq Members[v], B \subseteq Members[v],
           Cardinality(A) >= Quorum[v], Cardinality(B) >= Quorum[v]
    PROVE  \E w \in A \cap B : w \in Honest
<1> DEFINE M == Members[v]
           n == Cardinality(M)
           f == (n - 1) \div 3
           H == M \ Byz
           AB == A \cap B
<1>mf. IsFiniteSet(M) BY MembersFinite
<1>ne. M # {} BY MembersNonempty
<1>n1. n \in Nat /\ n >= 1 BY <1>mf, <1>ne, FS_EmptySet, FS_CardinalityType
<1>ff. f \in Nat BY <1>n1
<1>fb. Quorum[v] = n - f /\ Cardinality(M \cap Byz) <= f
    BY VersionsFaultBounded DEF FaultBounded, Faults
<1>n3f. n > 3 * f BY <1>n1, <1>ff, FaultArith
<1>af. IsFiniteSet(A) /\ Cardinality(A) \in Nat /\ Cardinality(A) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>bf. IsFiniteSet(B) /\ Cardinality(B) \in Nat /\ Cardinality(B) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>qn. Quorum[v] \in Nat /\ Quorum[v] <= n BY QuorumType, <1>fb, <1>n1
<1>bz. IsFiniteSet(M \cap Byz) /\ Cardinality(M \cap Byz) \in Nat
    BY <1>mf, FS_Intersection, FS_CardinalityType
<1>h1. IsFiniteSet(H) /\ Cardinality(H) = n - Cardinality(M \cap Byz)
    BY <1>mf, FS_Difference
<1>h2. Cardinality(H) \in Nat /\ Cardinality(H) >= n - f
    BY <1>h1, <1>fb, <1>n1, <1>bz, FS_CardinalityType, SMT
<1>hsub. H \subseteq M OBVIOUS
<1>u1. IsFiniteSet(A \cup B) /\ Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(AB)
    BY <1>af, <1>bf, FS_Union
<1>u2. (A \cup B) \subseteq M OBVIOUS
<1>uc. Cardinality(A \cup B) \in Nat BY <1>u1, FS_CardinalityType
<1>u3. Cardinality(A \cup B) <= n BY <1>u1, <1>u2, <1>mf, FS_Subset
<1>abf. IsFiniteSet(AB) /\ Cardinality(AB) \in Nat BY <1>af, FS_Intersection, FS_CardinalityType
<1>ab1. Cardinality(AB) >= Cardinality(A) + Cardinality(B) - n
    BY <1>u1, <1>u3, <1>uc, <1>af, <1>bf, <1>abf, <1>n1, SMT
<1>bign. Cardinality(AB) + Cardinality(H) > n
    BY <1>ab1, <1>h2, <1>af, <1>bf, <1>abf, <1>fb, <1>qn, <1>n1, <1>ff, <1>n3f, SMT
<1>mi. AB \cap H # {}
    BY <1>mf, <1>abf, <1>h2, <1>bign, FS_MajoritiesIntersect
<1>. QED
    <2>1. PICK w \in AB \cap H : TRUE BY <1>mi
    <2>2. w \in A \cap B /\ w \notin Byz OBVIOUS
    <2>3. w \in Witnesses BY <2>2, MembersType
    <2>4. w \in Honest BY <2>2, <2>3 DEF Witnesses
    <2>. QED BY <2>1, <2>2, <2>4

LEMMA QuorumHasHonest ==
    ASSUME NEW v \in Vers, NEW A, A \subseteq Members[v], Cardinality(A) >= Quorum[v]
    PROVE  \E w \in A : w \in Honest
<1>1. \E w \in A \cap A : w \in Honest BY HonestInBothQuorums
<1>. QED BY <1>1

(* ---- Monotonicity in the vote set (votes only ever grow). *)
LEMMA VotersMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW v, NEW s, NEW g, NEW t
    PROVE  /\ VotersV(V1, v, s, g, t) \subseteq VotersV(V2, v, s, g, t)
           /\ AgainstV(V1, v, s, g, t) \subseteq AgainstV(V2, v, s, g, t)
BY DEF VotersV, AgainstV

LEMMA CardMonotoneQuorum ==
    ASSUME NEW v \in Vers, NEW X, NEW Y, X \subseteq Y, Y \subseteq Members[v],
           Cardinality(X) >= Quorum[v]
    PROVE  Cardinality(Y) >= Quorum[v]
<1>1. IsFiniteSet(Members[v]) BY MembersFinite
<1>2. IsFiniteSet(Y) /\ IsFiniteSet(X) BY <1>1, FS_Subset
<1>3. Cardinality(X) <= Cardinality(Y) BY <1>2, FS_Subset
<1>4. Cardinality(X) \in Nat /\ Cardinality(Y) \in Nat BY <1>2, FS_CardinalityType
<1>. QED BY <1>3, <1>4, QuorumType, SMT

LEMMA SealedInMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW v \in Vers, NEW s, NEW g, NEW t,
           SealedInV(V1, v, s, g, t)
    PROVE  SealedInV(V2, v, s, g, t)
<1>1. VotersV(V1, v, s, g, t) \subseteq VotersV(V2, v, s, g, t) BY VotersMonotone
<1>2. VotersV(V2, v, s, g, t) \subseteq Members[v] BY DEF VotersV
<1>. QED BY <1>1, <1>2, CardMonotoneQuorum DEF SealedInV

LEMMA AgainstMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW v \in Vers, NEW s, NEW g, NEW t,
           Cardinality(AgainstV(V1, v, s, g, t)) >= Quorum[v]
    PROVE  Cardinality(AgainstV(V2, v, s, g, t)) >= Quorum[v]
<1>1. AgainstV(V1, v, s, g, t) \subseteq AgainstV(V2, v, s, g, t) BY VotersMonotone
<1>2. AgainstV(V2, v, s, g, t) \subseteq Members[v] BY DEF AgainstV
<1>. QED BY <1>1, <1>2, CardMonotoneQuorum

LEMMA DeathMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW t, DeathProofV(V1, t)
    PROVE  DeathProofV(V2, t)
<1>1. PICK p \in Header[t] :
        \/ \E u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u)
        \/ \E v \in Vers : Cardinality(AgainstV(V1, v, p[1], p[2], t)) >= Quorum[v]
    BY DEF DeathProofV
<1>. QED
    <2>1. CASE \E u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u)
        <3>1. PICK u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u) BY <2>1
        <3>2. PICK v \in Vers : SealedInV(V1, v, p[1], p[2], u) BY <3>1 DEF SealedV
        <3>3. SealedInV(V2, v, p[1], p[2], u) BY <3>2, SealedInMonotone
        <3>. QED BY <3>1, <3>3 DEF DeathProofV, SealedV
    <2>2. CASE \E v \in Vers : Cardinality(AgainstV(V1, v, p[1], p[2], t)) >= Quorum[v]
        <3>1. PICK v \in Vers : Cardinality(AgainstV(V1, v, p[1], p[2], t)) >= Quorum[v] BY <2>2
        <3>2. Cardinality(AgainstV(V2, v, p[1], p[2], t)) >= Quorum[v] BY <3>1, AgainstMonotone
        <3>. QED BY <3>2 DEF DeathProofV
    <2>. QED BY <1>1, <2>1, <2>2

(* A seal for u is a quorum of votes against every other tid.               *)
LEMMA SealedAgainst ==
    ASSUME NEW V, NEW v \in Vers, NEW s, NEW g, NEW t, NEW u \in Tids, u # t,
           SealedInV(V, v, s, g, u)
    PROVE  Cardinality(AgainstV(V, v, s, g, t)) >= Quorum[v]
<1>1. VotersV(V, v, s, g, u) \subseteq AgainstV(V, v, s, g, t) BY DEF VotersV, AgainstV
<1>2. AgainstV(V, v, s, g, t) \subseteq Members[v] BY DEF AgainstV
<1>. QED BY <1>1, <1>2, CardMonotoneQuorum DEF SealedInV

(* So every death proof is a quorum of one version voting against t at one *)
(* of its inputs.                                                           *)
LEMMA DeathAgainst ==
    ASSUME NEW V, NEW t, DeathProofV(V, t)
    PROVE  \E p \in Header[t] : \E v \in Vers :
               Cardinality(AgainstV(V, v, p[1], p[2], t)) >= Quorum[v]
<1>1. PICK p \in Header[t] :
        \/ \E u \in Tids : u # t /\ SealedV(V, p[1], p[2], u)
        \/ \E v \in Vers : Cardinality(AgainstV(V, v, p[1], p[2], t)) >= Quorum[v]
    BY DEF DeathProofV
<1>2. CASE \E u \in Tids : u # t /\ SealedV(V, p[1], p[2], u)
    <2>1. PICK u \in Tids : u # t /\ SealedV(V, p[1], p[2], u) BY <1>2
    <2>2. PICK v \in Vers : SealedInV(V, v, p[1], p[2], u) BY <2>1 DEF SealedV
    <2>3. Cardinality(AgainstV(V, v, p[1], p[2], t)) >= Quorum[v] BY <2>1, <2>2, SealedAgainst
    <2>. QED BY <2>3
<1>3. CASE \E v \in Vers : Cardinality(AgainstV(V, v, p[1], p[2], t)) >= Quorum[v]
    BY <1>3
<1>. QED BY <1>1, <1>2, <1>3

LEMMA GenOfSpec ==
    ASSUME NEW t \in Tids, NEW s \in SigilsOf(t)
    PROVE  GenOf(t, s) \in Nat /\ <<s, GenOf(t, s)>> \in Header[t]
<1>1. PICK p \in Header[t] : s = p[1] BY DEF SigilsOf
<1>2. p \in Sigils \X Nat BY HeaderType DEF ValidHeader
<1>3. <<s, p[2]>> \in Header[t] /\ p[2] \in Nat BY <1>1, <1>2
<1>4. \E g \in Nat : <<s, g>> \in Header[t] BY <1>3
<1>. QED BY <1>4 DEF GenOf

LEMMA VoteEq ==
    ASSUME NEW v, NEW w, NEW s, NEW g, NEW t,
           NEW v2, NEW w2, NEW s2, NEW g2, NEW t2
    PROVE  Vote(v, w, s, g, t) = Vote(v2, w2, s2, g2, t2)
             <=> (v = v2 /\ w = w2 /\ s = s2 /\ g = g2 /\ t = t2)
BY DEF Vote

LEMMA VoteFields ==
    ASSUME NEW v, NEW w, NEW s, NEW g, NEW t
    PROVE  /\ Vote(v, w, s, g, t).ver = v
           /\ Vote(v, w, s, g, t).wit = w
           /\ Vote(v, w, s, g, t).sgl = s
           /\ Vote(v, w, s, g, t).gnr = g
           /\ Vote(v, w, s, g, t).trn = t
BY DEF Vote

(* The adopter's own votes, as ADOPT sees them.                             *)
LEMMA OwnHV ==
    ASSUME NEW w, NEW s, NEW v, NEW g, NEW t, Vote(v, w, s, g, t) \in votes
    PROVE  <<g, t>> \in Own(w, s)
<1> DEFINE x == Vote(v, w, s, g, t)
<1>1. x.wit = w /\ x.sgl = s /\ x.gnr = g /\ x.trn = t BY VoteFields
<1>2. x \in { y \in votes : y.wit = w /\ y.sgl = s } BY <1>1
<1>3. <<x.gnr, x.trn>> \in Own(w, s) BY <1>2 DEF Own
<1>. QED BY <1>1, <1>3

LEMMA OwnType ==
    ASSUME TypeOK, NEW w, NEW s
    PROVE  Own(w, s) \subseteq Nat \X Tids
<1> SUFFICES ASSUME NEW o \in Own(w, s) PROVE o \in Nat \X Tids OBVIOUS
<1>1. PICK x \in { y \in votes : y.wit = w /\ y.sgl = s } : o = <<x.gnr, x.trn>> BY DEF Own
<1>2. x \in [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids] BY <1>1 DEF TypeOK
<1>3. x.gnr \in Nat /\ x.trn \in Tids BY <1>2
<1>. QED BY <1>1, <1>3

(* A normal quorum survives more votes, more death proofs, and evidence    *)
(* changes of keys that have not voted.                                     *)
LEMMA NSealedMono ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW H1, NEW H2,
           \A vv \in Vers, xx \in Honest, ss \in Sigils : \A gg, tt :
               Vote(vv, xx, ss, gg, tt) \in V1 => H2[vv][xx][ss] = H1[vv][xx][ss],
           NEW s \in Sigils, NEW g, NEW t, NSealedV(V1, H1, s, g, t)
    PROVE  NSealedV(V2, H2, s, g, t)
<1>0. PICK v \in Vers : \E Q \in SUBSET Members[v] : NormalQuorumV(V1, H1, v, Q, s, g, t)
    BY DEF NSealedV
<1>1. PICK Q \in SUBSET Members[v] : NormalQuorumV(V1, H1, v, Q, s, g, t)
    BY <1>0
<1>2. Q \subseteq Members[v] /\ Cardinality(Q) >= Quorum[v] BY <1>1 DEF NormalQuorumV
<1>3. \A x \in Q : Vote(v, x, s, g, t) \in V2 BY <1>1 DEF NormalQuorumV
<1>4. \A x \in Q : x \in Honest => NormalVoteV(V2, H2, v, x, s, g, t)
    <2> SUFFICES ASSUME NEW x \in Q, x \in Honest PROVE NormalVoteV(V2, H2, v, x, s, g, t)
        OBVIOUS
    <2>1. Vote(v, x, s, g, t) \in V1 /\ NormalVoteV(V1, H1, v, x, s, g, t) BY <1>1 DEF NormalQuorumV
    <2>2. H2[v][x][s] = H1[v][x][s] BY <2>1
    <2>3. \A u : DeathProofV(V1, u) => DeathProofV(V2, u) BY DeathMonotone
    <2>. QED BY <2>1, <2>2, <2>3 DEF NormalVoteV
<1>5. NormalQuorumV(V2, H2, v, Q, s, g, t) BY <1>2, <1>3, <1>4 DEF NormalQuorumV
<1>. QED BY <1>5 DEF NSealedV

(* ADOPT's decision (NewRec) gives the new record the shape the invariant  *)
(* requires.  This is exactly where the lone rule (LoneOK) is used:        *)
(* without its conditions the conjunct on logged binds (one above the      *)
(* inherited generation, Bug 3) and the one on own votes (one above it,    *)
(* Bug 4) fail.                                                             *)
LEMMA NewRecSpec ==
    ASSUME NEW EB \in SUBSET (Nat \X Tids), NEW ED \in SUBSET Tids, NEW ES,
           NEW O \in SUBSET (Nat \X Tids), NEW ng \in Nat, GenOK(EB, ED, O, ng)
    PROVE  LET r == NewRec(EB, ED, ES, O, ng) IN
           /\ r.g \in Nat
           /\ r.t \in Tids \cup {NoTid, Contested}
           /\ r.c \in SUBSET (Nat \X Tids)
           /\ r.a \in BOOLEAN
           /\ r.a => r.t \in Tids
           /\ \A b \in EB : \/ b[2] \in ED /\ b[1] < r.g
                            \/ b[1] = r.g /\ r.t = b[2]
                            \/ r.t = Contested /\ b \in r.c /\ b[1] <= r.g
                            \/ b[1] = r.g /\ r.t \in Tids /\ b[2] \in ED /\ <<r.g, r.t>> \in ES
           /\ \A o \in O : \/ r.t = Contested
                           \/ o[1] < r.g
                           \/ o[1] = r.g /\ r.t \in Tids /\ (r.t = o[2] \/ r.a)
<1> DEFINE A == Alive(EB, ED)
           r == NewRec(EB, ED, ES, O, ng)
<1>gok. /\ \A b \in EB : b[1] <= ng /\ (b[2] \in ED => b[1] < ng)
        /\ A = {} => \A o \in O : o[1] < ng
    BY DEF GenOK
<1>as. A \subseteq EB BY DEF Alive
<1>1. CASE HasLone(EB, ED, ES, O)
    <2> DEFINE b0 == TheLone(EB, ED, ES, O)
    <2>1. b0 \in EB /\ IsLone(EB, ED, ES, O, b0) BY <1>1 DEF HasLone, TheLone
    <2>2. A = {b0} BY <2>1 DEF IsLone
    <2>3. \A b2 \in EB : b2 # b0 => (b2[1] < b0[1] \/ (b0 \in ES /\ b2[1] = b0[1]))
        BY <2>1 DEF IsLone, LoneOK
    <2>4. \A o \in O : o[1] <= b0[1] BY <2>1 DEF IsLone, LoneOK
    <2>5. r = [g |-> b0[1], t |-> b0[2], c |-> {},
               a |-> \E o \in O : o[1] = b0[1] /\ o[2] # b0[2]]
        BY <1>1 DEF NewRec
    <2>6. b0[1] \in Nat /\ b0[2] \in Tids /\ b0 = <<b0[1], b0[2]>> BY <2>1
    <2>7. \A b \in EB : \/ b[2] \in ED /\ b[1] < r.g
                        \/ b[1] = r.g /\ r.t = b[2]
                        \/ r.t = Contested /\ b \in r.c /\ b[1] <= r.g
                        \/ b[1] = r.g /\ r.t \in Tids /\ b[2] \in ED /\ <<r.g, r.t>> \in ES
        <3> SUFFICES ASSUME NEW b \in EB
                     PROVE  \/ b[2] \in ED /\ b[1] < r.g
                            \/ b[1] = r.g /\ r.t = b[2]
                            \/ r.t = Contested /\ b \in r.c /\ b[1] <= r.g
                            \/ b[1] = r.g /\ r.t \in Tids /\ b[2] \in ED /\ <<r.g, r.t>> \in ES
            OBVIOUS
        <3>1. CASE b = b0 BY <3>1, <2>5
        <3>2. CASE b # b0
            <4>1. b \notin A BY <3>2, <2>2
            <4>2. b[2] \in ED BY <4>1 DEF Alive
            <4>3. b[1] < b0[1] \/ (b0 \in ES /\ b[1] = b0[1]) BY <3>2, <2>3
            <4>4. CASE b[1] < b0[1] BY <4>2, <4>4, <2>5
            <4>5. CASE b0 \in ES /\ b[1] = b0[1] BY <4>2, <4>5, <2>5, <2>6
            <4>. QED BY <4>3, <4>4, <4>5
        <3>. QED BY <3>1, <3>2
    <2>8. \A o \in O : \/ r.t = Contested
                       \/ o[1] < r.g
                       \/ o[1] = r.g /\ r.t \in Tids /\ (r.t = o[2] \/ r.a)
        <3> SUFFICES ASSUME NEW o \in O
                     PROVE  \/ r.t = Contested
                            \/ o[1] < r.g
                            \/ o[1] = r.g /\ r.t \in Tids /\ (r.t = o[2] \/ r.a)
            OBVIOUS
        <3>1. o[1] \in Nat /\ o[2] \in Tids /\ o[1] <= b0[1] BY <2>4
        <3>2. CASE o[1] < b0[1] BY <3>2, <2>5
        <3>3. CASE o[1] = b0[1] /\ o[2] = b0[2] BY <3>3, <2>5, <2>6
        <3>4. CASE o[1] = b0[1] /\ o[2] # b0[2]
            <4>1. r.a BY <3>4, <2>5
            <4>. QED BY <3>4, <4>1, <2>5, <2>6
        <3>. QED BY <3>1, <3>2, <3>3, <3>4, <2>6, SMT
    <2>. QED BY <2>5, <2>6, <2>7, <2>8
<1>2. CASE ~HasLone(EB, ED, ES, O) /\ A # {}
    <2>1. r = [g |-> ng, t |-> Contested, c |-> A, a |-> FALSE] BY <1>2 DEF NewRec
    <2>2. \A b \in EB : \/ b[2] \in ED /\ b[1] < r.g
                        \/ r.t = Contested /\ b \in r.c /\ b[1] <= r.g
        <3> SUFFICES ASSUME NEW b \in EB
                     PROVE  \/ b[2] \in ED /\ b[1] < r.g
                            \/ r.t = Contested /\ b \in r.c /\ b[1] <= r.g
            OBVIOUS
        <3>1. CASE b \in A BY <3>1, <2>1, <1>gok
        <3>2. CASE b \notin A
            <4>1. b[2] \in ED BY <3>2 DEF Alive
            <4>. QED BY <4>1, <2>1, <1>gok
        <3>. QED BY <3>1, <3>2
    <2>. QED BY <2>1, <2>2, <1>as, ContestedFresh
<1>3. CASE ~HasLone(EB, ED, ES, O) /\ A = {}
    <2>1. r = [g |-> ng, t |-> NoTid, c |-> {}, a |-> FALSE] BY <1>3 DEF NewRec
    <2>2. \A b \in EB : b[2] \in ED /\ b[1] < r.g
        <3> SUFFICES ASSUME NEW b \in EB PROVE b[2] \in ED /\ b[1] < r.g OBVIOUS
        <3>1. b \notin A BY <1>3
        <3>2. b[2] \in ED BY <3>1 DEF Alive
        <3>. QED BY <3>2, <2>1, <1>gok
    <2>3. \A o \in O : o[1] < r.g BY <1>3, <1>gok, <2>1
    <2>. QED BY <2>1, <2>2, <2>3
<1>. QED BY <1>1, <1>2, <1>3

-----------------------------------------------------------------------------
(* ============  PART B: SPEC Section 8 from the invariant  =============== *)

LEMMA VoteAdv ==
    ASSUME Inv, NEW v, NEW w \in Honest, NEW s, NEW g, NEW t, HV(v, w, s, g, t)
    PROVE  v \in adv[w]
BY VoteFields DEF Inv, VotesShape, HV

(* THE cross-version transfer.  If A is a quorum of an OLDER version v1,   *)
(* the evidence any honest key adopted for v2 contains the binds behind    *)
(* every v1-vote of some honest member h of A: the lineage gives a         *)
(* freezing quorum F of v1 whose snapshots went into that evidence; A and  *)
(* F share an honest member h (quorum intersection, proved); h froze in    *)
(* v1, and its snapshot holds the bind behind each of its v1 votes.        *)
LEMMA InheritVote ==
    ASSUME Inv, NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv[w], v1 < v2,
           NEW A, A \subseteq Members[v1], Cardinality(A) >= Quorum[v1]
    PROVE  \E h \in A : /\ h \in Honest
                        /\ \A s \in Sigils, g \in Nat, u \in Tids :
                               HV(v1, h, s, g, u) => <<g, u>> \in hev[v2][w][s]
<1>1. PICK F \in SUBSET Members[v1] :
        /\ Cardinality(F) >= Quorum[v1]
        /\ F \cap Honest \subseteq fr[v1]
        /\ \A h \in F \cap Honest, s \in Sigils : sb[v1][h][s] \subseteq hev[v2][w][s]
    BY DEF Inv, Lineage
<1>2. PICK h \in A \cap F : h \in Honest BY <1>1, HonestInBothQuorums
<1>3. h \in fr[v1] BY <1>1, <1>2
<1>4. \A s \in Sigils, g \in Nat, u \in Tids : HV(v1, h, s, g, u) => <<g, u>> \in sb[v1][h][s]
    BY <1>2, <1>3 DEF Inv, SnapVotes
<1>. QED BY <1>1, <1>2, <1>4

(* Two normal quorums for different tids at one (s, g) never coexist, in  *)
(* any versions.                                                           *)
LEMMA TwoNormal ==
    ASSUME Inv, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids, NEW u \in Tids, t # u,
           NEW va \in Vers, NEW Qa, NormalQuorum(va, Qa, s, g, t),
           NEW vb \in Vers, NEW Qb, NormalQuorum(vb, Qb, s, g, u)
    PROVE  FALSE
<1>a. /\ Qa \subseteq Members[va] /\ Cardinality(Qa) >= Quorum[va]
      /\ \A x \in Qa : HV(va, x, s, g, t) /\ (x \in Honest => NormalVote(va, x, s, g, t))
    BY DEF NormalQuorum, NormalQuorumV, HV, NormalVote
<1>b. /\ Qb \subseteq Members[vb] /\ Cardinality(Qb) >= Quorum[vb]
      /\ \A x \in Qb : HV(vb, x, s, g, u) /\ (x \in Honest => NormalVote(vb, x, s, g, u))
    BY DEF NormalQuorum, NormalQuorumV, HV, NormalVote
<1>vn. va \in Nat /\ vb \in Nat BY VersType
<1>1. CASE va = vb
    <2>1. PICK x \in Qa \cap Qb : x \in Honest BY <1>1, <1>a, <1>b, HonestInBothQuorums
    <2>2. HV(va, x, s, g, t) /\ HV(vb, x, s, g, u) BY <2>1, <1>a, <1>b
    <2>. QED BY <2>1, <2>2 DEF Inv, NoEquiv, HonestNoEquiv
<1>2. CASE va < vb
    <2>1. PICK y \in Qb : y \in Honest BY <1>b, QuorumHasHonest
    <2>2. HV(vb, y, s, g, u) /\ NormalVote(vb, y, s, g, u) BY <2>1, <1>b
    <2>3. vb \in adv[y] BY <2>1, <2>2, VoteAdv
    <2>4. PICK x \in Qa : /\ x \in Honest
                          /\ \A s2 \in Sigils, g2 \in Nat, u2 \in Tids :
                                 HV(va, x, s2, g2, u2) => <<g2, u2>> \in hev[vb][y][s2]
        BY <1>2, <1>a, <2>1, <2>3, InheritVote
    <2>5. <<g, t>> \in hev[vb][y][s] BY <2>4, <1>a
    <2>. QED BY <2>2, <2>5 DEF NormalVote, NormalVoteV
<1>3. CASE vb < va
    <2>1. PICK x \in Qa : x \in Honest BY <1>a, QuorumHasHonest
    <2>2. HV(va, x, s, g, t) /\ NormalVote(va, x, s, g, t) BY <2>1, <1>a
    <2>3. va \in adv[x] BY <2>1, <2>2, VoteAdv
    <2>4. PICK y \in Qb : /\ y \in Honest
                          /\ \A s2 \in Sigils, g2 \in Nat, u2 \in Tids :
                                 HV(vb, y, s2, g2, u2) => <<g2, u2>> \in hev[va][x][s2]
        BY <1>3, <1>b, <2>1, <2>3, InheritVote
    <2>5. <<g, u>> \in hev[va][x][s] BY <2>4, <1>b
    <2>. QED BY <2>2, <2>5 DEF NormalVote, NormalVoteV
<1>. QED BY <1>vn, <1>1, <1>2, <1>3

(* A quorum of any version voting against t at (s, g) and a normal quorum *)
(* for t at (s, g) never coexist.                                          *)
LEMMA AgainstVsNormal ==
    ASSUME Inv, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
           NEW v1 \in Vers, Cardinality(Against(v1, s, g, t)) >= Quorum[v1],
           NEW va \in Vers, NEW Qa, NormalQuorum(va, Qa, s, g, t)
    PROVE  FALSE
<1> DEFINE A == Against(v1, s, g, t)
<1>A. /\ A \subseteq Members[v1]
      /\ \A x \in A : \E u \in Tids : u # t /\ HV(v1, x, s, g, u)
    BY DEF Against, AgainstV, HV
<1>a. /\ Qa \subseteq Members[va] /\ Cardinality(Qa) >= Quorum[va]
      /\ \A x \in Qa : HV(va, x, s, g, t) /\ (x \in Honest => NormalVote(va, x, s, g, t))
    BY DEF NormalQuorum, NormalQuorumV, HV, NormalVote
<1>vn. v1 \in Nat /\ va \in Nat BY VersType
<1>1. CASE v1 = va
    <2>1. PICK x \in A \cap Qa : x \in Honest BY <1>1, <1>A, <1>a, HonestInBothQuorums
    <2>2. PICK u \in Tids : u # t /\ HV(v1, x, s, g, u) BY <2>1, <1>A
    <2>3. HV(va, x, s, g, t) BY <2>1, <1>a
    <2>. QED BY <2>1, <2>2, <2>3 DEF Inv, NoEquiv, HonestNoEquiv
<1>2. CASE v1 < va
    <2>1. PICK y \in Qa : y \in Honest BY <1>a, QuorumHasHonest
    <2>2. HV(va, y, s, g, t) /\ NormalVote(va, y, s, g, t) BY <2>1, <1>a
    <2>3. va \in adv[y] BY <2>1, <2>2, VoteAdv
    <2>4. PICK x \in A : /\ x \in Honest
                         /\ \A s2 \in Sigils, g2 \in Nat, u2 \in Tids :
                                HV(v1, x, s2, g2, u2) => <<g2, u2>> \in hev[va][y][s2]
        BY <1>2, <1>A, <2>1, <2>3, InheritVote
    <2>5. PICK u \in Tids : u # t /\ HV(v1, x, s, g, u) BY <2>4, <1>A
    <2>6. <<g, u>> \in hev[va][y][s] BY <2>4, <2>5
    <2>. QED BY <2>2, <2>5, <2>6 DEF NormalVote, NormalVoteV
<1>3. CASE va < v1
    <2>1. PICK x \in A : x \in Honest BY <1>A, QuorumHasHonest
    <2>2. PICK u \in Tids : u # t /\ HV(v1, x, s, g, u) BY <2>1, <1>A
    <2>3. v1 \in adv[x] BY <2>1, <2>2, VoteAdv
    <2>4. PICK y \in Qa : /\ y \in Honest
                          /\ \A s2 \in Sigils, g2 \in Nat, u2 \in Tids :
                                 HV(va, y, s2, g2, u2) => <<g2, u2>> \in hev[v1][x][s2]
        BY <1>3, <1>a, <2>1, <2>3, InheritVote
    <2>5. <<g, t>> \in hev[v1][x][s] BY <2>4, <1>a
    <2>6. NormalVote(v1, x, s, g, u) \/ NSealed(s, g, u) BY <2>1, <2>2 DEF Inv, VoteJust
    <2>7. CASE NormalVote(v1, x, s, g, u) BY <2>7, <2>5, <2>2 DEF NormalVote, NormalVoteV
    <2>8. CASE NSealed(s, g, u)
        <3>0. PICK vb \in Vers : \E Qb \in SUBSET Members[vb] : NormalQuorum(vb, Qb, s, g, u)
            BY <2>8 DEF NSealed, NSealedV, NormalQuorum
        <3>1. PICK Qb \in SUBSET Members[vb] : NormalQuorum(vb, Qb, s, g, u) BY <3>0
        <3>. QED BY <3>1, <2>2, TwoNormal
    <2>. QED BY <2>6, <2>7, <2>8
<1>. QED BY <1>vn, <1>1, <1>2, <1>3

(* The core of Lemmas 1 and 2 across versions.                             *)
LEMMA AgainstExcludesSeal ==
    ASSUME Inv, NEW v1 \in Vers, NEW v2 \in Vers, NEW s \in Sigils, NEW g \in Nat,
           NEW t \in Tids,
           Cardinality(Against(v1, s, g, t)) >= Quorum[v1], SealedIn(v2, s, g, t)
    PROVE  FALSE
<1>1. Sealed(s, g, t) BY DEF Sealed, SealedV, SealedIn
<1>2. NSealed(s, g, t) BY <1>1 DEF Inv, SealedNormal
<1>3. PICK va \in Vers : \E Qa \in SUBSET Members[va] : NormalQuorum(va, Qa, s, g, t)
    BY <1>2 DEF NSealed, NSealedV, NormalQuorum
<1>4. PICK Qa \in SUBSET Members[va] : NormalQuorum(va, Qa, s, g, t) BY <1>3
<1>. QED BY <1>4, AgainstVsNormal

(* Two seals of s at g1 < g2, in any versions: the lower one is dead.      *)
LEMMA SealOrder ==
    ASSUME Inv, NEW v1 \in Vers, NEW v2 \in Vers, NEW s \in Sigils,
           NEW g1 \in Nat, NEW g2 \in Nat, NEW t1 \in Tids, NEW t2 \in Tids,
           SealedIn(v1, s, g1, t1), SealedIn(v2, s, g2, t2), g1 < g2
    PROVE  DeathProof(t1)
<1>1. NSealed(s, g1, t1) BY DEF Inv, SealedNormal, Sealed, SealedV, SealedIn
<1>2. NSealed(s, g2, t2) BY DEF Inv, SealedNormal, Sealed, SealedV, SealedIn
<1>3. PICK va \in Vers : \E Qa \in SUBSET Members[va] : NormalQuorum(va, Qa, s, g1, t1)
    BY <1>1 DEF NSealed, NSealedV, NormalQuorum
<1>3b. PICK Qa \in SUBSET Members[va] : NormalQuorum(va, Qa, s, g1, t1) BY <1>3
<1>4. PICK vb \in Vers : \E Qb \in SUBSET Members[vb] : NormalQuorum(vb, Qb, s, g2, t2)
    BY <1>2 DEF NSealed, NSealedV, NormalQuorum
<1>4b. PICK Qb \in SUBSET Members[vb] : NormalQuorum(vb, Qb, s, g2, t2) BY <1>4
<1>a. /\ Qa \subseteq Members[va] /\ Cardinality(Qa) >= Quorum[va]
      /\ \A x \in Qa : HV(va, x, s, g1, t1) /\ (x \in Honest => NormalVote(va, x, s, g1, t1))
    BY <1>3b DEF NormalQuorum, NormalQuorumV, HV, NormalVote
<1>b. /\ Qb \subseteq Members[vb] /\ Cardinality(Qb) >= Quorum[vb]
      /\ \A x \in Qb : HV(vb, x, s, g2, t2) /\ (x \in Honest => NormalVote(vb, x, s, g2, t2))
    BY <1>4b DEF NormalQuorum, NormalQuorumV, HV, NormalVote
<1>vn. va \in Nat /\ vb \in Nat BY VersType
<1>5. CASE va = vb
    <2>1. PICK x \in Qa \cap Qb : x \in Honest BY <1>5, <1>a, <1>b, HonestInBothQuorums
    <2>2. HV(va, x, s, g1, t1) /\ HV(va, x, s, g2, t2) BY <1>5, <2>1, <1>a, <1>b
    <2>. QED BY <2>1, <2>2 DEF Inv, RelDisc
<1>6. CASE va < vb
    <2>1. PICK y \in Qb : y \in Honest BY <1>b, QuorumHasHonest
    <2>2. HV(vb, y, s, g2, t2) /\ NormalVote(vb, y, s, g2, t2) BY <2>1, <1>b
    <2>3. vb \in adv[y] BY <2>1, <2>2, VoteAdv
    <2>4. PICK x \in Qa : /\ x \in Honest
                          /\ \A s2 \in Sigils, g3 \in Nat, u2 \in Tids :
                                 HV(va, x, s2, g3, u2) => <<g3, u2>> \in hev[vb][y][s2]
        BY <1>6, <1>a, <2>1, <2>3, InheritVote
    <2>5. <<g1, t1>> \in hev[vb][y][s] BY <2>4, <1>a
    <2>. QED BY <2>2, <2>5 DEF NormalVote, NormalVoteV, DeathProof
<1>7. CASE vb < va
    <2>1. PICK x \in Qa : x \in Honest BY <1>a, QuorumHasHonest
    <2>2. HV(va, x, s, g1, t1) /\ NormalVote(va, x, s, g1, t1) BY <2>1, <1>a
    <2>3. va \in adv[x] BY <2>1, <2>2, VoteAdv
    <2>4. PICK y \in Qb : /\ y \in Honest
                          /\ \A s2 \in Sigils, g3 \in Nat, u2 \in Tids :
                                 HV(vb, y, s2, g3, u2) => <<g3, u2>> \in hev[va][x][s2]
        BY <1>7, <1>b, <2>1, <2>3, InheritVote
    <2>5. <<g2, t2>> \in hev[va][x][s] BY <2>4, <1>b
    <2>6. FALSE BY <2>2, <2>5 DEF NormalVote, NormalVoteV
    <2>. QED BY <2>6
<1>. QED BY <1>vn, <1>5, <1>6, <1>7

(* SPEC Section 8 Lemma 1, across ALL charter versions.                     *)
THEOREM Inv_OneSealAcrossVersions == Inv => OneSealAcrossVersions
<1>. SUFFICES ASSUME Inv, NEW s \in Sigils, NEW g \in Nat, NEW t1 \in Tids, NEW t2 \in Tids,
                     Sealed(s, g, t1), Sealed(s, g, t2), t1 # t2
              PROVE  FALSE
    BY DEF OneSealAcrossVersions
<1>1. PICK v1 \in Vers : SealedIn(v1, s, g, t1) BY DEF Sealed, SealedV, SealedIn
<1>2. PICK v2 \in Vers : SealedIn(v2, s, g, t2) BY DEF Sealed, SealedV, SealedIn
<1>3. Cardinality(Against(v2, s, g, t1)) >= Quorum[v2]
    BY <1>2, SealedAgainst DEF SealedIn, Against
<1>. QED BY <1>1, <1>3, AgainstExcludesSeal

(* SPEC Section 8 Lemma 2, across ALL charter versions.                     *)
THEOREM Inv_DeathProofsSound == Inv => DeathProofsSound
<1>. SUFFICES ASSUME Inv, NEW t \in Tids, DeathProof(t), Complete(t)
              PROVE  FALSE
    BY DEF DeathProofsSound
<1>1. PICK p \in Header[t] : \E v \in Vers :
          Cardinality(AgainstV(votes, v, p[1], p[2], t)) >= Quorum[v]
    BY DeathAgainst DEF DeathProof
<1>2. PICK v \in Vers : Cardinality(Against(v, p[1], p[2], t)) >= Quorum[v] BY <1>1 DEF Against
<1>3. p \in Sigils \X Nat BY HeaderType DEF ValidHeader
<1>4. Sealed(p[1], p[2], t) BY DEF Complete, CompleteV, Sealed
<1>5. PICK v2 \in Vers : SealedIn(v2, p[1], p[2], t) BY <1>4 DEF Sealed, SealedV, SealedIn
<1>. QED BY <1>2, <1>3, <1>5, AgainstExcludesSeal

(* ======================  THE SAFETY THEOREM (SPEC 8)  ==================== *)
THEOREM Inv_Safety == Inv => Safety
<1>. SUFFICES ASSUME Inv,
                     NEW t1 \in Tids, NEW t2 \in Tids,
                     t1 # t2, Complete(t1), Complete(t2),
                     NEW s, s \in SigilsOf(t1) \cap SigilsOf(t2)
              PROVE  FALSE
    BY DEF Safety
<1>osg. OneSealAcrossVersions BY Inv_OneSealAcrossVersions
<1>dps. DeathProofsSound BY Inv_DeathProofsSound
<1>p1. PICK g1 \in Nat : <<s, g1>> \in Header[t1]
    BY HeaderType DEF SigilsOf, ValidHeader
<1>p2. PICK g2 \in Nat : <<s, g2>> \in Header[t2]
    BY HeaderType DEF SigilsOf, ValidHeader
<1>sg. s \in Sigils BY <1>p1, HeaderType DEF ValidHeader
<1>se1. Sealed(s, g1, t1) BY <1>p1 DEF Complete, CompleteV, Sealed
<1>se2. Sealed(s, g2, t2) BY <1>p2 DEF Complete, CompleteV, Sealed
<1>1. CASE g1 = g2
    BY <1>1, <1>se1, <1>se2, <1>sg, <1>osg DEF OneSealAcrossVersions
<1>2. CASE g1 < g2
    <2>1. PICK v1 \in Vers : SealedIn(v1, s, g1, t1) BY <1>se1 DEF Sealed, SealedV, SealedIn
    <2>2. PICK v2 \in Vers : SealedIn(v2, s, g2, t2) BY <1>se2 DEF Sealed, SealedV, SealedIn
    <2>3. DeathProof(t1) BY <1>2, <1>sg, <2>1, <2>2, SealOrder
    <2>. QED BY <2>3, <1>dps DEF DeathProofsSound
<1>3. CASE g2 < g1
    <2>1. PICK v1 \in Vers : SealedIn(v1, s, g1, t1) BY <1>se1 DEF Sealed, SealedV, SealedIn
    <2>2. PICK v2 \in Vers : SealedIn(v2, s, g2, t2) BY <1>se2 DEF Sealed, SealedV, SealedIn
    <2>3. DeathProof(t2) BY <1>3, <1>sg, <2>1, <2>2, SealOrder
    <2>. QED BY <2>3, <1>dps DEF DeathProofsSound
<1>. QED BY <1>1, <1>2, <1>3, <1>p1, <1>p2, SMT

-----------------------------------------------------------------------------
(* ============  PART C: Inv is an inductive invariant of Spec  ============ *)

LEMMA InitInv == Init => Inv
<1>. SUFFICES ASSUME Init PROVE Inv OBVIOUS
<1>v. votes = {} BY DEF Init
<1>r. InitRecords BY DEF Init
<1>T. TypeOK
    <2>1. votes \subseteq [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids] BY <1>v
    <2>2. act \in [Honest -> BOOLEAN] BY <1>r DEF InitRecords
    <2>3. kv \in [Honest -> Vers] BY <1>r, VersType DEF InitRecords
    <2>4. adv \in [Honest -> SUBSET Vers] BY <1>r, VersType DEF InitRecords
    <2>5. /\ frz \in [Honest -> BOOLEAN]
          /\ gen \in [Honest -> [Sigils -> Nat]]
          /\ bnd \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]]
          /\ cand \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]
          /\ abst \in [Honest -> [Sigils -> BOOLEAN]]
          /\ lg \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]
          /\ ld \in [Honest -> [Sigils -> SUBSET Tids]]
        BY <1>r DEF InitRecords
    <2>6. /\ fr \in [Vers -> SUBSET Honest]
          /\ sb \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]
          /\ sd \in [Vers -> [Honest -> [Sigils -> SUBSET Tids]]]
          /\ hev \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]
        BY <1>r DEF InitRecords
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
<1>A. AdvShape BY <1>r, VersType DEF InitRecords, AdvShape
<1>C. ContestedSilent BY <1>r, ContestedFresh, TidsNoTid DEF InitRecords, ContestedSilent
<1>B. AbstBound BY <1>r DEF InitRecords, AbstBound
<1>V1. VotesShape /\ NoEquiv BY <1>v DEF VotesShape, NoEquiv, HonestNoEquiv, HV
<1>V2. OldVotes /\ CurVote /\ RelDisc BY <1>v DEF OldVotes, CurVote, RelDisc, HV
<1>V3. VoteLogged /\ VoteJust BY <1>v DEF VoteLogged, VoteJust, HV
<1>L1. LogOK BY <1>r DEF InitRecords, LogOK
<1>L2. LogDead BY <1>r DEF InitRecords, LogDead
<1>L3. SnapDead BY <1>r DEF InitRecords, SnapDead
<1>L4. FrozenAdv /\ FrozenStays BY <1>r, VersType DEF InitRecords, FrozenAdv, FrozenStays
<1>L5. SnapVotes BY <1>r DEF InitRecords, SnapVotes
<1>L6. EvLogged BY <1>r, VersType DEF InitRecords, EvLogged
<1>L7. SnapEv BY <1>r DEF InitRecords, SnapEv
<1>N. Lineage
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv[w], v1 < v2
                 PROVE  FALSE
        BY DEF Lineage
    <2>1. v2 = 0 BY <1>r DEF InitRecords
    <2>. QED BY <2>1, VersType
<1>S. SealedNormal
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids, Sealed(s, g, t)
                 PROVE  NSealed(s, g, t)
        BY DEF SealedNormal
    <2>1. PICK v \in Vers : SealedIn(v, s, g, t) BY DEF Sealed, SealedV, SealedIn
    <2> DEFINE Q == VotersV(votes, v, s, g, t)
    <2>2. Q \subseteq Members[v] /\ Cardinality(Q) >= Quorum[v] BY <2>1 DEF SealedIn, SealedInV, VotersV
    <2>3. Q = {} BY <1>v DEF VotersV
    <2>4. NormalQuorumV(votes, hev, v, Q, s, g, t) BY <2>2, <2>3 DEF NormalQuorumV
    <2>. QED BY <2>2, <2>4 DEF NSealed, NSealedV
<1>. QED BY <1>T, <1>A, <1>C, <1>B, <1>V1, <1>V2, <1>V3, <1>L1, <1>L2, <1>L3, <1>L4,
            <1>L5, <1>L6, <1>L7, <1>N, <1>S DEF Inv

(* ---------------------------------------------------------------- Spend  *)
LEMMA SpendInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, NEW t0 \in Tids, Spend(w0, s0, t0)
    PROVE  Inv'
<1> DEFINE g0 == GenOf(t0, s0)
           v0 == kv[w0]
           nv == Vote(v0, w0, s0, g0, t0)
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. act[w0] /\ ~frz[w0] /\ s0 \in SigilsOf(t0) BY DEF Spend
<1>g. g0 \in Nat /\ <<s0, g0>> \in Header[t0] BY <1>a, GenOfSpec
<1>pre. \/ g0 >= gen[w0][s0] /\ bnd[w0][s0] = NoTid
        \/ g0 = gen[w0][s0] /\ bnd[w0][s0] = t0 /\ ~abst[w0][s0]
    BY DEF Spend
<1>post. /\ gen' = [gen EXCEPT ![w0][s0] = g0]
         /\ bnd' = [bnd EXCEPT ![w0][s0] = t0]
         /\ lg' = [lg EXCEPT ![w0][s0] = @ \cup {<<g0, t0>>}]
         /\ votes' = votes \cup {nv}
         /\ UNCHANGED <<act, kv, adv, frz, cand, abst, ld, fr, sb, sd, hev>>
    BY DEF Spend
<1>gn. gen[w0][s0] \in Nat /\ g0 >= gen[w0][s0] BY <1>i, <1>g, <1>pre DEF TypeOK
<1>v0. v0 \in Vers /\ v0 \in adv[w0] /\ w0 \in Members[v0] BY <1>a, <1>i DEF TypeOK, AdvShape
<1>gen. \A w \in Honest, s \in Sigils : gen'[w][s] = IF w = w0 /\ s = s0 THEN g0 ELSE gen[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>bnd. \A w \in Honest, s \in Sigils : bnd'[w][s] = IF w = w0 /\ s = s0 THEN t0 ELSE bnd[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>lg. \A w \in Honest, s \in Sigils :
         lg'[w][s] = IF w = w0 /\ s = s0 THEN lg[w][s] \cup {<<g0, t0>>} ELSE lg[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=>
          (HV(v, w, s, g, t) \/ (v = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t = t0))
    BY <1>post, VoteEq DEF HV
<1>sub. votes \subseteq votes' BY <1>post
<1>dp. \A t : DeathProof(t) => DeathProof(t)' BY <1>sub, DeathMonotone DEF DeathProof
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t) => NormalVote(v, w, s, g, t)'
    BY <1>post, <1>dp DEF NormalVote, NormalVoteV, DeathProof
<1>nsm. \A s \in Sigils : \A g, t : NSealed(s, g, t) => NSealed(s, g, t)'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g, NEW t, NSealed(s, g, t)
                 PROVE  NSealed(s, g, t)'
        OBVIOUS
    <2>1. \A vv \in Vers, xx \in Honest, ss \in Sigils : \A gg, tt :
             Vote(vv, xx, ss, gg, tt) \in votes => hev'[vv][xx][ss] = hev[vv][xx][ss]
        BY <1>post
    <2>. QED BY <2>1, <1>sub, NSealedMono DEF NSealed
<1>ndc. bnd[w0][s0] # Contested BY <1>pre, ContestedFresh
<1>cur. \A g \in Nat, t \in Tids : HV(v0, w0, s0, g, t) =>
          \/ g < gen[w0][s0] /\ DeathProof(t)
          \/ g = gen[w0][s0] /\ bnd[w0][s0] = t
    BY <1>a, <1>i DEF CurVote
<1>old. \A v \in Vers, g \in Nat, t \in Tids : (HV(v, w0, s0, g, t) /\ v < v0) =>
          \/ bnd[w0][s0] = Contested
          \/ g < gen[w0][s0]
          \/ g = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = t \/ abst[w0][s0])
    BY <1>a, <1>i DEF OldVotes
<1>vle. \A v \in Vers, g \in Nat, t \in Tids : HV(v, w0, s0, g, t) => v <= v0
    <2> SUFFICES ASSUME NEW v \in Vers, NEW g \in Nat, NEW t \in Tids, HV(v, w0, s0, g, t)
                 PROVE  v <= v0
        OBVIOUS
    <2>1. v \in adv[w0] BY VoteFields, <1>i DEF VotesShape, HV
    <2>. QED BY <2>1, <1>a, <1>i DEF AdvShape
(* Every earlier vote of w0 on s0 at g0 is for t0.                         *)
<1>same. \A v \in Vers, u \in Tids : HV(v, w0, s0, g0, u) => u = t0
    <2> SUFFICES ASSUME NEW v \in Vers, NEW u \in Tids, HV(v, w0, s0, g0, u) PROVE u = t0
        OBVIOUS
    <2>0. v \in Nat /\ v0 \in Nat BY <1>v0, VersType
    <2>1. v <= v0 BY <1>vle, <1>g
    <2>2. CASE v = v0
        <3>1. \/ g0 < gen[w0][s0] /\ DeathProof(u)
              \/ g0 = gen[w0][s0] /\ bnd[w0][s0] = u
            BY <2>2, <1>cur, <1>g
        <3>2. g0 = gen[w0][s0] /\ bnd[w0][s0] = u BY <3>1, <1>gn, <1>g
        <3>. QED BY <3>2, <1>pre, TidsNoTid
    <2>3. CASE v < v0
        <3>1. \/ bnd[w0][s0] = Contested
              \/ g0 < gen[w0][s0]
              \/ g0 = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = u \/ abst[w0][s0])
            BY <2>3, <1>old, <1>g
        <3>2. g0 = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = u \/ abst[w0][s0])
            BY <3>1, <1>ndc, <1>gn, <1>g
        <3>3. bnd[w0][s0] = t0 /\ ~abst[w0][s0] BY <3>2, <1>pre, TidsNoTid
        <3>. QED BY <3>2, <3>3
    <2>. QED BY <2>0, <2>1, <2>2, <2>3
(* The new vote is normal, unless t0 is already normally sealed at (s0,g0). *)
<1>nv. ~NSealed(s0, g0, t0) => NormalVoteV(votes', hev', v0, w0, s0, g0, t0)
    <2> SUFFICES ASSUME ~NSealed(s0, g0, t0), NEW b \in hev'[v0][w0][s0]
                 PROVE  (b[1] = g0 /\ b[2] = t0) \/ (b[1] < g0 /\ DeathProofV(votes', b[2]))
        BY DEF NormalVoteV
    <2>1. b \in hev[v0][w0][s0] BY <1>post
    <2>2. b \in lg[w0][s0] BY <2>1, <1>a, <1>i DEF EvLogged
    <2>3. \/ DeathProof(b[2]) /\ b[1] < gen[w0][s0]
          \/ b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
          \/ bnd[w0][s0] = Contested /\ b \in cand[w0][s0] /\ b[1] <= gen[w0][s0]
          \/ /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
             /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
        BY <2>2, <1>a, <1>i DEF LogOK
    <2>4. b[1] \in Nat /\ b[2] \in Tids BY <2>2, <1>i DEF TypeOK
    <2>5. CASE DeathProof(b[2]) /\ b[1] < gen[w0][s0]
        <3>1. b[1] < g0 BY <2>5, <2>4, <1>gn, <1>g
        <3>2. DeathProofV(votes', b[2]) BY <2>5, <1>dp DEF DeathProof
        <3>. QED BY <3>1, <3>2
    <2>6. CASE b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
        <3>1. bnd[w0][s0] = t0 /\ g0 = gen[w0][s0] BY <2>6, <2>4, <1>pre, TidsNoTid
        <3>. QED BY <2>6, <3>1
    <2>7. CASE /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
               /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
        <3>1. bnd[w0][s0] = t0 /\ g0 = gen[w0][s0] BY <2>7, <1>pre, TidsNoTid
        <3>. QED BY <2>7, <3>1
    <2>. QED BY <2>3, <2>5, <2>6, <2>7, <1>ndc

<1>T. TypeOK'
    <2>1. nv \in [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids]
        BY <1>v0, <1>g DEF Vote, Witnesses
    <2>2. votes' \subseteq [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids]
        BY <2>1, <1>post, <1>i DEF TypeOK
    <2>3. gen' \in [Honest -> [Sigils -> Nat]] BY <1>i, <1>post, <1>g DEF TypeOK
    <2>4. bnd' \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]] BY <1>i, <1>post DEF TypeOK
    <2>5. lg' \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]] BY <1>i, <1>post, <1>g DEF TypeOK
    <2>. QED BY <2>2, <2>3, <2>4, <2>5, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape'
    <2> SUFFICES ASSUME NEW x \in votes', x.wit \in Honest
                 PROVE  act'[x.wit] /\ x.ver \in adv'[x.wit] /\ x.wit \in Members[x.ver]
        BY DEF VotesShape
    <2>1. CASE x \in votes BY <2>1, <1>i, <1>post DEF VotesShape
    <2>2. CASE x = nv
        <3>1. x.wit = w0 /\ x.ver = v0 BY <2>2, VoteFields
        <3>. QED BY <3>1, <1>a, <1>v0, <1>post
    <2>. QED BY <2>1, <2>2, <1>post
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat,
                        NEW v1 \in Vers, NEW v2 \in Vers, NEW t1 \in Tids, NEW t2 \in Tids,
                        HV(v1, w, s, g, t1)', HV(v2, w, s, g, t2)'
                 PROVE  t1 = t2
        BY DEF NoEquiv, HonestNoEquiv
    <2>1. HV(v1, w, s, g, t1) \/ (v1 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t1 = t0) BY <1>hv
    <2>2. HV(v2, w, s, g, t2) \/ (v2 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t2 = t0) BY <1>hv
    <2>3. CASE HV(v1, w, s, g, t1) /\ HV(v2, w, s, g, t2)
        BY <2>3, <1>i DEF NoEquiv, HonestNoEquiv
    <2>4. CASE (v1 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t1 = t0) /\ HV(v2, w, s, g, t2)
        BY <2>4, <1>same
    <2>5. CASE HV(v1, w, s, g, t1) /\ (v2 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t2 = t0)
        BY <2>5, <1>same
    <2>6. CASE (v1 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t1 = t0)
               /\ (v2 = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t2 = t0)
        BY <2>6
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>CS. ContestedSilent'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], bnd'[w][s] = Contested,
                        NEW g \in Nat, NEW t \in Tids, HV(kv[w], w, s, g, t)'
                 PROVE  FALSE
        BY DEF ContestedSilent
    <2>1. ~(w = w0 /\ s = s0) BY <1>bnd, ContestedFresh
    <2>2. bnd[w][s] = Contested BY <2>1, <1>bnd
    <2>3. HV(kv[w], w, s, g, t) BY <2>1, <1>hv, <1>post
    <2>. QED BY <2>2, <2>3, <1>i, <1>post DEF ContestedSilent
<1>AB. AbstBound'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], abst'[w][s]
                 PROVE  bnd'[w][s] \in Tids
        BY DEF AbstBound
    <2>1. CASE w = w0 /\ s = s0 BY <2>1, <1>bnd
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>2, <1>bnd, <1>i, <1>post DEF AbstBound
    <2>. QED BY <2>1, <2>2
<1>OV. OldVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, act'[w], HV(v, w, s, g, t)', v < kv'[w]
                 PROVE  \/ bnd'[w][s] = Contested
                        \/ g < gen'[w][s]
                        \/ g = gen'[w][s] /\ bnd'[w][s] \in Tids /\ (bnd'[w][s] = t \/ abst'[w][s])
        BY DEF OldVotes
    <2>0. HV(v, w, s, g, t) /\ act[w] /\ v < kv[w] BY <1>hv, <1>post, <1>v0, VersType
    <2>1. CASE w = w0 /\ s = s0
        <3>1. \/ bnd[w0][s0] = Contested
              \/ g < gen[w0][s0]
              \/ g = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = t \/ abst[w0][s0])
            BY <2>0, <2>1, <1>old
        <3>3. CASE g < gen[w0][s0] BY <3>3, <2>1, <1>gen, <1>gn, <1>g
        <3>4. CASE g = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = t \/ abst[w0][s0])
            <4>1. g0 = gen[w0][s0] /\ bnd[w0][s0] = t0 /\ ~abst[w0][s0] BY <3>4, <1>pre, TidsNoTid
            <4>2. t0 = t BY <3>4, <4>1
            <4>. QED BY <2>1, <3>4, <4>1, <4>2, <1>gen, <1>bnd
        <3>. QED BY <3>1, <1>ndc, <3>3, <3>4
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>0, <2>2, <1>gen, <1>bnd, <1>i, <1>post DEF OldVotes
    <2>. QED BY <2>1, <2>2
<1>CV. CurVote'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  \/ g < gen'[w][s] /\ DeathProof(t)'
                        \/ g = gen'[w][s] /\ bnd'[w][s] = t
        BY DEF CurVote
    <2>0. act[w] BY <1>post
    <2>1. CASE kv[w] = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t = t0 BY <2>1, <1>gen, <1>bnd
    <2>2. CASE HV(kv[w], w, s, g, t)
        <3>1. \/ g < gen[w][s] /\ DeathProof(t)
              \/ g = gen[w][s] /\ bnd[w][s] = t
            BY <2>0, <2>2, <1>i DEF CurVote
        <3>2. CASE w = w0 /\ s = s0
            <4>1. CASE g < gen[w0][s0] /\ DeathProof(t) BY <4>1, <3>2, <1>gen, <1>gn, <1>g, <1>dp
            <4>2. CASE g = gen[w0][s0] /\ bnd[w0][s0] = t
                <5>1. bnd[w0][s0] = t0 /\ g0 = gen[w0][s0] BY <4>2, <1>pre, TidsNoTid
                <5>. QED BY <4>2, <5>1, <3>2, <1>gen, <1>bnd
            <4>. QED BY <3>1, <3>2, <4>1, <4>2
        <3>3. CASE ~(w = w0 /\ s = s0) BY <3>1, <3>3, <1>gen, <1>bnd, <1>dp
        <3>. QED BY <3>2, <3>3
    <2>. QED BY <1>hv, <1>post, <2>1, <2>2
<1>RD. RelDisc'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers,
                        NEW g1 \in Nat, NEW g2 \in Nat, NEW t1 \in Tids, NEW t2 \in Tids,
                        HV(v, w, s, g1, t1)', HV(v, w, s, g2, t2)', g1 < g2
                 PROVE  DeathProof(t1)'
        BY DEF RelDisc
    <2>1. CASE HV(v, w, s, g1, t1) /\ HV(v, w, s, g2, t2) BY <2>1, <1>i, <1>dp DEF RelDisc
    <2>2. CASE (v = v0 /\ w = w0 /\ s = s0 /\ g2 = g0 /\ t2 = t0) /\ HV(v, w, s, g1, t1)
        <3>1. \/ g1 < gen[w0][s0] /\ DeathProof(t1)
              \/ g1 = gen[w0][s0] /\ bnd[w0][s0] = t1
            BY <2>2, <1>cur
        <3>2. CASE g1 < gen[w0][s0] /\ DeathProof(t1) BY <3>2, <1>dp
        <3>3. CASE g1 = gen[w0][s0] /\ bnd[w0][s0] = t1
            <4>1. g0 > gen[w0][s0] BY <3>3, <2>2
            <4>2. bnd[w0][s0] = NoTid BY <4>1, <1>pre
            <4>. QED BY <4>2, <3>3, TidsNoTid
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. CASE HV(v, w, s, g2, t2) /\ (v = v0 /\ w = w0 /\ s = s0 /\ g1 = g0 /\ t1 = t0)
        <3>1. \/ g2 < gen[w0][s0] /\ DeathProof(t2)
              \/ g2 = gen[w0][s0] /\ bnd[w0][s0] = t2
            BY <2>3, <1>cur
        <3>2. g2 <= gen[w0][s0] BY <3>1, <1>gn
        <3>. QED BY <3>2, <2>3, <1>gn
    <2>4. CASE (v = v0 /\ w = w0 /\ s = s0 /\ g1 = g0 /\ t1 = t0)
               /\ (v = v0 /\ w = w0 /\ s = s0 /\ g2 = g0 /\ t2 = t0)
        BY <2>4
    <2>. QED BY <1>hv, <2>1, <2>2, <2>3, <2>4
<1>LO. LogOK'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW b \in lg'[w][s]
                 PROVE  \/ DeathProof(b[2])' /\ b[1] < gen'[w][s]
                        \/ b[1] = gen'[w][s] /\ bnd'[w][s] = b[2]
                        \/ bnd'[w][s] = Contested /\ b \in cand'[w][s] /\ b[1] <= gen'[w][s]
                        \/ /\ b[1] = gen'[w][s] /\ bnd'[w][s] \in Tids /\ DeathProof(b[2])'
                           /\ NSealed(s, gen[w][s], bnd[w][s])'
        BY DEF LogOK
    <2>1. CASE w = w0 /\ s = s0
        <3>1. CASE b = <<g0, t0>> BY <3>1, <2>1, <1>gen, <1>bnd
        <3>2. CASE b \in lg[w0][s0]
            <4>1. \/ DeathProof(b[2]) /\ b[1] < gen[w0][s0]
                  \/ b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
                  \/ bnd[w0][s0] = Contested /\ b \in cand[w0][s0] /\ b[1] <= gen[w0][s0]
                  \/ /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
                     /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
                BY <3>2, <1>a, <1>i DEF LogOK
            <4>2. b[1] \in Nat /\ b[2] \in Tids BY <3>2, <1>i DEF TypeOK
            <4>3. CASE DeathProof(b[2]) /\ b[1] < gen[w0][s0]
                BY <4>3, <4>2, <2>1, <1>gen, <1>gn, <1>g, <1>dp
            <4>4. CASE b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
                <5>1. bnd[w0][s0] = t0 /\ g0 = gen[w0][s0] BY <4>4, <4>2, <1>pre, TidsNoTid
                <5>. QED BY <4>4, <5>1, <2>1, <1>gen, <1>bnd
            <4>5. CASE /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
                       /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
                <5>1. bnd[w0][s0] = t0 /\ g0 = gen[w0][s0] BY <4>5, <1>pre, TidsNoTid
                <5>2. NSealed(s0, g0, t0)' BY <4>5, <5>1, <1>nsm, <1>g
                <5>3. gen'[w0][s0] = g0 /\ bnd'[w0][s0] = t0 BY <1>gen, <1>bnd
                <5>. QED BY <4>5, <5>1, <5>2, <5>3, <2>1, <1>dp
            <4>. QED BY <4>1, <4>3, <4>4, <4>5, <1>ndc
        <3>. QED BY <3>1, <3>2, <2>1, <1>lg
    <2>2. CASE ~(w = w0 /\ s = s0)
        <3>0. act[w] BY <1>post
        <3>1. b \in lg[w][s] BY <2>2, <1>lg
        <3>2. \/ DeathProof(b[2]) /\ b[1] < gen[w][s]
              \/ b[1] = gen[w][s] /\ bnd[w][s] = b[2]
              \/ bnd[w][s] = Contested /\ b \in cand[w][s] /\ b[1] <= gen[w][s]
              \/ /\ b[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s, gen[w][s], bnd[w][s])
            BY <3>0, <3>1, <1>i DEF LogOK
        <3>3. gen'[w][s] = gen[w][s] /\ bnd'[w][s] = bnd[w][s] /\ cand'[w][s] = cand[w][s]
            BY <2>2, <1>gen, <1>bnd, <1>post
        <3>4. gen[w][s] \in Nat /\ bnd[w][s] \in Tids \cup {NoTid, Contested} BY <1>i DEF TypeOK
        <3>5. NSealed(s, gen[w][s], bnd[w][s]) => NSealed(s, gen[w][s], bnd[w][s])'
            <4>1. NSealed(s, gen[w][s], bnd[w][s]) => NSealedV(votes', hev', s, gen[w][s], bnd[w][s])
                BY <1>nsm DEF NSealed
            <4>. QED BY <4>1, <3>3 DEF NSealed
        <3>. QED BY <3>2, <3>3, <3>5, <1>dp
    <2>. QED BY <2>1, <2>2
<1>LD. LogDead' BY <1>i, <1>post, <1>dp DEF LogDead
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  <<g, t>> \in lg'[w][s]
        BY DEF VoteLogged
    <2>1. CASE kv[w] = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t = t0 BY <2>1, <1>lg
    <2>2. CASE HV(kv[w], w, s, g, t)
        <3>1. <<g, t>> \in lg[w][s] BY <2>2, <1>i, <1>post DEF VoteLogged
        <3>. QED BY <3>1, <1>lg
    <2>. QED BY <1>hv, <1>post, <2>1, <2>2
<1>FA. FrozenAdv' BY <1>i, <1>post DEF FrozenAdv
<1>FS. FrozenStays' BY <1>i, <1>post DEF FrozenStays
<1>SV. SnapVotes'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, NEW s \in Sigils, NEW g \in Nat,
                        NEW t \in Tids, h \in fr'[v], HV(v, h, s, g, t)'
                 PROVE  <<g, t>> \in sb'[v][h][s]
        BY DEF SnapVotes
    <2>1. h \in fr[v] /\ sb'[v][h][s] = sb[v][h][s] BY <1>post
    <2>2. CASE HV(v, h, s, g, t) BY <2>1, <2>2, <1>i DEF SnapVotes
    <2>3. CASE v = v0 /\ h = w0 /\ s = s0 /\ g = g0 /\ t = t0
        <3>1. w0 \notin fr[v0] BY <1>a, <1>i DEF FrozenStays
        <3>. QED BY <3>1, <2>1, <2>3
    <2>. QED BY <1>hv, <2>2, <2>3
<1>EL. EvLogged'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w]
                 PROVE  hev'[kv'[w]][w][s] \subseteq lg'[w][s]
        BY DEF EvLogged
    <2>1. hev[kv[w]][w][s] \subseteq lg[w][s] BY <1>i, <1>post DEF EvLogged
    <2>2. lg[w][s] \subseteq lg'[w][s] BY <1>lg
    <2>. QED BY <2>1, <2>2, <1>post
<1>SE. SnapEv' BY <1>i, <1>post DEF SnapEv
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage
<1>VJ. VoteJust'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, HV(v, w, s, g, t)'
                 PROVE  NormalVote(v, w, s, g, t)' \/ NSealed(s, g, t)'
        BY DEF VoteJust
    <2>1. CASE HV(v, w, s, g, t)
        <3>1. NormalVote(v, w, s, g, t) \/ NSealed(s, g, t) BY <2>1, <1>i DEF VoteJust
        <3>. QED BY <3>1, <1>nm, <1>nsm
    <2>2. CASE v = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t = t0
        <3>1. CASE NSealed(s0, g0, t0) BY <3>1, <2>2, <1>nsm, <1>g
        <3>2. CASE ~NSealed(s0, g0, t0)
            <4>1. NormalVoteV(votes', hev', v0, w0, s0, g0, t0) BY <3>2, <1>nv
            <4>2. NormalVote(v, w, s, g, t)' BY <4>1, <2>2 DEF NormalVote
            <4>. QED BY <4>2
        <3>. QED BY <3>1, <3>2
    <2>. QED BY <1>hv, <2>1, <2>2
<1>SN. SealedNormal'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids, Sealed(s, g, t)'
                 PROVE  NSealed(s, g, t)'
        BY DEF SealedNormal
    <2>1. CASE NSealed(s, g, t) BY <2>1, <1>nsm
    <2>2. CASE ~NSealed(s, g, t)
        <3>1. ~Sealed(s, g, t) BY <2>2, <1>i DEF SealedNormal
        <3>2. PICK v \in Vers : SealedInV(votes', v, s, g, t) BY DEF Sealed, SealedV
        <3>3. \A x : Vote(v, x, s, g, t) \in votes' <=>
                       (Vote(v, x, s, g, t) \in votes \/ (v = v0 /\ x = w0 /\ s = s0 /\ g = g0 /\ t = t0))
            BY <1>post, VoteEq
        <3>4. v = v0 /\ s = s0 /\ g = g0 /\ t = t0
            <4> SUFFICES ASSUME ~(v = v0 /\ s = s0 /\ g = g0 /\ t = t0) PROVE FALSE OBVIOUS
            <4>1. VotersV(votes', v, s, g, t) = VotersV(votes, v, s, g, t) BY <3>3 DEF VotersV
            <4>2. SealedInV(votes, v, s, g, t) BY <3>2, <4>1 DEF SealedInV
            <4>. QED BY <4>2, <3>1 DEF Sealed, SealedV
        <3> DEFINE Q == VotersV(votes', v0, s0, g0, t0)
        <3>5. Q \subseteq Members[v0] /\ Cardinality(Q) >= Quorum[v0]
            BY <3>2, <3>4 DEF VotersV, SealedInV
        <3>6. \A x \in Q : Vote(v0, x, s0, g0, t0) \in votes' BY DEF VotersV
        <3>7. \A x \in Q : x \in Honest => NormalVoteV(votes', hev', v0, x, s0, g0, t0)
            <4> SUFFICES ASSUME NEW x \in Q, x \in Honest
                         PROVE  NormalVoteV(votes', hev', v0, x, s0, g0, t0)
                OBVIOUS
            <4>1. CASE x = w0
                <5>1. ~NSealed(s0, g0, t0) BY <2>2, <3>4
                <5>. QED BY <4>1, <5>1, <1>nv
            <4>2. CASE x # w0
                <5>1. HV(v0, x, s0, g0, t0)
                    <6>1. Vote(v0, x, s0, g0, t0) \in votes' BY <3>6
                    <6>2. Vote(v, x, s, g, t) \in votes \/ (v = v0 /\ x = w0 /\ s = s0 /\ g = g0 /\ t = t0)
                        BY <6>1, <3>3, <3>4
                    <6>. QED BY <6>2, <4>2, <3>4 DEF HV
                <5>2. NormalVote(v0, x, s0, g0, t0) \/ NSealed(s0, g0, t0)
                    BY <5>1, <1>i, <1>v0, <1>g DEF VoteJust
                <5>3. NormalVote(v0, x, s0, g0, t0) BY <5>2, <2>2, <3>4
                <5>. QED BY <5>3, <1>nm DEF NormalVote
            <4>. QED BY <4>1, <4>2
        <3>8. NormalQuorumV(votes', hev', v0, Q, s0, g0, t0) BY <3>5, <3>6, <3>7 DEF NormalQuorumV
        <3>. QED BY <3>8, <3>5, <3>4, <1>v0 DEF NSealed, NSealedV
    <2>. QED BY <2>1, <2>2
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* -------------------------------------------------------------- Release  *)
LEMMA ReleaseInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, Release(w0, s0)
    PROVE  Inv'
<1> DEFINE tb == bnd[w0][s0]
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. act[w0] /\ ~frz[w0] /\ tb \in Tids /\ DeathProof(tb) BY DEF Release
<1>post. /\ gen'  = [gen  EXCEPT ![w0][s0] = @ + 1]
         /\ bnd'  = [bnd  EXCEPT ![w0][s0] = NoTid]
         /\ abst' = [abst EXCEPT ![w0][s0] = FALSE]
         /\ ld'   = [ld   EXCEPT ![w0][s0] = @ \cup {tb}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, cand, lg, fr, sb, sd, hev>>
    BY DEF Release
<1>gn. gen[w0][s0] \in Nat BY <1>i DEF TypeOK
<1>gen. \A w \in Honest, s \in Sigils :
          gen'[w][s] = IF w = w0 /\ s = s0 THEN gen[w0][s0] + 1 ELSE gen[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>bnd. \A w \in Honest, s \in Sigils : bnd'[w][s] = IF w = w0 /\ s = s0 THEN NoTid ELSE bnd[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>abst. \A w \in Honest, s \in Sigils : abst'[w][s] = IF w = w0 /\ s = s0 THEN FALSE ELSE abst[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>ld. \A w \in Honest, s \in Sigils : ld'[w][s] = IF w = w0 /\ s = s0 THEN ld[w][s] \cup {tb} ELSE ld[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>post DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>post DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>post DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>post DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>post DEF Sealed
<1>ndc. tb # Contested BY <1>a, ContestedFresh
<1>T. TypeOK'
    <2>1. gen' \in [Honest -> [Sigils -> Nat]] BY <1>i, <1>post, <1>gn DEF TypeOK
    <2>2. bnd' \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]] BY <1>i, <1>post DEF TypeOK
    <2>3. abst' \in [Honest -> [Sigils -> BOOLEAN]] BY <1>i, <1>post DEF TypeOK
    <2>4. ld' \in [Honest -> [Sigils -> SUBSET Tids]] BY <1>i, <1>post, <1>a DEF TypeOK
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape' BY <1>i, <1>post DEF VotesShape
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], bnd'[w][s] = Contested
                 PROVE  \A g \in Nat, t \in Tids : ~HV(kv[w], w, s, g, t)'
        BY DEF ContestedSilent
    <2>1. ~(w = w0 /\ s = s0) BY <1>bnd, ContestedFresh
    <2>. QED BY <2>1, <1>bnd, <1>hv, <1>i, <1>post DEF ContestedSilent
<1>AB. AbstBound'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], abst'[w][s]
                 PROVE  bnd'[w][s] \in Tids
        BY DEF AbstBound
    <2>1. ~(w = w0 /\ s = s0) BY <1>abst
    <2>. QED BY <2>1, <1>abst, <1>bnd, <1>i, <1>post DEF AbstBound
<1>OV. OldVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, act'[w], HV(v, w, s, g, t)', v < kv'[w]
                 PROVE  \/ bnd'[w][s] = Contested
                        \/ g < gen'[w][s]
                        \/ g = gen'[w][s] /\ bnd'[w][s] \in Tids /\ (bnd'[w][s] = t \/ abst'[w][s])
        BY DEF OldVotes
    <2>0. HV(v, w, s, g, t) /\ act[w] /\ v < kv[w] BY <1>hv, <1>post
    <2>1. CASE w = w0 /\ s = s0
        <3>1. \/ bnd[w0][s0] = Contested
              \/ g < gen[w0][s0]
              \/ g = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ (bnd[w0][s0] = t \/ abst[w0][s0])
            BY <2>0, <2>1, <1>i DEF OldVotes
        <3>2. g <= gen[w0][s0] BY <3>1, <1>ndc, <1>gn
        <3>. QED BY <3>2, <2>1, <1>gen, <1>gn
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>0, <2>2, <1>gen, <1>bnd, <1>abst, <1>i DEF OldVotes
    <2>. QED BY <2>1, <2>2
<1>CV. CurVote'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  \/ g < gen'[w][s] /\ DeathProof(t)'
                        \/ g = gen'[w][s] /\ bnd'[w][s] = t
        BY DEF CurVote
    <2>0. act[w] /\ HV(kv[w], w, s, g, t) BY <1>hv, <1>post
    <2>1. \/ g < gen[w][s] /\ DeathProof(t)
          \/ g = gen[w][s] /\ bnd[w][s] = t
        BY <2>0, <1>i DEF CurVote
    <2>2. CASE w = w0 /\ s = s0
        <3>1. g <= gen[w0][s0] /\ DeathProof(t) BY <2>1, <2>2, <1>a, <1>gn
        <3>. QED BY <3>1, <2>2, <1>gen, <1>gn, <1>dp
    <2>3. CASE ~(w = w0 /\ s = s0) BY <2>1, <2>3, <1>gen, <1>bnd, <1>dp
    <2>. QED BY <2>2, <2>3
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW b \in lg'[w][s]
                 PROVE  \/ DeathProof(b[2])' /\ b[1] < gen'[w][s]
                        \/ b[1] = gen'[w][s] /\ bnd'[w][s] = b[2]
                        \/ bnd'[w][s] = Contested /\ b \in cand'[w][s] /\ b[1] <= gen'[w][s]
                        \/ /\ b[1] = gen'[w][s] /\ bnd'[w][s] \in Tids /\ DeathProof(b[2])'
                           /\ NSealed(s, gen[w][s], bnd[w][s])'
        BY DEF LogOK
    <2>0. b \in lg[w][s] /\ act[w] BY <1>post
    <2>t. b[1] \in Nat /\ b[2] \in Tids BY <2>0, <1>i DEF TypeOK
    <2>1. CASE w = w0 /\ s = s0
        <3>1. \/ DeathProof(b[2]) /\ b[1] < gen[w0][s0]
              \/ b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
              \/ bnd[w0][s0] = Contested /\ b \in cand[w0][s0] /\ b[1] <= gen[w0][s0]
              \/ /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
            BY <2>0, <2>1, <1>i DEF LogOK
        <3>2. DeathProof(b[2]) /\ b[1] <= gen[w0][s0] BY <3>1, <2>t, <1>a, <1>ndc, <1>gn
        <3>. QED BY <3>2, <2>t, <2>1, <1>gen, <1>gn, <1>dp
    <2>2. CASE ~(w = w0 /\ s = s0)
        <3>1. \/ DeathProof(b[2]) /\ b[1] < gen[w][s]
              \/ b[1] = gen[w][s] /\ bnd[w][s] = b[2]
              \/ bnd[w][s] = Contested /\ b \in cand[w][s] /\ b[1] <= gen[w][s]
              \/ /\ b[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s, gen[w][s], bnd[w][s])
            BY <2>0, <1>i DEF LogOK
        <3>2. gen'[w][s] = gen[w][s] /\ bnd'[w][s] = bnd[w][s] /\ cand'[w][s] = cand[w][s]
            BY <2>2, <1>gen, <1>bnd, <1>post
        <3>. QED BY <3>1, <3>2, <1>dp, <1>ns
    <2>. QED BY <2>1, <2>2
<1>LD. LogDead'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW t \in ld'[w][s]
                 PROVE  DeathProof(t)'
        BY DEF LogDead
    <2>1. CASE w = w0 /\ s = s0 /\ t = tb BY <2>1, <1>dp, <1>a
    <2>2. CASE t \in ld[w][s] BY <2>2, <1>dp, <1>i, <1>post DEF LogDead
    <2>. QED BY <2>1, <2>2, <1>ld
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged' BY <1>i, <1>post, <1>hv DEF VoteLogged
<1>FA. FrozenAdv' BY <1>i, <1>post DEF FrozenAdv
<1>FS. FrozenStays' BY <1>i, <1>post DEF FrozenStays
<1>SV. SnapVotes' BY <1>i, <1>post, <1>hv DEF SnapVotes
<1>EL. EvLogged' BY <1>i, <1>post DEF EvLogged
<1>SE. SnapEv' BY <1>i, <1>post DEF SnapEv
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* ------------------------------------------------- contested release  *)
LEMMA ReleaseCandInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, NEW c, NEW ng, ReleaseCand(w0, s0, c, ng)
    PROVE  Inv'
<1> DEFINE rest == cand[w0][s0] \ {c}
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. /\ act[w0] /\ ~frz[w0] /\ bnd[w0][s0] = Contested /\ c \in cand[w0][s0]
      /\ DeathProof(c[2]) /\ ng \in Nat
    BY DEF ReleaseCand
<1>ok. /\ ng >= gen[w0][s0] /\ ng > c[1]
       /\ rest = {} => \A o \in Own(w0, s0) : o[1] < ng
    BY DEF ReleaseCand, CandGenOK
<1>post. /\ gen'  = [gen  EXCEPT ![w0][s0] = ng]
         /\ cand' = [cand EXCEPT ![w0][s0] = @ \ {c}]
         /\ bnd'  = [bnd  EXCEPT ![w0][s0] = IF rest = {} THEN NoTid ELSE Contested]
         /\ ld'   = [ld   EXCEPT ![w0][s0] = @ \cup {c[2]}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, abst, lg, fr, sb, sd, hev>>
    BY DEF ReleaseCand
<1>c. c \in Nat \X Tids BY <1>a, <1>i DEF TypeOK
<1>gn. gen[w0][s0] \in Nat BY <1>i DEF TypeOK
<1>gen. \A w \in Honest, s \in Sigils : gen'[w][s] = IF w = w0 /\ s = s0 THEN ng ELSE gen[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>bnd. \A w \in Honest, s \in Sigils :
          bnd'[w][s] = IF w = w0 /\ s = s0 THEN (IF rest = {} THEN NoTid ELSE Contested) ELSE bnd[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>cand. \A w \in Honest, s \in Sigils : cand'[w][s] = IF w = w0 /\ s = s0 THEN rest ELSE cand[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>ld. \A w \in Honest, s \in Sigils :
         ld'[w][s] = IF w = w0 /\ s = s0 THEN ld[w][s] \cup {c[2]} ELSE ld[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>post DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>post DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>post DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>post DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>post DEF Sealed
<1>na. ~abst[w0][s0] BY <1>a, <1>i, ContestedFresh DEF AbstBound
<1>T. TypeOK'
    <2>1. gen' \in [Honest -> [Sigils -> Nat]] BY <1>i, <1>post, <1>a DEF TypeOK
    <2>2. bnd' \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]] BY <1>i, <1>post DEF TypeOK
    <2>3. cand' \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]] BY <1>i, <1>post DEF TypeOK
    <2>4. ld' \in [Honest -> [Sigils -> SUBSET Tids]] BY <1>i, <1>post, <1>c DEF TypeOK
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape' BY <1>i, <1>post DEF VotesShape
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], bnd'[w][s] = Contested
                 PROVE  \A g \in Nat, t \in Tids : ~HV(kv[w], w, s, g, t)'
        BY DEF ContestedSilent
    <2>1. CASE w = w0 /\ s = s0 BY <2>1, <1>a, <1>hv, <1>i, <1>post DEF ContestedSilent
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>2, <1>bnd, <1>hv, <1>i, <1>post DEF ContestedSilent
    <2>. QED BY <2>1, <2>2
<1>AB. AbstBound'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], abst'[w][s]
                 PROVE  bnd'[w][s] \in Tids
        BY DEF AbstBound
    <2>1. ~(w = w0 /\ s = s0) BY <1>na, <1>post
    <2>. QED BY <2>1, <1>bnd, <1>i, <1>post DEF AbstBound
<1>OV. OldVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, act'[w], HV(v, w, s, g, t)', v < kv'[w]
                 PROVE  \/ bnd'[w][s] = Contested
                        \/ g < gen'[w][s]
                        \/ g = gen'[w][s] /\ bnd'[w][s] \in Tids /\ (bnd'[w][s] = t \/ abst'[w][s])
        BY DEF OldVotes
    <2>0. HV(v, w, s, g, t) /\ act[w] /\ v < kv[w] BY <1>hv, <1>post
    <2>1. CASE w = w0 /\ s = s0 /\ rest # {} BY <2>1, <1>bnd
    <2>2. CASE w = w0 /\ s = s0 /\ rest = {}
        <3>1. <<g, t>> \in Own(w0, s0) BY <2>0, <2>2, OwnHV DEF HV
        <3>2. g < ng BY <3>1, <2>2, <1>ok
        <3>. QED BY <3>2, <2>2, <1>gen
    <2>3. CASE ~(w = w0 /\ s = s0) BY <2>0, <2>3, <1>gen, <1>bnd, <1>i, <1>post DEF OldVotes
    <2>. QED BY <2>1, <2>2, <2>3
<1>CV. CurVote'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  \/ g < gen'[w][s] /\ DeathProof(t)'
                        \/ g = gen'[w][s] /\ bnd'[w][s] = t
        BY DEF CurVote
    <2>0. act[w] /\ HV(kv[w], w, s, g, t) BY <1>hv, <1>post
    <2>1. ~(w = w0 /\ s = s0) BY <2>0, <1>a, <1>i DEF ContestedSilent
    <2>2. \/ g < gen[w][s] /\ DeathProof(t)
          \/ g = gen[w][s] /\ bnd[w][s] = t
        BY <2>0, <1>i DEF CurVote
    <2>. QED BY <2>1, <2>2, <1>gen, <1>bnd, <1>dp
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW b \in lg'[w][s]
                 PROVE  \/ DeathProof(b[2])' /\ b[1] < gen'[w][s]
                        \/ b[1] = gen'[w][s] /\ bnd'[w][s] = b[2]
                        \/ bnd'[w][s] = Contested /\ b \in cand'[w][s] /\ b[1] <= gen'[w][s]
                        \/ /\ b[1] = gen'[w][s] /\ bnd'[w][s] \in Tids /\ DeathProof(b[2])'
                           /\ NSealed(s, gen[w][s], bnd[w][s])'
        BY DEF LogOK
    <2>0. b \in lg[w][s] /\ act[w] BY <1>post
    <2>t. b[1] \in Nat /\ b[2] \in Tids BY <2>0, <1>i DEF TypeOK
    <2>1. CASE w = w0 /\ s = s0
        <3>1. \/ DeathProof(b[2]) /\ b[1] < gen[w0][s0]
              \/ b[1] = gen[w0][s0] /\ bnd[w0][s0] = b[2]
              \/ bnd[w0][s0] = Contested /\ b \in cand[w0][s0] /\ b[1] <= gen[w0][s0]
              \/ /\ b[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
            BY <2>0, <2>1, <1>i DEF LogOK
        <3>2. CASE DeathProof(b[2]) /\ b[1] < gen[w0][s0]
            BY <3>2, <2>t, <2>1, <1>gen, <1>gn, <1>ok, <1>a, <1>dp
        <3>3. CASE bnd[w0][s0] = Contested /\ b \in cand[w0][s0] /\ b[1] <= gen[w0][s0]
            <4>1. CASE b = c BY <4>1, <2>1, <1>a, <1>ok, <1>gen, <1>dp, <1>c
            <4>2. CASE b # c
                <5>1. b \in rest BY <4>2, <3>3
                <5>2. rest # {} BY <5>1
                <5>. QED BY <5>1, <5>2, <3>3, <2>1, <2>t, <1>gen, <1>bnd, <1>cand, <1>ok, <1>a, <1>gn
            <4>. QED BY <4>1, <4>2
        <3>. QED BY <3>1, <3>2, <3>3, <2>t, <1>a, ContestedFresh
    <2>2. CASE ~(w = w0 /\ s = s0)
        <3>1. \/ DeathProof(b[2]) /\ b[1] < gen[w][s]
              \/ b[1] = gen[w][s] /\ bnd[w][s] = b[2]
              \/ bnd[w][s] = Contested /\ b \in cand[w][s] /\ b[1] <= gen[w][s]
              \/ /\ b[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s, gen[w][s], bnd[w][s])
            BY <2>0, <1>i DEF LogOK
        <3>2. gen'[w][s] = gen[w][s] /\ bnd'[w][s] = bnd[w][s] /\ cand'[w][s] = cand[w][s]
            BY <2>2, <1>gen, <1>bnd, <1>cand
        <3>. QED BY <3>1, <3>2, <1>dp, <1>ns
    <2>. QED BY <2>1, <2>2
<1>LD. LogDead'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW t \in ld'[w][s]
                 PROVE  DeathProof(t)'
        BY DEF LogDead
    <2>1. CASE w = w0 /\ s = s0 /\ t = c[2] BY <2>1, <1>dp, <1>a
    <2>2. CASE t \in ld[w][s] BY <2>2, <1>dp, <1>i, <1>post DEF LogDead
    <2>. QED BY <2>1, <2>2, <1>ld
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged' BY <1>i, <1>post, <1>hv DEF VoteLogged
<1>FA. FrozenAdv' BY <1>i, <1>post DEF FrozenAdv
<1>FS. FrozenStays' BY <1>i, <1>post DEF FrozenStays
<1>SV. SnapVotes' BY <1>i, <1>post, <1>hv DEF SnapVotes
<1>EL. EvLogged' BY <1>i, <1>post DEF EvLogged
<1>SE. SnapEv' BY <1>i, <1>post DEF SnapEv
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* ------------------------------------- W9: a seal settles a contested record *)
LEMMA ResolveInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, NEW b, ResolveContested(w0, s0, b)
    PROVE  Inv'
<1> DEFINE others == cand[w0][s0] \ {b}
           ab == \E o \in Own(w0, s0) : o[1] = b[1] /\ o[2] # b[2]
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. /\ act[w0] /\ ~frz[w0] /\ bnd[w0][s0] = Contested /\ b \in cand[w0][s0]
      /\ Sealed(s0, b[1], b[2])
      /\ \A c \in others : DeathProof(c[2]) /\ c[1] <= b[1]
      /\ gen[w0][s0] <= b[1] + 1
      /\ \A o \in Own(w0, s0) : o[1] <= b[1]
    BY DEF ResolveContested, ResolveTop, ResolveOK
<1>post. /\ gen'  = [gen  EXCEPT ![w0][s0] = b[1]]
         /\ bnd'  = [bnd  EXCEPT ![w0][s0] = b[2]]
         /\ cand' = [cand EXCEPT ![w0][s0] = {}]
         /\ abst' = [abst EXCEPT ![w0][s0] = ab]
         /\ ld'   = [ld   EXCEPT ![w0][s0] = @ \cup { c[2] : c \in others }]
         /\ UNCHANGED <<votes, act, kv, adv, frz, lg, fr, sb, sd, hev>>
    BY DEF ResolveContested
<1>b. b \in Nat \X Tids /\ b[1] \in Nat /\ b[2] \in Tids BY <1>a, <1>i DEF TypeOK
<1>gn. gen[w0][s0] \in Nat BY <1>i DEF TypeOK
<1>oth. others \subseteq Nat \X Tids BY <1>i DEF TypeOK
<1>gen. \A w \in Honest, s \in Sigils : gen'[w][s] = IF w = w0 /\ s = s0 THEN b[1] ELSE gen[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>bnd. \A w \in Honest, s \in Sigils : bnd'[w][s] = IF w = w0 /\ s = s0 THEN b[2] ELSE bnd[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>cand. \A w \in Honest, s \in Sigils : cand'[w][s] = IF w = w0 /\ s = s0 THEN {} ELSE cand[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>abst. \A w \in Honest, s \in Sigils : abst'[w][s] = IF w = w0 /\ s = s0 THEN ab ELSE abst[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>ld. \A w \in Honest, s \in Sigils :
         ld'[w][s] = IF w = w0 /\ s = s0 THEN ld[w][s] \cup { c[2] : c \in others } ELSE ld[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>post DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>post DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>post DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>post DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>post DEF Sealed
<1>nsb. NSealed(s0, b[1], b[2]) BY <1>a, <1>b, <1>i DEF SealedNormal
<1>T. TypeOK'
    <2>1. gen' \in [Honest -> [Sigils -> Nat]] BY <1>i, <1>post, <1>b DEF TypeOK
    <2>2. bnd' \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]] BY <1>i, <1>post, <1>b DEF TypeOK
    <2>3. cand' \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]] BY <1>i, <1>post DEF TypeOK
    <2>4. abst' \in [Honest -> [Sigils -> BOOLEAN]] BY <1>i, <1>post DEF TypeOK
    <2>5. { c[2] : c \in others } \subseteq Tids BY <1>oth
    <2>6. ld' \in [Honest -> [Sigils -> SUBSET Tids]] BY <2>5, <1>i, <1>post DEF TypeOK
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>6, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape' BY <1>i, <1>post DEF VotesShape
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], bnd'[w][s] = Contested
                 PROVE  \A g \in Nat, t \in Tids : ~HV(kv[w], w, s, g, t)'
        BY DEF ContestedSilent
    <2>1. ~(w = w0 /\ s = s0) BY <1>bnd, <1>b, ContestedFresh
    <2>. QED BY <2>1, <1>bnd, <1>hv, <1>i, <1>post DEF ContestedSilent
<1>AB. AbstBound'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], abst'[w][s]
                 PROVE  bnd'[w][s] \in Tids
        BY DEF AbstBound
    <2>1. CASE w = w0 /\ s = s0 BY <2>1, <1>bnd, <1>b
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>2, <1>abst, <1>bnd, <1>i, <1>post DEF AbstBound
    <2>. QED BY <2>1, <2>2
<1>OV. OldVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, act'[w], HV(v, w, s, g, t)', v < kv'[w]
                 PROVE  \/ bnd'[w][s] = Contested
                        \/ g < gen'[w][s]
                        \/ g = gen'[w][s] /\ bnd'[w][s] \in Tids /\ (bnd'[w][s] = t \/ abst'[w][s])
        BY DEF OldVotes
    <2>0. HV(v, w, s, g, t) /\ act[w] /\ v < kv[w] BY <1>hv, <1>post
    <2>1. CASE w = w0 /\ s = s0
        <3>1. <<g, t>> \in Own(w0, s0) BY <2>0, <2>1, OwnHV DEF HV
        <3>2. g <= b[1] BY <3>1, <1>a
        <3>3. CASE g < b[1] BY <3>3, <2>1, <1>gen
        <3>4. CASE g = b[1] /\ t = b[2] BY <3>4, <2>1, <1>gen, <1>bnd, <1>b
        <3>5. CASE g = b[1] /\ t # b[2]
            <4>1. ab BY <3>1, <3>5
            <4>. QED BY <4>1, <3>5, <2>1, <1>gen, <1>bnd, <1>abst, <1>b
        <3>. QED BY <3>2, <3>3, <3>4, <3>5, <1>b
    <2>2. CASE ~(w = w0 /\ s = s0) BY <2>0, <2>2, <1>gen, <1>bnd, <1>abst, <1>i DEF OldVotes
    <2>. QED BY <2>1, <2>2
<1>CV. CurVote'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  \/ g < gen'[w][s] /\ DeathProof(t)'
                        \/ g = gen'[w][s] /\ bnd'[w][s] = t
        BY DEF CurVote
    <2>0. act[w] /\ HV(kv[w], w, s, g, t) BY <1>hv, <1>post
    <2>1. ~(w = w0 /\ s = s0) BY <2>0, <1>a, <1>i DEF ContestedSilent
    <2>2. \/ g < gen[w][s] /\ DeathProof(t)
          \/ g = gen[w][s] /\ bnd[w][s] = t
        BY <2>0, <1>i DEF CurVote
    <2>. QED BY <2>1, <2>2, <1>gen, <1>bnd, <1>dp
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW b2 \in lg'[w][s]
                 PROVE  \/ DeathProof(b2[2])' /\ b2[1] < gen'[w][s]
                        \/ b2[1] = gen'[w][s] /\ bnd'[w][s] = b2[2]
                        \/ bnd'[w][s] = Contested /\ b2 \in cand'[w][s] /\ b2[1] <= gen'[w][s]
                        \/ /\ b2[1] = gen'[w][s] /\ bnd'[w][s] \in Tids /\ DeathProof(b2[2])'
                           /\ NSealed(s, gen[w][s], bnd[w][s])'
        BY DEF LogOK
    <2>0. b2 \in lg[w][s] /\ act[w] BY <1>post
    <2>t. b2[1] \in Nat /\ b2[2] \in Tids /\ b2 = <<b2[1], b2[2]>> BY <2>0, <1>i DEF TypeOK
    <2>1. CASE w = w0 /\ s = s0
        <3>g. gen'[w0][s0] = b[1] /\ bnd'[w0][s0] = b[2] BY <1>gen, <1>bnd
        <3>n. NSealed(s0, gen[w0][s0], bnd[w0][s0])' = NSealed(s0, b[1], b[2])'
            BY <3>g
        <3>1. \/ DeathProof(b2[2]) /\ b2[1] < gen[w0][s0]
              \/ b2[1] = gen[w0][s0] /\ bnd[w0][s0] = b2[2]
              \/ bnd[w0][s0] = Contested /\ b2 \in cand[w0][s0] /\ b2[1] <= gen[w0][s0]
              \/ /\ b2[1] = gen[w0][s0] /\ bnd[w0][s0] \in Tids /\ DeathProof(b2[2])
                 /\ NSealed(s0, gen[w0][s0], bnd[w0][s0])
            BY <2>0, <2>1, <1>i DEF LogOK
        (* Every logged bind other than b is dead and at most at b's generation. *)
        <3>2. b2 = b \/ (DeathProof(b2[2]) /\ b2[1] <= b[1])
            <4>1. CASE DeathProof(b2[2]) /\ b2[1] < gen[w0][s0]
                BY <4>1, <2>t, <1>a, <1>b, <1>gn
            <4>2. CASE bnd[w0][s0] = Contested /\ b2 \in cand[w0][s0] /\ b2[1] <= gen[w0][s0]
                BY <4>2, <1>a
            <4>. QED BY <3>1, <4>1, <4>2, <1>a, <2>t, ContestedFresh
        <3>3. CASE b2 = b BY <3>3, <3>g, <2>1
        <3>4. CASE b2 # b /\ b2[1] < b[1] BY <3>2, <3>4, <3>g, <1>dp, <2>1
        <3>5. CASE b2 # b /\ b2[1] = b[1]
            <4>1. DeathProof(b2[2]) BY <3>2, <3>5
            <4>2. b2[2] # b[2] BY <3>5, <2>t, <1>b
            <4>3. NSealed(s0, b[1], b[2])' BY <1>nsb, <1>ns
            <4>. QED BY <3>5, <4>1, <4>2, <4>3, <3>g, <3>n, <1>dp, <1>b, <2>1
        <3>. QED BY <3>2, <3>3, <3>4, <3>5, <2>t, <1>b
    <2>2. CASE ~(w = w0 /\ s = s0)
        <3>1. \/ DeathProof(b2[2]) /\ b2[1] < gen[w][s]
              \/ b2[1] = gen[w][s] /\ bnd[w][s] = b2[2]
              \/ bnd[w][s] = Contested /\ b2 \in cand[w][s] /\ b2[1] <= gen[w][s]
              \/ /\ b2[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b2[2])
                 /\ NSealed(s, gen[w][s], bnd[w][s])
            BY <2>0, <1>i DEF LogOK
        <3>2. gen'[w][s] = gen[w][s] /\ bnd'[w][s] = bnd[w][s] /\ cand'[w][s] = cand[w][s]
            BY <2>2, <1>gen, <1>bnd, <1>cand
        <3>. QED BY <3>1, <3>2, <1>dp, <1>ns
    <2>. QED BY <2>1, <2>2
<1>LD. LogDead'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW t \in ld'[w][s]
                 PROVE  DeathProof(t)'
        BY DEF LogDead
    <2>1. CASE w = w0 /\ s = s0 /\ t \in { c[2] : c \in others } BY <2>1, <1>dp, <1>a
    <2>2. CASE t \in ld[w][s] BY <2>2, <1>dp, <1>i, <1>post DEF LogDead
    <2>. QED BY <2>1, <2>2, <1>ld
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged' BY <1>i, <1>post, <1>hv DEF VoteLogged
<1>FA. FrozenAdv' BY <1>i, <1>post DEF FrozenAdv
<1>FS. FrozenStays' BY <1>i, <1>post DEF FrozenStays
<1>SV. SnapVotes' BY <1>i, <1>post, <1>hv DEF SnapVotes
<1>EL. EvLogged' BY <1>i, <1>post DEF EvLogged
<1>SE. SnapEv' BY <1>i, <1>post DEF SnapEv
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* --------------------------------------------------------------- Freeze  *)
LEMMA FreezeInv ==
    ASSUME Inv, NEW w0 \in Honest, Freeze(w0)
    PROVE  Inv'
<1> DEFINE v0 == kv[w0]
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. act[w0] /\ ~frz[w0] BY DEF Freeze
<1>post. /\ frz' = [frz EXCEPT ![w0] = TRUE]
         /\ fr'  = [fr  EXCEPT ![v0] = @ \cup {w0}]
         /\ sb'  = [sb  EXCEPT ![v0][w0] = lg[w0]]
         /\ sd'  = [sd  EXCEPT ![v0][w0] = ld[w0]]
         /\ UNCHANGED <<votes, act, kv, adv, gen, bnd, cand, abst, lg, ld, hev>>
    BY DEF Freeze
<1>v0. v0 \in Vers /\ v0 \in adv[w0] BY <1>a, <1>i DEF TypeOK, AdvShape
<1>nf. w0 \notin fr[v0] BY <1>a, <1>i DEF FrozenStays
<1>fr. \A v \in Vers : fr'[v] = IF v = v0 THEN fr[v] \cup {w0} ELSE fr[v]
    BY <1>i, <1>post, <1>v0 DEF TypeOK
<1>sb. \A v \in Vers, h \in Honest : sb'[v][h] = IF v = v0 /\ h = w0 THEN lg[w0] ELSE sb[v][h]
    BY <1>i, <1>post, <1>v0 DEF TypeOK
<1>sd. \A v \in Vers, h \in Honest : sd'[v][h] = IF v = v0 /\ h = w0 THEN ld[w0] ELSE sd[v][h]
    BY <1>i, <1>post, <1>v0 DEF TypeOK
<1>frz. \A w \in Honest : frz'[w] = IF w = w0 THEN TRUE ELSE frz[w] BY <1>i, <1>post DEF TypeOK
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>post DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>post DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>post DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>post DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>post DEF Sealed
<1>T. TypeOK'
    <2>1. frz' \in [Honest -> BOOLEAN] BY <1>i, <1>post DEF TypeOK
    <2>2. fr' \in [Vers -> SUBSET Honest] BY <1>i, <1>post, <1>v0 DEF TypeOK
    <2>3. sb' \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]] BY <1>i, <1>post, <1>v0 DEF TypeOK
    <2>4. sd' \in [Vers -> [Honest -> [Sigils -> SUBSET Tids]]] BY <1>i, <1>post, <1>v0 DEF TypeOK
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape' BY <1>i, <1>post DEF VotesShape
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent' BY <1>i, <1>post, <1>hv DEF ContestedSilent
<1>AB. AbstBound' BY <1>i, <1>post DEF AbstBound
<1>OV. OldVotes' BY <1>i, <1>post, <1>hv DEF OldVotes
<1>CV. CurVote' BY <1>i, <1>post, <1>hv, <1>dp DEF CurVote
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK' BY <1>i, <1>post, <1>dp, <1>ns DEF LogOK
<1>LD. LogDead' BY <1>i, <1>post, <1>dp DEF LogDead
<1>SD. SnapDead'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, NEW s \in Sigils, NEW t \in sd'[v][h][s]
                 PROVE  DeathProof(t)'
        BY DEF SnapDead
    <2>1. CASE v = v0 /\ h = w0 BY <2>1, <1>sd, <1>a, <1>dp, <1>i DEF LogDead
    <2>2. CASE ~(v = v0 /\ h = w0) BY <2>2, <1>sd, <1>dp, <1>i DEF SnapDead
    <2>. QED BY <2>1, <2>2
<1>VL. VoteLogged' BY <1>i, <1>post, <1>hv DEF VoteLogged
<1>FA. FrozenAdv'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, h \in fr'[v] PROVE v \in adv'[h]
        BY DEF FrozenAdv
    <2>1. CASE v = v0 /\ h = w0 BY <2>1, <1>v0, <1>post
    <2>2. CASE ~(v = v0 /\ h = w0) BY <2>2, <1>fr, <1>i, <1>post DEF FrozenAdv
    <2>. QED BY <2>1, <2>2
<1>FS. FrozenStays'
    <2> SUFFICES ASSUME NEW w \in Honest, act'[w], w \in fr'[kv'[w]] PROVE frz'[w]
        BY DEF FrozenStays
    <2>1. CASE w = w0 BY <2>1, <1>frz
    <2>2. CASE w # w0
        <3>1. kv[w] \in Vers BY <1>i DEF TypeOK
        <3>2. w \in fr[kv[w]] BY <2>2, <3>1, <1>fr, <1>post
        <3>. QED BY <3>2, <2>2, <1>frz, <1>i, <1>post DEF FrozenStays
    <2>. QED BY <2>1, <2>2
<1>SV. SnapVotes'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, NEW s \in Sigils, NEW g \in Nat,
                        NEW t \in Tids, h \in fr'[v], HV(v, h, s, g, t)'
                 PROVE  <<g, t>> \in sb'[v][h][s]
        BY DEF SnapVotes
    <2>0. HV(v, h, s, g, t) BY <1>hv
    <2>1. CASE v = v0 /\ h = w0
        <3>1. <<g, t>> \in lg[w0][s] BY <2>0, <2>1, <1>a, <1>i DEF VoteLogged
        <3>. QED BY <3>1, <2>1, <1>sb
    <2>2. CASE ~(v = v0 /\ h = w0)
        <3>1. h \in fr[v] BY <2>2, <1>fr
        <3>. QED BY <3>1, <2>0, <2>2, <1>sb, <1>i DEF SnapVotes
    <2>. QED BY <2>1, <2>2
<1>EL. EvLogged' BY <1>i, <1>post DEF EvLogged
<1>SE. SnapEv'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, NEW s \in Sigils, h \in fr'[v]
                 PROVE  hev'[v][h][s] \subseteq sb'[v][h][s]
        BY DEF SnapEv
    <2>1. CASE v = v0 /\ h = w0 BY <2>1, <1>sb, <1>a, <1>i, <1>post DEF EvLogged
    <2>2. CASE ~(v = v0 /\ h = w0)
        <3>1. h \in fr[v] BY <2>2, <1>fr
        <3>. QED BY <3>1, <2>2, <1>sb, <1>i, <1>post DEF SnapEv
    <2>. QED BY <2>1, <2>2
<1>LI. Lineage'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv'[w], v1 < v2
                 PROVE  \E F \in SUBSET Members[v1] :
                           /\ Cardinality(F) >= Quorum[v1]
                           /\ F \cap Honest \subseteq fr'[v1]
                           /\ \A h \in F \cap Honest, s \in Sigils : sb'[v1][h][s] \subseteq hev'[v2][w][s]
        BY DEF Lineage
    <2>1. PICK F \in SUBSET Members[v1] :
              /\ Cardinality(F) >= Quorum[v1]
              /\ F \cap Honest \subseteq fr[v1]
              /\ \A h \in F \cap Honest, s \in Sigils : sb[v1][h][s] \subseteq hev[v2][w][s]
        BY <1>i, <1>post DEF Lineage
    <2>2. F \cap Honest \subseteq fr'[v1] BY <2>1, <1>fr
    <2>3. \A h \in F \cap Honest : sb'[v1][h] = sb[v1][h]
        <3> SUFFICES ASSUME NEW h \in F \cap Honest PROVE sb'[v1][h] = sb[v1][h] OBVIOUS
        <3>1. h \in fr[v1] BY <2>1
        <3>2. ~(v1 = v0 /\ h = w0) BY <3>1, <1>nf
        <3>. QED BY <3>2, <1>sb
    <2>. QED BY <2>1, <2>2, <2>3, <1>post
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* ---------------------------------------------------------------- Adopt  *)
LEMMA AdoptInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW v0, NEW F0, NEW XB, NEW XD, NEW XS, NEW NG,
           Adopt(w0, v0, F0, XB, XD, XS, NG)
    PROVE  Inv'
<1> DEFINE EB(s) == EvB(v0 - 1, F0, XB, s)
           ED(s) == EvD(v0 - 1, F0, XD, s)
           O(s)  == Own(w0, s)
           R(s)  == NewRec(EB(s), ED(s), XS[s], O(s), NG[s])
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ w0 \in Members[v0]
      /\ act[w0] => kv[w0] < v0
      /\ F0 \subseteq Members[v0 - 1]
      /\ Cardinality(F0) >= Quorum[v0 - 1]
      /\ F0 \cap Honest \subseteq fr[v0 - 1]
      /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ XD \in [Sigils -> SUBSET Tids]
      /\ XS \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
      /\ \A s \in Sigils : \A b \in XS[s] : Sealed(s, b[1], b[2])
      /\ NG \in [Sigils -> Nat]
      /\ \A s \in Sigils : GenOK(EB(s), ED(s), O(s), NG[s])
    BY DEF Adopt
<1>post. /\ gen'  = [gen  EXCEPT ![w0] = [s \in Sigils |-> R(s).g]]
         /\ bnd'  = [bnd  EXCEPT ![w0] = [s \in Sigils |-> R(s).t]]
         /\ cand' = [cand EXCEPT ![w0] = [s \in Sigils |-> R(s).c]]
         /\ abst' = [abst EXCEPT ![w0] = [s \in Sigils |-> R(s).a]]
         /\ lg'   = [lg   EXCEPT ![w0] = [s \in Sigils |-> EB(s)]]
         /\ ld'   = [ld   EXCEPT ![w0] = [s \in Sigils |-> ED(s)]]
         /\ hev'  = [hev  EXCEPT ![v0][w0] = [s \in Sigils |-> EB(s)]]
         /\ act'  = [act  EXCEPT ![w0] = TRUE]
         /\ kv'   = [kv   EXCEPT ![w0] = v0]
         /\ adv'  = [adv  EXCEPT ![w0] = @ \cup {v0}]
         /\ frz'  = [frz  EXCEPT ![w0] = FALSE]
         /\ UNCHANGED <<votes, fr, sb, sd>>
    BY DEF Adopt
<1>vn. v0 \in Nat BY <1>a, VersType
<1>k1. v0 \notin adv[w0]
    <2>1. CASE act[w0] BY <2>1, <1>a, <1>i, <1>vn, VersType DEF AdvShape, TypeOK
    <2>2. CASE ~act[w0] BY <2>2, <1>i DEF AdvShape
    <2>. QED BY <2>1, <2>2
<1>k2. \A s, g, t : ~HV(v0, w0, s, g, t)
    <2> SUFFICES ASSUME NEW s, NEW g, NEW t, HV(v0, w0, s, g, t) PROVE FALSE OBVIOUS
    <2>1. v0 \in adv[w0] BY VoteFields, <1>i DEF VotesShape, HV
    <2>. QED BY <2>1, <1>k1
<1>k3. w0 \notin fr[v0] BY <1>k1, <1>a, <1>i DEF FrozenAdv
<1>k4. \A s \in Sigils : /\ EB(s) \subseteq Nat \X Tids
                         /\ ED(s) \subseteq Tids
                         /\ O(s) \subseteq Nat \X Tids
    <2> SUFFICES ASSUME NEW s \in Sigils
                 PROVE  /\ EB(s) \subseteq Nat \X Tids
                        /\ ED(s) \subseteq Tids
                        /\ O(s) \subseteq Nat \X Tids
        OBVIOUS
    <2>1. \A h \in F0 \cap Honest : sb[v0 - 1][h][s] \subseteq Nat \X Tids /\ sd[v0 - 1][h][s] \subseteq Tids
        BY <1>a, <1>i DEF TypeOK
    <2>2. EB(s) \subseteq Nat \X Tids
        <3> SUFFICES ASSUME NEW b \in EB(s) PROVE b \in Nat \X Tids OBVIOUS
        <3>1. b \in UNION { sb[v0 - 1][h][s] : h \in F0 \cap Honest } \/ b \in XB[s] BY DEF EvB
        <3>2. CASE b \in XB[s] BY <3>2, <1>a
        <3>3. CASE b \in UNION { sb[v0 - 1][h][s] : h \in F0 \cap Honest }
            <4>1. PICK h \in F0 \cap Honest : b \in sb[v0 - 1][h][s] BY <3>3
            <4>. QED BY <4>1, <2>1
        <3>. QED BY <3>1, <3>2, <3>3
    <2>3. ED(s) \subseteq Tids
        <3> SUFFICES ASSUME NEW t \in ED(s) PROVE t \in Tids OBVIOUS
        <3>1. t \in UNION { sd[v0 - 1][h][s] : h \in F0 \cap Honest } \/ t \in XD[s] BY DEF EvD
        <3>2. CASE t \in XD[s] BY <3>2, <1>a
        <3>3. CASE t \in UNION { sd[v0 - 1][h][s] : h \in F0 \cap Honest }
            <4>1. PICK h \in F0 \cap Honest : t \in sd[v0 - 1][h][s] BY <3>3
            <4>. QED BY <4>1, <2>1
        <3>. QED BY <3>1, <3>2, <3>3
    <2>4. O(s) \subseteq Nat \X Tids BY <1>i, OwnType
    <2>. QED BY <2>2, <2>3, <2>4
<1>k5. \A s \in Sigils : \A t \in ED(s) : DeathProof(t)
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW t \in ED(s) PROVE DeathProof(t) OBVIOUS
    <2>0. t \in UNION { sd[v0 - 1][h][s] : h \in F0 \cap Honest } \/ t \in XD[s] BY DEF EvD
    <2>1. CASE t \in UNION { sd[v0 - 1][h][s] : h \in F0 \cap Honest }
        <3>1. PICK h \in F0 \cap Honest : t \in sd[v0 - 1][h][s] BY <2>1
        <3>. QED BY <3>1, <1>a, <1>i DEF SnapDead
    <2>2. CASE t \in XD[s] BY <2>2, <1>a
    <2>. QED BY <2>0, <2>1, <2>2
<1>nr. \A s \in Sigils :
          /\ R(s).g \in Nat
          /\ R(s).t \in Tids \cup {NoTid, Contested}
          /\ R(s).c \in SUBSET (Nat \X Tids)
          /\ R(s).a \in BOOLEAN
          /\ R(s).a => R(s).t \in Tids
          /\ \A b \in EB(s) : \/ b[2] \in ED(s) /\ b[1] < R(s).g
                              \/ b[1] = R(s).g /\ R(s).t = b[2]
                              \/ R(s).t = Contested /\ b \in R(s).c /\ b[1] <= R(s).g
                              \/ /\ b[1] = R(s).g /\ R(s).t \in Tids /\ b[2] \in ED(s)
                                 /\ <<R(s).g, R(s).t>> \in XS[s]
          /\ \A o \in O(s) : \/ R(s).t = Contested
                             \/ o[1] < R(s).g
                             \/ o[1] = R(s).g /\ R(s).t \in Tids /\ (R(s).t = o[2] \/ R(s).a)
    <2> SUFFICES ASSUME NEW s \in Sigils
                 PROVE  /\ R(s).g \in Nat
                        /\ R(s).t \in Tids \cup {NoTid, Contested}
                        /\ R(s).c \in SUBSET (Nat \X Tids)
                        /\ R(s).a \in BOOLEAN
                        /\ R(s).a => R(s).t \in Tids
                        /\ \A b \in EB(s) : \/ b[2] \in ED(s) /\ b[1] < R(s).g
                                            \/ b[1] = R(s).g /\ R(s).t = b[2]
                                            \/ R(s).t = Contested /\ b \in R(s).c /\ b[1] <= R(s).g
                                            \/ /\ b[1] = R(s).g /\ R(s).t \in Tids /\ b[2] \in ED(s)
                                               /\ <<R(s).g, R(s).t>> \in XS[s]
                        /\ \A o \in O(s) : \/ R(s).t = Contested
                                           \/ o[1] < R(s).g
                                           \/ o[1] = R(s).g /\ R(s).t \in Tids /\ (R(s).t = o[2] \/ R(s).a)
        OBVIOUS
    <2>1. EB(s) \in SUBSET (Nat \X Tids) /\ ED(s) \in SUBSET Tids /\ O(s) \in SUBSET (Nat \X Tids)
        BY <1>k4
    <2>2. NG[s] \in Nat /\ GenOK(EB(s), ED(s), O(s), NG[s]) BY <1>a
    <2>. QED BY <2>1, <2>2, NewRecSpec
<1>gen. \A w \in Honest, s \in Sigils : gen'[w][s] = IF w = w0 THEN R(s).g ELSE gen[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>bnd. \A w \in Honest, s \in Sigils : bnd'[w][s] = IF w = w0 THEN R(s).t ELSE bnd[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>cand. \A w \in Honest, s \in Sigils : cand'[w][s] = IF w = w0 THEN R(s).c ELSE cand[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>abst. \A w \in Honest, s \in Sigils : abst'[w][s] = IF w = w0 THEN R(s).a ELSE abst[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>lg. \A w \in Honest, s \in Sigils : lg'[w][s] = IF w = w0 THEN EB(s) ELSE lg[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>ld. \A w \in Honest, s \in Sigils : ld'[w][s] = IF w = w0 THEN ED(s) ELSE ld[w][s]
    BY <1>i, <1>post DEF TypeOK
<1>hev. \A v \in Vers, w \in Honest, s \in Sigils :
           hev'[v][w][s] = IF v = v0 /\ w = w0 THEN EB(s) ELSE hev[v][w][s]
    BY <1>i, <1>post, <1>a DEF TypeOK
<1>act. \A w \in Honest : act'[w] = IF w = w0 THEN TRUE ELSE act[w] BY <1>i, <1>post DEF TypeOK
<1>kv. \A w \in Honest : kv'[w] = IF w = w0 THEN v0 ELSE kv[w] BY <1>i, <1>post DEF TypeOK
<1>adv. \A w \in Honest : adv'[w] = IF w = w0 THEN adv[w0] \cup {v0} ELSE adv[w] BY <1>i, <1>post DEF TypeOK
<1>frz. \A w \in Honest : frz'[w] = IF w = w0 THEN FALSE ELSE frz[w] BY <1>i, <1>post DEF TypeOK
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>post DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>post DEF HV
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>post DEF Sealed
(* Evidence changed only for w0 in v0, where w0 has not voted.              *)
<1>hvo. \A vv \in Vers, xx \in Honest, ss \in Sigils : \A gg, tt :
           Vote(vv, xx, ss, gg, tt) \in votes => hev'[vv][xx][ss] = hev[vv][xx][ss]
    <2> SUFFICES ASSUME NEW vv \in Vers, NEW xx \in Honest, NEW ss \in Sigils, NEW gg, NEW tt,
                        Vote(vv, xx, ss, gg, tt) \in votes
                 PROVE  hev'[vv][xx][ss] = hev[vv][xx][ss]
        OBVIOUS
    <2>1. ~(vv = v0 /\ xx = w0) BY <1>k2 DEF HV
    <2>. QED BY <2>1, <1>hev
<1>nsm. \A s \in Sigils : \A g, t : NSealed(s, g, t) => NSealed(s, g, t)'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g, NEW t, NSealed(s, g, t)
                 PROVE  NSealed(s, g, t)'
        OBVIOUS
    <2>1. votes \subseteq votes' BY <1>post
    <2>. QED BY <2>1, <1>hvo, NSealedMono DEF NSealed
<1>nmv. \A v \in Vers, w \in Honest, s \in Sigils : \A g, t :
           HV(v, w, s, g, t) => (NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t))
    <2> SUFFICES ASSUME NEW v \in Vers, NEW w \in Honest, NEW s \in Sigils, NEW g, NEW t,
                        HV(v, w, s, g, t)
                 PROVE  NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
        OBVIOUS
    <2>1. hev'[v][w][s] = hev[v][w][s] BY <1>hvo DEF HV
    <2>. QED BY <2>1, <1>post DEF NormalVote, NormalVoteV

<1>T. TypeOK'
    <2>1. gen' \in [Honest -> [Sigils -> Nat]] BY <1>i, <1>post, <1>nr DEF TypeOK
    <2>2. bnd' \in [Honest -> [Sigils -> Tids \cup {NoTid, Contested}]] BY <1>i, <1>post, <1>nr DEF TypeOK
    <2>3. cand' \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]] BY <1>i, <1>post, <1>nr DEF TypeOK
    <2>4. abst' \in [Honest -> [Sigils -> BOOLEAN]] BY <1>i, <1>post, <1>nr DEF TypeOK
    <2>5. lg' \in [Honest -> [Sigils -> SUBSET (Nat \X Tids)]] BY <1>i, <1>post, <1>k4 DEF TypeOK
    <2>6. ld' \in [Honest -> [Sigils -> SUBSET Tids]] BY <1>i, <1>post, <1>k4 DEF TypeOK
    <2>7. hev' \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]] BY <1>i, <1>post, <1>k4, <1>a DEF TypeOK
    <2>8. /\ act' \in [Honest -> BOOLEAN]
          /\ kv' \in [Honest -> Vers]
          /\ adv' \in [Honest -> SUBSET Vers]
          /\ frz' \in [Honest -> BOOLEAN]
        BY <1>i, <1>post, <1>a DEF TypeOK
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape'
    <2> SUFFICES ASSUME NEW x \in votes', x.wit \in Honest
                 PROVE  act'[x.wit] /\ x.ver \in adv'[x.wit] /\ x.wit \in Members[x.ver]
        BY DEF VotesShape
    <2>1. x \in votes BY <1>post
    <2>2. act[x.wit] /\ x.ver \in adv[x.wit] /\ x.wit \in Members[x.ver] BY <2>1, <1>i DEF VotesShape
    <2>. QED BY <2>2, <1>act, <1>adv
<1>AS. AdvShape'
    <2> SUFFICES ASSUME NEW w \in Honest
                 PROVE  /\ act'[w] => /\ kv'[w] \in adv'[w]
                                      /\ \A v \in adv'[w] : v <= kv'[w]
                                      /\ w \in Members[kv'[w]]
                        /\ ~act'[w] => adv'[w] = {}
        BY DEF AdvShape
    <2>1. CASE w = w0
        <3>1. \A v \in adv[w0] : v <= v0
            <4>1. CASE act[w0] BY <4>1, <1>a, <1>i, VersType DEF AdvShape, TypeOK
            <4>2. CASE ~act[w0] BY <4>2, <1>i DEF AdvShape
            <4>. QED BY <4>1, <4>2
        <3>. QED BY <2>1, <3>1, <1>act, <1>kv, <1>adv, <1>a, <1>vn
    <2>2. CASE w # w0 BY <2>2, <1>act, <1>kv, <1>adv, <1>i DEF AdvShape
    <2>. QED BY <2>1, <2>2
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], bnd'[w][s] = Contested
                 PROVE  \A g \in Nat, t \in Tids : ~HV(kv[w], w, s, g, t)'
        BY DEF ContestedSilent
    <2>1. CASE w = w0 BY <2>1, <1>kv, <1>hv, <1>k2
    <2>2. CASE w # w0 BY <2>2, <1>act, <1>kv, <1>bnd, <1>hv, <1>i DEF ContestedSilent
    <2>. QED BY <2>1, <2>2
<1>AB. AbstBound'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], abst'[w][s]
                 PROVE  bnd'[w][s] \in Tids
        BY DEF AbstBound
    <2>1. CASE w = w0 BY <2>1, <1>abst, <1>bnd, <1>nr
    <2>2. CASE w # w0 BY <2>2, <1>act, <1>abst, <1>bnd, <1>i DEF AbstBound
    <2>. QED BY <2>1, <2>2
<1>OV. OldVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, act'[w], HV(v, w, s, g, t)', v < kv'[w]
                 PROVE  \/ bnd'[w][s] = Contested
                        \/ g < gen'[w][s]
                        \/ g = gen'[w][s] /\ bnd'[w][s] \in Tids /\ (bnd'[w][s] = t \/ abst'[w][s])
        BY DEF OldVotes
    <2>0. HV(v, w, s, g, t) BY <1>hv
    <2>1. CASE w = w0
        <3>1. <<g, t>> \in O(s) BY <2>0, <2>1, OwnHV DEF HV
        <3>2. \/ R(s).t = Contested
              \/ <<g, t>>[1] < R(s).g
              \/ <<g, t>>[1] = R(s).g /\ R(s).t \in Tids /\ (R(s).t = <<g, t>>[2] \/ R(s).a)
            BY <3>1, <1>nr
        <3>. QED BY <3>2, <2>1, <1>gen, <1>bnd, <1>abst
    <2>2. CASE w # w0 BY <2>0, <2>2, <1>act, <1>kv, <1>gen, <1>bnd, <1>abst, <1>i DEF OldVotes
    <2>. QED BY <2>1, <2>2
<1>CV. CurVote'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  \/ g < gen'[w][s] /\ DeathProof(t)'
                        \/ g = gen'[w][s] /\ bnd'[w][s] = t
        BY DEF CurVote
    <2>1. CASE w = w0 BY <2>1, <1>kv, <1>hv, <1>k2
    <2>2. CASE w # w0
        <3>1. act[w] /\ HV(kv[w], w, s, g, t) BY <2>2, <1>act, <1>kv, <1>hv
        <3>2. \/ g < gen[w][s] /\ DeathProof(t)
              \/ g = gen[w][s] /\ bnd[w][s] = t
            BY <3>1, <1>i DEF CurVote
        <3>. QED BY <3>2, <2>2, <1>gen, <1>bnd, <1>dp
    <2>. QED BY <2>1, <2>2
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW b \in lg'[w][s]
                 PROVE  \/ DeathProof(b[2])' /\ b[1] < gen'[w][s]
                        \/ b[1] = gen'[w][s] /\ bnd'[w][s] = b[2]
                        \/ bnd'[w][s] = Contested /\ b \in cand'[w][s] /\ b[1] <= gen'[w][s]
                        \/ /\ b[1] = gen'[w][s] /\ bnd'[w][s] \in Tids /\ DeathProof(b[2])'
                           /\ NSealed(s, gen[w][s], bnd[w][s])'
        BY DEF LogOK
    <2>1. CASE w = w0
        <3>1. b \in EB(s) BY <2>1, <1>lg
        <3>2. \/ b[2] \in ED(s) /\ b[1] < R(s).g
              \/ b[1] = R(s).g /\ R(s).t = b[2]
              \/ R(s).t = Contested /\ b \in R(s).c /\ b[1] <= R(s).g
              \/ /\ b[1] = R(s).g /\ R(s).t \in Tids /\ b[2] \in ED(s)
                 /\ <<R(s).g, R(s).t>> \in XS[s]
            BY <3>1, <1>nr
        <3>3. b[2] \in ED(s) => DeathProof(b[2])' BY <1>k5, <1>dp
        <3>g. gen'[w0][s] = R(s).g /\ bnd'[w0][s] = R(s).t /\ cand'[w0][s] = R(s).c
            BY <1>gen, <1>bnd, <1>cand
        <3>4. CASE /\ b[1] = R(s).g /\ R(s).t \in Tids /\ b[2] \in ED(s)
                   /\ <<R(s).g, R(s).t>> \in XS[s]
            <4>1. Sealed(s, R(s).g, R(s).t) BY <3>4, <1>a
            <4>2. R(s).g \in Nat BY <1>nr
            <4>3. NSealed(s, R(s).g, R(s).t) BY <4>1, <4>2, <3>4, <1>i DEF SealedNormal
            <4>4. NSealedV(votes', hev', s, R(s).g, R(s).t) BY <4>3, <1>nsm DEF NSealed
            <4>5. NSealed(s, gen[w0][s], bnd[w0][s])' BY <4>4, <3>g DEF NSealed
            <4>. QED BY <3>4, <3>3, <3>g, <4>5, <2>1
        <3>. QED BY <3>2, <3>3, <3>4, <3>g, <2>1
    <2>2. CASE w # w0
        <3>1. b \in lg[w][s] /\ act[w] BY <2>2, <1>lg, <1>act
        <3>2. \/ DeathProof(b[2]) /\ b[1] < gen[w][s]
              \/ b[1] = gen[w][s] /\ bnd[w][s] = b[2]
              \/ bnd[w][s] = Contested /\ b \in cand[w][s] /\ b[1] <= gen[w][s]
              \/ /\ b[1] = gen[w][s] /\ bnd[w][s] \in Tids /\ DeathProof(b[2])
                 /\ NSealed(s, gen[w][s], bnd[w][s])
            BY <3>1, <1>i DEF LogOK
        <3>3. gen'[w][s] = gen[w][s] /\ bnd'[w][s] = bnd[w][s] /\ cand'[w][s] = cand[w][s]
            BY <2>2, <1>gen, <1>bnd, <1>cand
        <3>4. gen[w][s] \in Nat BY <1>i DEF TypeOK
        <3>5. NSealed(s, gen[w][s], bnd[w][s]) => NSealed(s, gen[w][s], bnd[w][s])'
            <4>1. NSealed(s, gen[w][s], bnd[w][s]) => NSealedV(votes', hev', s, gen[w][s], bnd[w][s])
                BY <1>nsm DEF NSealed
            <4>. QED BY <4>1, <3>3 DEF NSealed
        <3>. QED BY <3>2, <3>3, <3>5, <1>dp
    <2>. QED BY <2>1, <2>2
<1>LD. LogDead'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w], NEW t \in ld'[w][s]
                 PROVE  DeathProof(t)'
        BY DEF LogDead
    <2>1. CASE w = w0 BY <2>1, <1>ld, <1>k5, <1>dp
    <2>2. CASE w # w0 BY <2>2, <1>ld, <1>act, <1>dp, <1>i DEF LogDead
    <2>. QED BY <2>1, <2>2
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
                        act'[w], HV(kv[w], w, s, g, t)'
                 PROVE  <<g, t>> \in lg'[w][s]
        BY DEF VoteLogged
    <2>1. CASE w = w0 BY <2>1, <1>kv, <1>hv, <1>k2
    <2>2. CASE w # w0 BY <2>2, <1>act, <1>kv, <1>lg, <1>hv, <1>i DEF VoteLogged
    <2>. QED BY <2>1, <2>2
<1>FA. FrozenAdv'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, h \in fr'[v] PROVE v \in adv'[h]
        BY DEF FrozenAdv
    <2>1. v \in adv[h] BY <1>post, <1>i DEF FrozenAdv
    <2>. QED BY <2>1, <1>adv
<1>FS. FrozenStays'
    <2> SUFFICES ASSUME NEW w \in Honest, act'[w], w \in fr'[kv'[w]] PROVE frz'[w]
        BY DEF FrozenStays
    <2>1. CASE w = w0 BY <2>1, <1>kv, <1>post, <1>k3
    <2>2. CASE w # w0 BY <2>2, <1>act, <1>kv, <1>frz, <1>post, <1>i DEF FrozenStays
    <2>. QED BY <2>1, <2>2
<1>SV. SnapVotes' BY <1>i, <1>post, <1>hv DEF SnapVotes
<1>EL. EvLogged'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, act'[w]
                 PROVE  hev'[kv'[w]][w][s] \subseteq lg'[w][s]
        BY DEF EvLogged
    <2>1. CASE w = w0 BY <2>1, <1>kv, <1>hev, <1>lg, <1>a
    <2>2. CASE w # w0
        <3>1. kv[w] \in Vers /\ act[w] BY <2>2, <1>act, <1>i DEF TypeOK
        <3>2. hev'[kv[w]][w][s] = hev[kv[w]][w][s] BY <3>1, <2>2, <1>hev
        <3>. QED BY <3>1, <3>2, <2>2, <1>kv, <1>lg, <1>i DEF EvLogged
    <2>. QED BY <2>1, <2>2
<1>SE. SnapEv'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW h \in Honest, NEW s \in Sigils, h \in fr'[v]
                 PROVE  hev'[v][h][s] \subseteq sb'[v][h][s]
        BY DEF SnapEv
    <2>1. h \in fr[v] /\ sb'[v][h][s] = sb[v][h][s] BY <1>post
    <2>2. ~(v = v0 /\ h = w0) BY <2>1, <1>k3
    <2>. QED BY <2>1, <2>2, <1>hev, <1>i DEF SnapEv
<1>LI. Lineage'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv'[w], v1 < v2
                 PROVE  \E F \in SUBSET Members[v1] :
                           /\ Cardinality(F) >= Quorum[v1]
                           /\ F \cap Honest \subseteq fr'[v1]
                           /\ \A h \in F \cap Honest, s \in Sigils : sb'[v1][h][s] \subseteq hev'[v2][w][s]
        BY DEF Lineage
    <2>fr. fr' = fr /\ sb' = sb BY <1>post
    <2>1. CASE w = w0 /\ v2 = v0
        <3>h. \A s \in Sigils : hev'[v0][w0][s] = EB(s) BY <1>hev, <1>a
        <3>ev. \A h \in F0 \cap Honest, s \in Sigils : sb[v0 - 1][h][s] \subseteq EB(s) BY DEF EvB
        <3>vn. v1 \in Nat /\ v1 < v0 BY <2>1, VersType
        <3>1. CASE v1 = v0 - 1
            BY <3>1, <3>ev, <3>h, <2>1, <2>fr, <1>a
        <3>2. CASE v1 < v0 - 1
            <4>1. PICK h0 \in F0 : h0 \in Honest BY <1>a, QuorumHasHonest
            <4>2. h0 \in fr[v0 - 1] BY <4>1, <1>a
            <4>3. v0 - 1 \in adv[h0] BY <4>1, <4>2, <1>a, <1>i DEF FrozenAdv
            <4>4. PICK F \in SUBSET Members[v1] :
                      /\ Cardinality(F) >= Quorum[v1]
                      /\ F \cap Honest \subseteq fr[v1]
                      /\ \A h \in F \cap Honest, s \in Sigils : sb[v1][h][s] \subseteq hev[v0 - 1][h0][s]
                BY <3>2, <4>1, <4>3, <1>a, <1>i DEF Lineage
            <4>5. \A s \in Sigils : hev[v0 - 1][h0][s] \subseteq sb[v0 - 1][h0][s]
                BY <4>1, <4>2, <1>a, <1>i DEF SnapEv
            <4>6. \A s \in Sigils : sb[v0 - 1][h0][s] \subseteq EB(s) BY <4>1, <3>ev
            <4>. QED BY <4>4, <4>5, <4>6, <3>h, <2>1, <2>fr
        <3>. QED BY <3>vn, <3>1, <3>2, <1>vn
    <2>2. CASE ~(w = w0 /\ v2 = v0)
        <3>1. v2 \in adv[w] BY <2>2, <1>adv
        <3>2. \A s \in Sigils : hev'[v2][w][s] = hev[v2][w][s] BY <2>2, <1>hev
        <3>. QED BY <3>1, <3>2, <2>fr, <1>i DEF Lineage
    <2>. QED BY <2>1, <2>2
<1>VJ. VoteJust'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW s \in Sigils, NEW v \in Vers, NEW g \in Nat,
                        NEW t \in Tids, HV(v, w, s, g, t)'
                 PROVE  NormalVote(v, w, s, g, t)' \/ NSealed(s, g, t)'
        BY DEF VoteJust
    <2>1. HV(v, w, s, g, t) BY <1>hv
    <2>2. NormalVote(v, w, s, g, t) \/ NSealed(s, g, t) BY <2>1, <1>i DEF VoteJust
    <2>. QED BY <2>1, <2>2, <1>nmv, <1>nsm
<1>SN. SealedNormal'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids, Sealed(s, g, t)'
                 PROVE  NSealed(s, g, t)'
        BY DEF SealedNormal
    <2>1. NSealed(s, g, t) BY <1>sl, <1>i DEF SealedNormal
    <2>. QED BY <2>1, <1>nsm
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* ------------------------------------------------------------- ByzVote  *)
LEMMA ByzVoteInv ==
    ASSUME Inv, NEW b \in Byz, NEW v1 \in Vers, NEW s1 \in Sigils, NEW g1 \in Nat, NEW t1 \in Tids,
           ByzVote(b, v1, s1, g1, t1)
    PROVE  Inv'
<1> DEFINE bv == Vote(v1, b, s1, g1, t1)
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>post. /\ votes' = votes \cup {bv}
         /\ UNCHANGED <<act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev>>
    BY DEF ByzVote
<1>nb. b \notin Honest BY HonestByzDisjoint
<1>hv. \A v, w, s, g, t : w \in Honest => (HV(v, w, s, g, t)' <=> HV(v, w, s, g, t))
    <2> SUFFICES ASSUME NEW v, NEW w, NEW s, NEW g, NEW t, w \in Honest
                 PROVE  HV(v, w, s, g, t)' <=> HV(v, w, s, g, t)
        OBVIOUS
    <2>1. Vote(v, w, s, g, t) # bv BY <1>nb, VoteEq
    <2>. QED BY <2>1, <1>post DEF HV
<1>sub. votes \subseteq votes' BY <1>post
<1>dp. \A t : DeathProof(t) => DeathProof(t)' BY <1>sub, DeathMonotone DEF DeathProof
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t) => NormalVote(v, w, s, g, t)'
    BY <1>post, <1>dp DEF NormalVote, NormalVoteV, DeathProof
<1>nsm. \A s \in Sigils : \A g, t : NSealed(s, g, t) => NSealed(s, g, t)'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g, NEW t, NSealed(s, g, t)
                 PROVE  NSealed(s, g, t)'
        OBVIOUS
    <2>1. \A vv \in Vers, xx \in Honest, ss \in Sigils : \A gg, tt :
             Vote(vv, xx, ss, gg, tt) \in votes => hev'[vv][xx][ss] = hev[vv][xx][ss]
        BY <1>post
    <2>. QED BY <2>1, <1>sub, NSealedMono DEF NSealed
<1>T. TypeOK'
    <2>1. bv \in [ver : Vers, wit : Witnesses, sgl : Sigils, gnr : Nat, trn : Tids]
        BY DEF Vote, Witnesses
    <2>. QED BY <2>1, <1>i, <1>post DEF TypeOK
<1>VS. VotesShape'
    <2> SUFFICES ASSUME NEW x \in votes', x.wit \in Honest
                 PROVE  act'[x.wit] /\ x.ver \in adv'[x.wit] /\ x.wit \in Members[x.ver]
        BY DEF VotesShape
    <2>1. x # bv BY <1>nb, VoteFields
    <2>. QED BY <2>1, <1>i, <1>post DEF VotesShape
<1>AS. AdvShape' BY <1>i, <1>post DEF AdvShape
<1>NE. NoEquiv' BY <1>i, <1>hv DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent' BY <1>i, <1>post, <1>hv DEF ContestedSilent
<1>AB. AbstBound' BY <1>i, <1>post DEF AbstBound
<1>OV. OldVotes' BY <1>i, <1>post, <1>hv DEF OldVotes
<1>CV. CurVote' BY <1>i, <1>post, <1>hv, <1>dp DEF CurVote
<1>RD. RelDisc' BY <1>i, <1>hv, <1>dp DEF RelDisc
<1>LO. LogOK' BY <1>i, <1>post, <1>dp, <1>nsm DEF LogOK, TypeOK
<1>LD. LogDead' BY <1>i, <1>post, <1>dp DEF LogDead
<1>SD. SnapDead' BY <1>i, <1>post, <1>dp DEF SnapDead
<1>VL. VoteLogged' BY <1>i, <1>post, <1>hv DEF VoteLogged
<1>FA. FrozenAdv' BY <1>i, <1>post DEF FrozenAdv
<1>FS. FrozenStays' BY <1>i, <1>post DEF FrozenStays
<1>SV. SnapVotes' BY <1>i, <1>post, <1>hv DEF SnapVotes
<1>EL. EvLogged' BY <1>i, <1>post DEF EvLogged
<1>SE. SnapEv' BY <1>i, <1>post DEF SnapEv
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>nsm DEF VoteJust
<1>SN. SealedNormal'
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids, Sealed(s, g, t)'
                 PROVE  NSealed(s, g, t)'
        BY DEF SealedNormal
    <2>1. CASE NSealed(s, g, t) BY <2>1, <1>nsm
    <2>2. CASE ~NSealed(s, g, t)
        <3>1. PICK v \in Vers : SealedInV(votes', v, s, g, t) BY DEF Sealed, SealedV
        <3> DEFINE Q == VotersV(votes', v, s, g, t)
        <3>2. Q \subseteq Members[v] /\ Cardinality(Q) >= Quorum[v] BY <3>1 DEF VotersV, SealedInV
        <3>3. \A x \in Q : Vote(v, x, s, g, t) \in votes' BY DEF VotersV
        <3>4. \A x \in Q : x \in Honest => NormalVoteV(votes', hev', v, x, s, g, t)
            <4> SUFFICES ASSUME NEW x \in Q, x \in Honest
                         PROVE  NormalVoteV(votes', hev', v, x, s, g, t)
                OBVIOUS
            <4>1. HV(v, x, s, g, t) BY <3>3, <1>hv DEF HV
            <4>2. NormalVote(v, x, s, g, t) \/ NSealed(s, g, t) BY <4>1, <1>i DEF VoteJust
            <4>. QED BY <4>2, <2>2, <1>nm DEF NormalVote
        <3>5. NormalQuorumV(votes', hev', v, Q, s, g, t) BY <3>2, <3>3, <3>4 DEF NormalQuorumV
        <3>. QED BY <3>5, <3>2 DEF NSealed, NSealedV
    <2>. QED BY <2>1, <2>2
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

(* ------------------------------------------------------------ stuttering *)
LEMMA StutterInv ==
    ASSUME Inv, UNCHANGED vars
    PROVE  Inv'
<1>1. /\ votes' = votes /\ act' = act /\ kv' = kv /\ adv' = adv /\ frz' = frz
      /\ gen' = gen /\ bnd' = bnd /\ cand' = cand /\ abst' = abst /\ lg' = lg /\ ld' = ld
      /\ fr' = fr /\ sb' = sb /\ sd' = sd /\ hev' = hev
    BY DEF vars
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>1 DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>1 DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>1 DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>1 DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>1 DEF Sealed
<1>T. TypeOK' BY <1>1, <1>i DEF TypeOK
<1>VS. VotesShape' BY <1>1, <1>i DEF VotesShape
<1>AS. AdvShape' BY <1>1, <1>i DEF AdvShape
<1>NE. NoEquiv' BY <1>hv, <1>i DEF NoEquiv, HonestNoEquiv
<1>CS. ContestedSilent' BY <1>1, <1>hv, <1>i DEF ContestedSilent
<1>AB. AbstBound' BY <1>1, <1>i DEF AbstBound
<1>OV. OldVotes' BY <1>1, <1>hv, <1>i DEF OldVotes
<1>CV. CurVote' BY <1>1, <1>hv, <1>dp, <1>i DEF CurVote
<1>RD. RelDisc' BY <1>hv, <1>dp, <1>i DEF RelDisc
<1>LO. LogOK' BY <1>1, <1>dp, <1>ns, <1>i DEF LogOK
<1>LD. LogDead' BY <1>1, <1>dp, <1>i DEF LogDead
<1>SD. SnapDead' BY <1>1, <1>dp, <1>i DEF SnapDead
<1>VL. VoteLogged' BY <1>1, <1>hv, <1>i DEF VoteLogged
<1>FA. FrozenAdv' BY <1>1, <1>i DEF FrozenAdv
<1>FS. FrozenStays' BY <1>1, <1>i DEF FrozenStays
<1>SV. SnapVotes' BY <1>1, <1>hv, <1>i DEF SnapVotes
<1>EL. EvLogged' BY <1>1, <1>i DEF EvLogged
<1>SE. SnapEv' BY <1>1, <1>i DEF SnapEv
<1>LI. Lineage' BY <1>1, <1>i DEF Lineage
<1>VJ. VoteJust' BY <1>hv, <1>nm, <1>ns, <1>i DEF VoteJust
<1>SN. SealedNormal' BY <1>sl, <1>ns, <1>i DEF SealedNormal
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1>. SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
<1>1. CASE \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    BY <1>1, SpendInv
<1>2. CASE \E w \in Honest, s \in Sigils : Release(w, s)
    BY <1>2, ReleaseInv
<1>3. CASE \E w \in Honest, s \in Sigils, c \in Nat \X Tids, ng \in Nat : ReleaseCand(w, s, c, ng)
    BY <1>3, ReleaseCandInv
<1>4. CASE \E w \in Honest, s \in Sigils, b \in Nat \X Tids : ResolveContested(w, s, b)
    BY <1>4, ResolveInv
<1>5. CASE \E w \in Honest : Freeze(w)
    BY <1>5, FreezeInv
<1>6. CASE \E w \in Honest, v \in Vers, F \in SUBSET Witnesses,
              XB \in ForgeBinds, XD \in ForgeDead, XS \in ForgeSeals, NG \in [Sigils -> Nat] :
                Adopt(w, v, F, XB, XD, XS, NG)
    BY <1>6, AdoptInv
<1>7. CASE \E b \in Byz, v \in Vers, s \in Sigils, g \in Nat, t \in Tids : ByzVote(b, v, s, g, t)
    BY <1>7, ByzVoteInv
<1>8. CASE UNCHANGED vars
    BY <1>8, StutterInv
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Next, HonestNext

-----------------------------------------------------------------------------
(* =====================  PART D: MAIN THEOREMS (unbounded)  =============== *)

THEOREM SpecInv == Spec => []Inv
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY NextInv
<1>. QED BY <1>1, <1>2, PTL DEF Spec

(* SPEC Section 8, Theorem, under charter rotation: no sigil is an input of *)
(* two different complete transitions, for any number of charter versions,  *)
(* witnesses, sigils, transitions and generations.                          *)
THEOREM SpecSafety == Spec => []Safety
<1>1. Inv => Safety BY Inv_Safety
<1>. QED BY <1>1, SpecInv, PTL

(* SPEC Section 8, Lemma 1, across all versions: at most one tid is sealed  *)
(* per (sigil, gen), counting the seals of every charter version.           *)
THEOREM SpecOneSealAcrossVersions == Spec => []OneSealAcrossVersions
<1>1. Inv => OneSealAcrossVersions BY Inv_OneSealAcrossVersions
<1>. QED BY <1>1, SpecInv, PTL

(* SPEC Section 8, Lemma 2, across all versions.                            *)
THEOREM SpecDeathProofsSound == Spec => []DeathProofsSound
<1>1. Inv => DeathProofsSound BY Inv_DeathProofsSound
<1>. QED BY <1>1, SpecInv, PTL

(* SPEC Section 5.4, last sentence: an honest key -- re-used or not --      *)
(* never signs two tids for one (sigil, gen), even across versions.         *)
THEOREM SpecHonestNoEquiv == Spec => []HonestNoEquiv
<1>1. Inv => HonestNoEquiv BY DEF Inv, NoEquiv
<1>. QED BY <1>1, SpecInv, PTL

(* FREEZE binds one successor (SPEC 5.4, witness.py Witness.freeze): an     *)
(* honest key of version v signs at most one successor charter, succ[h];   *)
(* Byzantine members may sign anything.  Then two different successors     *)
(* never both collect a quorum of v's signatures (the validity condition   *)
(* of SPEC 3.7), so the charter chain -- the constant Members -- is the    *)
(* only one a holder can verify.                                            *)
THEOREM OneSuccessor ==
    ASSUME NEW v \in Vers, NEW succ, NEW S1, NEW S2, S1 # S2,
           NEW Q1, NEW Q2, Q1 \subseteq Members[v], Q2 \subseteq Members[v],
           Cardinality(Q1) >= Quorum[v], Cardinality(Q2) >= Quorum[v],
           \A h \in Q1 \cap Honest : succ[h] = S1,
           \A h \in Q2 \cap Honest : succ[h] = S2
    PROVE  FALSE
<1>1. PICK h \in Q1 \cap Q2 : h \in Honest BY HonestInBothQuorums
<1>. QED BY <1>1
================================================================================
