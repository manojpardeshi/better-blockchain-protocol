---- MODULE SigilSuccProofs ----
(***************************************************************************)
(* An UNBOUNDED, machine-checked (TLAPS) proof of the Sigil safety theorem *)
(* (docs/SPEC.md Section 8) under charter rotation AND CONSTELLATION       *)
(* SUCCESSION (dead-man takeover, SPEC Section 5.5): any number of charter *)
(* versions, witnesses per version, successor-committee members, sigils,   *)
(* transitions and generations; keys may be re-used across versions and   *)
(* committees.                                                              *)
(*                                                                         *)
(* It extends the rotation proof (SigilRotProofs.tla) and reuses all of    *)
(* its machinery: the per-key records, SPEND, RELEASE, the contested       *)
(* RELEASE, W9 seal settlement, FREEZE and ADOPT with the proved lone rule *)
(* (LoneOK, ResolveOK).  What is new, per SPEC 5.5:                         *)
(*   * every charter version v may name a successor committee              *)
(*     Committee[v] (empty: no successor clause), fault-bounded like a     *)
(*     version, with quorum KQuorum[v];                                    *)
(*   * MIRROR: an honest committee member m of v that has not fenced for v *)
(*     stores any owner-authorised binding in its mirror log mir[v][m]     *)
(*     (anyone may push one);                                               *)
(*   * mirror before vote: an honest witness of a version with a committee *)
(*     votes for t at (s, g) only if a quorum of the committee has stored  *)
(*     <<g, t>> (MirQ: the mirror acks its request carries);               *)
(*   * FENCE: a standby member signs a successor of v and never mirrors    *)
(*     for v again (it must have entered standby first);                   *)
(*   * STANDBY: a member of v's committee enters standby with the evidence *)
(*     v's members adopt: the snapshots of a freezing quorum of v-1, or the *)
(*     mirror logs of a fenced quorum of v-1's committee;                  *)
(*   * ADOPT from a SUCCESSION (AdoptS): a member of v adopts from the     *)
(*     mirror logs of a fenced quorum of v-1's committee (plus anything the *)
(*     Byzantine members of that quorum add), with the same ADOPT rule.    *)
(* Rotation (Adopt from a freezing quorum) stays available for every       *)
(* version: the model over-approximates the SPEC, where a version with a   *)
(* committee is succeeded only with its committee's signatures (and the    *)
(* theorem OneSuccessorK shows those signatures make the chain linear).    *)
(* Old members are never forced to stop: after a succession they may keep  *)
(* voting (an old quorum that was merely partitioned comes back), subject  *)
(* only to their own discipline -- in particular mirror before vote.        *)
(*                                                                         *)
(* No timing assumption is used anywhere: the dead-man period of SPEC 5.5  *)
(* only decides WHEN an honest standby member fences, and Fence may happen *)
(* at any time here.                                                        *)
(*                                                                         *)
(* Cryptography is idealised as in SigilRotProofs.tla.  Every version and  *)
(* every non-empty committee has at most f Byzantine members; a key is     *)
(* honest or Byzantine for the whole run.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS
    Honest,     \* honest keys
    Byz,        \* Byzantine keys (may sign any vote for themselves)
    Vers,       \* the charter versions of the home (Nat: an unbounded chain)
    Members,    \* Vers -> SUBSET Witnesses : the members of each version
    Quorum,     \* Vers -> Nat : q of each version
    Committee,  \* Vers -> SUBSET Witnesses : each version's successor committee ({} = none)
    KQuorum,    \* Vers -> Nat : q of each committee
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
ASSUME CommitteeType     == Committee \in [Vers -> SUBSET Witnesses]
ASSUME CommitteeFinite   == \A v \in Vers : IsFiniteSet(Committee[v])
ASSUME KQuorumType       == KQuorum \in [Vers -> Nat]
ASSUME TidsNoTid         == NoTid \notin Tids
ASSUME ContestedFresh    == Contested \notin Tids /\ Contested # NoTid

(* SPEC Section 8: every version of the home is fault-bounded, and so is   *)
(* every successor committee a version names (SPEC 5.5).                   *)
Faults(n) == (n - 1) \div 3
FaultBounded(v) ==
    LET n == Cardinality(Members[v])
    IN  /\ Quorum[v] = n - Faults(n)
        /\ Cardinality(Members[v] \cap Byz) <= Faults(n)
ASSUME VersionsFaultBounded == \A v \in Vers : FaultBounded(v)

HasSucc(v) == Committee[v] # {}
KFaultBounded(v) ==
    LET n == Cardinality(Committee[v])
    IN  /\ KQuorum[v] = n - Faults(n)
        /\ Cardinality(Committee[v] \cap Byz) <= Faults(n)
ASSUME CommitteesFaultBounded == \A v \in Vers : HasSucc(v) => KFaultBounded(v)

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
    hev,    \* hev[v][w][s]: (ghost) the bind evidence w adopted for version v
    mir,    \* mir[v][m][s]: the bind entries in honest standby member m's mirror log for v
    fz,     \* fz[v]       : the honest members of v's committee that fenced (signed a successor)
    sa      \* sa[v]       : the honest members of v's committee that entered standby

vars == <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, mir, fz, sa>>

(* Seals and death proofs, over a vote set V (they only grow with V).      *)
VotersV(V, v, s, g, t)  == { w \in Members[v] : Vote(v, w, s, g, t) \in V }
AgainstV(V, v, s, g, t) == { w \in Members[v] :
                                \E u \in Tids : u # t /\ Vote(v, w, s, g, u) \in V }
SealedInV(V, v, s, g, t) == Cardinality(VotersV(V, v, s, g, t)) >= Quorum[v]
(* Holders accept a seal from any version of the home (SPEC 6.4), the      *)
(* versions before a succession included (SPEC 5.5).                       *)
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

(* ---- Succession (SPEC 5.5) ---------------------------------------------- *)
(* Mirror before vote: a quorum of v's committee whose honest members have  *)
(* stored <<g, t>> for s -- what the mirror acks of a SPEND request attest. *)
MirQV(Mir, v, s, g, t) ==
    \E A \in SUBSET Committee[v] :
        /\ Cardinality(A) >= KQuorum[v]
        /\ \A m \in A \cap Honest : <<g, t>> \in Mir[v][m][s]
MirQ(v, s, g, t) == MirQV(mir, v, s, g, t)

(* Where the evidence E (a function Sigils -> bind sets) of a later version *)
(* comes from, for an earlier version v1: it holds the snapshots of the     *)
(* honest members of a freezing quorum of v1 (rotation), or the mirror logs *)
(* of the honest members of a fenced quorum of v1's committee (succession).*)
FrozeIntoV(E, v1, Fr, Sb) ==
    \E F \in SUBSET Members[v1] :
        /\ Cardinality(F) >= Quorum[v1]
        /\ F \cap Honest \subseteq Fr[v1]
        /\ \A h \in F \cap Honest, s \in Sigils : Sb[v1][h][s] \subseteq E[s]
FencedIntoV(E, v1, Fz, Mir) ==
    \E T \in SUBSET Committee[v1] :
        /\ HasSucc(v1)
        /\ Cardinality(T) >= KQuorum[v1]
        /\ T \cap Honest \subseteq Fz[v1]
        /\ \A m \in T \cap Honest, s \in Sigils : Mir[v1][m][s] \subseteq E[s]
CoversV(E, v1, Fr, Sb, Fz, Mir) == FrozeIntoV(E, v1, Fr, Sb) \/ FencedIntoV(E, v1, Fz, Mir)
Covers(E, v1) == CoversV(E, v1, fr, sb, fz, mir)

-----------------------------------------------------------------------------
(* ADOPT's decision for one sigil, from the bind evidence EB, the dead tids *)
(* ED, the binds with a valid seal in the evidence ES, and the adopter's    *)
(* own votes O; ng is the generation used when contested or unbound.       *)
(* (Unchanged from SigilRotProofs.tla.)                                     *)
Alive(EB, ED) == { b \in EB : b[2] \notin ED }

LoneOK(EB, ES, O, b) ==
    /\ \A b2 \in EB : b2 # b => (b2[1] < b[1] \/ (b \in ES /\ b2[1] = b[1]))
    /\ \A o \in O : o[1] <= b[1]

IsLone(EB, ED, ES, O, b) == Alive(EB, ED) = {b} /\ LoneOK(EB, ES, O, b)
HasLone(EB, ED, ES, O)   == \E b \in EB : IsLone(EB, ED, ES, O, b)
TheLone(EB, ED, ES, O)   == CHOOSE b \in EB : IsLone(EB, ED, ES, O, b)

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

CandGenOK(g0, c, rest, O, ng) ==
    /\ ng >= g0
    /\ ng > c[1]
    /\ rest = {} => \A o \in O : o[1] < ng

ResolveTop(w, s, b) ==
    /\ \A c \in cand[w][s] \ {b} : c[1] <= b[1]
    /\ gen[w][s] <= b[1] + 1
ResolveOK(w, s, b) == \A o \in Own(w, s) : o[1] <= b[1]

(* The evidence of a ROTATION of v (ADOPT of v+1): the union of the        *)
(* snapshots of the honest members of the freezing quorum F of v, plus     *)
(* what F's Byzantine members add.                                          *)
EvB(v, F, XB, s) == (UNION { sb[v][h][s] : h \in F \cap Honest }) \cup XB[s]
EvD(v, F, XD, s) == (UNION { sd[v][h][s] : h \in F \cap Honest }) \cup XD[s]
(* The evidence of a SUCCESSION of v: the union of the mirror logs of the  *)
(* honest members of the fenced committee quorum T of v, plus what T's     *)
(* Byzantine members add.                                                   *)
EvM(v, T, XB, s) == (UNION { mir[v][m][s] : m \in T \cap Honest }) \cup XB[s]

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
    /\ mir  = [v \in Vers |-> [m \in Honest |-> [s \in Sigils |-> {}]]]
    /\ fz   = [v \in Vers |-> {}]
    /\ sa   = [v \in Vers |-> {}]

Init == votes = {} /\ InitRecords

(* SPEC 5.1 step 4 (the owner is adversarial: every request may arrive),   *)
(* with SPEC 5.5's mirror before vote in a version with a committee.       *)
Spend(w, s, t) ==
    /\ act[w] /\ ~frz[w]
    /\ s \in SigilsOf(t)
    /\ LET g == GenOf(t, s) IN
        /\ \/ g >= gen[w][s] /\ bnd[w][s] = NoTid
           \/ g = gen[w][s] /\ bnd[w][s] = t /\ ~abst[w][s]
        /\ HasSucc(kv[w]) => MirQ(kv[w], s, g, t)
        /\ gen'   = [gen EXCEPT ![w][s] = g]
        /\ bnd'   = [bnd EXCEPT ![w][s] = t]
        /\ lg'    = [lg  EXCEPT ![w][s] = @ \cup {<<g, t>>}]
        /\ votes' = votes \cup {Vote(kv[w], w, s, g, t)}
    /\ UNCHANGED <<act, kv, adv, frz, cand, abst, ld, fr, sb, sd, hev, mir, fz, sa>>

(* SPEC 5.2 steps 3-4.                                                      *)
Release(w, s) ==
    /\ act[w] /\ ~frz[w]
    /\ bnd[w][s] \in Tids
    /\ DeathProof(bnd[w][s])
    /\ gen'  = [gen  EXCEPT ![w][s] = @ + 1]
    /\ bnd'  = [bnd  EXCEPT ![w][s] = NoTid]
    /\ abst' = [abst EXCEPT ![w][s] = FALSE]
    /\ ld'   = [ld   EXCEPT ![w][s] = @ \cup {bnd[w][s]}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, cand, lg, fr, sb, sd, hev, mir, fz, sa>>

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
    /\ UNCHANGED <<votes, act, kv, adv, frz, abst, lg, fr, sb, sd, hev, mir, fz, sa>>

(* W9 seal settlement of a contested record (as in SigilRotProofs.tla).     *)
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
    /\ UNCHANGED <<votes, act, kv, adv, frz, lg, fr, sb, sd, hev, mir, fz, sa>>

(* SPEC 5.4 FREEZE: stop voting and releasing in this version; hand over   *)
(* the log.                                                                 *)
Freeze(w) ==
    /\ act[w] /\ ~frz[w]
    /\ frz' = [frz EXCEPT ![w] = TRUE]
    /\ fr'  = [fr  EXCEPT ![kv[w]] = @ \cup {w}]
    /\ sb'  = [sb  EXCEPT ![kv[w]][w] = lg[w]]
    /\ sd'  = [sd  EXCEPT ![kv[w]][w] = ld[w]]
    /\ UNCHANGED <<votes, act, kv, adv, gen, bnd, cand, abst, lg, ld, hev, mir, fz, sa>>

(* SPEC 5.4 ADOPT of version v, from the bind evidence EB, dead tids ED and *)
(* seals XS (functions over Sigils).  Adopt and AdoptS below differ only in *)
(* where the evidence comes from.  The new log is the evidence.            *)
AdoptCore(w, v, EB, ED, XS, NG) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ w \in Members[v]
    /\ act[w] => kv[w] < v
    /\ XS \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ \A s \in Sigils : \A b \in XS[s] : Sealed(s, b[1], b[2])
    /\ NG \in [Sigils -> Nat]
    /\ \A s \in Sigils : GenOK(EB[s], ED[s], Own(w, s), NG[s])
    /\ gen'  = [gen  EXCEPT ![w] = [s \in Sigils |-> NewRec(EB[s], ED[s], XS[s], Own(w, s), NG[s]).g]]
    /\ bnd'  = [bnd  EXCEPT ![w] = [s \in Sigils |-> NewRec(EB[s], ED[s], XS[s], Own(w, s), NG[s]).t]]
    /\ cand' = [cand EXCEPT ![w] = [s \in Sigils |-> NewRec(EB[s], ED[s], XS[s], Own(w, s), NG[s]).c]]
    /\ abst' = [abst EXCEPT ![w] = [s \in Sigils |-> NewRec(EB[s], ED[s], XS[s], Own(w, s), NG[s]).a]]
    /\ lg'   = [lg   EXCEPT ![w] = EB]
    /\ ld'   = [ld   EXCEPT ![w] = ED]
    /\ hev'  = [hev  EXCEPT ![v][w] = EB]
    /\ act'  = [act  EXCEPT ![w] = TRUE]
    /\ kv'   = [kv   EXCEPT ![w] = v]
    /\ adv'  = [adv  EXCEPT ![w] = @ \cup {v}]
    /\ frz'  = [frz  EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<votes, fr, sb, sd, mir, fz, sa>>

(* ADOPT after a ROTATION of v-1, from a freezing quorum F of v-1 (as in   *)
(* SigilRotProofs.tla).  XB, XD, XS: what Byzantine members of F may add   *)
(* (any bind; releases with a death proof; seals that verify).             *)
Adopt(w, v, F, XB, XD, XS, NG) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ F \subseteq Members[v - 1]
    /\ Cardinality(F) >= Quorum[v - 1]
    /\ F \cap Honest \subseteq fr[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ XD \in [Sigils -> SUBSET Tids]
    /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    /\ AdoptCore(w, v, [s \in Sigils |-> EvB(v - 1, F, XB, s)],
                       [s \in Sigils |-> EvD(v - 1, F, XD, s)], XS, NG)

(* SPEC 5.5: ADOPT after a SUCCESSION of v-1, from the mirror logs of a    *)
(* fenced quorum T of v-1's committee.  XB, XD, XS: what T's Byzantine     *)
(* members may add (their release entries need a death proof, as always). *)
AdoptS(w, v, T, XB, XD, XS, NG) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ HasSucc(v - 1)
    /\ T \subseteq Committee[v - 1]
    /\ Cardinality(T) >= KQuorum[v - 1]
    /\ T \cap Honest \subseteq fz[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ XD \in [Sigils -> SUBSET Tids]
    /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    /\ AdoptCore(w, v, [s \in Sigils |-> EvM(v - 1, T, XB, s)], XD, XS, NG)

(* SPEC 5.5 MIRROR: an honest member m of v's committee that has not       *)
(* fenced for v stores an owner-authorised binding (<<s, g>> is an input  *)
(* of t).  Anyone may push one: the owner is adversarial.                  *)
MirrorAck(m, v, s, b) ==
    /\ m \in Committee[v] /\ m \notin fz[v]
    /\ <<s, b[1]>> \in Header[b[2]]
    /\ mir' = [mir EXCEPT ![v][m][s] = @ \cup {b}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, fz, sa>>

(* SPEC 5.5 SUCCEED: m signs a successor of v (cooperatively or as a dead  *)
(* man -- when is a liveness matter, so it may happen at any time here)    *)
(* and fences: it never mirrors for v again.  It must be in standby.       *)
Fence(m, v) ==
    /\ m \in Committee[v] /\ m \in sa[v]
    /\ fz' = [fz EXCEPT ![v] = @ \cup {m}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, mir, sa>>

(* SPEC 5.5 STANDBY: a member of v's committee enters standby with the     *)
(* evidence E that v's members adopt; its mirror log starts with it.       *)
StandbyCore(m, v, E) ==
    /\ m \in Committee[v] /\ m \notin sa[v]
    /\ mir' = [mir EXCEPT ![v][m] = [s \in Sigils |-> mir[v][m][s] \cup E[s]]]
    /\ sa'  = [sa  EXCEPT ![v] = @ \cup {m}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, fz>>
(* ... version 0 has no predecessor (XB: anything) ...                     *)
Standby0(m, XB) ==
    /\ 0 \in Vers
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ StandbyCore(m, 0, XB)
(* ... after a rotation of v-1: a freezing quorum's snapshots ...          *)
StandbyR(m, v, F, XB) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ F \subseteq Members[v - 1]
    /\ Cardinality(F) >= Quorum[v - 1]
    /\ F \cap Honest \subseteq fr[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ StandbyCore(m, v, [s \in Sigils |-> EvB(v - 1, F, XB, s)])
(* ... after a succession of v-1: a fenced committee quorum's mirror logs. *)
StandbyS(m, v, T, XB) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ HasSucc(v - 1)
    /\ T \subseteq Committee[v - 1]
    /\ Cardinality(T) >= KQuorum[v - 1]
    /\ T \cap Honest \subseteq fz[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ StandbyCore(m, v, [s \in Sigils |-> EvM(v - 1, T, XB, s)])

ByzVote(b, v, s, g, t) ==
    /\ votes' = votes \cup {Vote(v, b, s, g, t)}
    /\ UNCHANGED <<act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, mir, fz, sa>>

(* The evidence Byzantine members may add (checked in the actions).  TLC   *)
(* instances override these with small sets.                                *)
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
    \/ \E w \in Honest, v \in Vers, T \in SUBSET Witnesses,
          XB \in ForgeBinds, XD \in ForgeDead, XS \in ForgeSeals, NG \in [Sigils -> Nat] :
            AdoptS(w, v, T, XB, XD, XS, NG)
    \/ \E m \in Honest, v \in Vers, s \in Sigils, b \in Nat \X Tids : MirrorAck(m, v, s, b)
    \/ \E m \in Honest, v \in Vers : Fence(m, v)
    \/ \E m \in Honest, XB \in ForgeBinds : Standby0(m, XB)
    \/ \E m \in Honest, v \in Vers, F \in SUBSET Witnesses, XB \in ForgeBinds : StandbyR(m, v, F, XB)
    \/ \E m \in Honest, v \in Vers, T \in SUBSET Witnesses, XB \in ForgeBinds : StandbyS(m, v, T, XB)

Next ==
    \/ HonestNext
    \/ \E b \in Byz, v \in Vers, s \in Sigils, g \in Nat, t \in Tids : ByzVote(b, v, s, g, t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* The properties (as in SigilRotProofs.tla).                               *)
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
(* The inductive invariant: the rotation proof's, with Lineage generalised *)
(* to successions, plus the succession conjuncts.                          *)
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
    /\ mir  \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]
    /\ fz   \in [Vers -> SUBSET Honest]
    /\ sa   \in [Vers -> SUBSET Honest]

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

OldVotes ==
    \A w \in Honest, s \in Sigils, v \in Vers, g \in Nat, t \in Tids :
        (act[w] /\ HV(v, w, s, g, t) /\ v < kv[w]) =>
            \/ bnd[w][s] = Contested
            \/ g < gen[w][s]
            \/ g = gen[w][s] /\ bnd[w][s] \in Tids /\ (bnd[w][s] = t \/ abst[w][s])

CurVote ==
    \A w \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (act[w] /\ HV(kv[w], w, s, g, t)) =>
            \/ g < gen[w][s] /\ DeathProof(t)
            \/ g = gen[w][s] /\ bnd[w][s] = t

RelDisc ==
    \A w \in Honest, s \in Sigils, v \in Vers, g1, g2 \in Nat, t1, t2 \in Tids :
        (HV(v, w, s, g1, t1) /\ HV(v, w, s, g2, t2) /\ g1 < g2) => DeathProof(t1)

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

SnapVotes ==
    \A v \in Vers, h \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (h \in fr[v] /\ HV(v, h, s, g, t)) => <<g, t>> \in sb[v][h][s]

EvLogged == \A w \in Honest, s \in Sigils : act[w] => hev[kv[w]][w][s] \subseteq lg[w][s]

SnapEv == \A v \in Vers, h \in Honest, s \in Sigils : h \in fr[v] => hev[v][h][s] \subseteq sb[v][h][s]

(* GENERALISED: the evidence any key adopted for v2 covers EVERY earlier   *)
(* version v1 -- by a freezing quorum's snapshots or a fenced committee    *)
(* quorum's mirror logs.                                                    *)
Lineage ==
    \A w \in Honest, v2 \in Vers, v1 \in Vers : (v2 \in adv[w] /\ v1 < v2) =>
        Covers(hev[v2][w], v1)

VoteJust ==
    \A w \in Honest, s \in Sigils, v \in Vers, g \in Nat, t \in Tids :
        HV(v, w, s, g, t) => NormalVote(v, w, s, g, t) \/ NSealed(s, g, t)

SealedNormal ==
    \A s \in Sigils, g \in Nat, t \in Tids : Sealed(s, g, t) => NSealed(s, g, t)

(* ---- Succession conjuncts ---------------------------------------------- *)
(* A member fences only once in standby.                                    *)
FenceShape == \A v \in Vers : fz[v] \subseteq sa[v]

(* Mirror before vote: behind every honest vote of a version with a        *)
(* committee there is a committee quorum whose honest members stored it.   *)
MirVotes ==
    \A w \in Honest, v \in Vers, s \in Sigils, g \in Nat, t \in Tids :
        (HV(v, w, s, g, t) /\ HasSucc(v)) => MirQ(v, s, g, t)

(* A standby member's mirror log covers every earlier version, like the    *)
(* evidence of a member (it entered standby with that evidence).           *)
StandbyLin ==
    \A v \in Vers, m \in Honest, v1 \in Vers : (m \in sa[v] /\ v1 < v) => Covers(mir[v][m], v1)

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
    /\ FenceShape
    /\ MirVotes
    /\ StandbyLin

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


(* Quorum intersection in a fault-bounded successor committee (SPEC 5.5),  *)
(* PROVED like HonestInBothQuorums.                                         *)
LEMMA HonestInBothKQuorums ==
    ASSUME NEW v \in Vers, HasSucc(v), NEW A, NEW B,
           A \subseteq Committee[v], B \subseteq Committee[v],
           Cardinality(A) >= KQuorum[v], Cardinality(B) >= KQuorum[v]
    PROVE  \E w \in A \cap B : w \in Honest
<1> DEFINE M == Committee[v]
           n == Cardinality(M)
           f == (n - 1) \div 3
           H == M \ Byz
           AB == A \cap B
<1>mf. IsFiniteSet(M) BY CommitteeFinite
<1>ne. M # {} BY DEF HasSucc
<1>n1. n \in Nat /\ n >= 1 BY <1>mf, <1>ne, FS_EmptySet, FS_CardinalityType
<1>ff. f \in Nat BY <1>n1
<1>fb. KQuorum[v] = n - f /\ Cardinality(M \cap Byz) <= f
    BY CommitteesFaultBounded DEF KFaultBounded, Faults
<1>n3f. n > 3 * f BY <1>n1, <1>ff, FaultArith
<1>af. IsFiniteSet(A) /\ Cardinality(A) \in Nat /\ Cardinality(A) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>bf. IsFiniteSet(B) /\ Cardinality(B) \in Nat /\ Cardinality(B) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>qn. KQuorum[v] \in Nat /\ KQuorum[v] <= n BY KQuorumType, <1>fb, <1>n1
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
    <2>3. w \in Witnesses BY <2>2, CommitteeType
    <2>4. w \in Honest BY <2>2, <2>3 DEF Witnesses
    <2>. QED BY <2>1, <2>2, <2>4

LEMMA KQuorumHasHonest ==
    ASSUME NEW v \in Vers, HasSucc(v), NEW A, A \subseteq Committee[v],
           Cardinality(A) >= KQuorum[v]
    PROVE  \E w \in A : w \in Honest
<1>1. \E w \in A \cap A : w \in Honest BY HonestInBothKQuorums
<1>. QED BY <1>1

(* Mirror before vote survives more mirror entries.                         *)
LEMMA MirQMono ==
    ASSUME NEW M1, NEW M2, NEW v, NEW s, NEW g, NEW t,
           \A m \in Honest : <<g, t>> \in M1[v][m][s] => <<g, t>> \in M2[v][m][s],
           MirQV(M1, v, s, g, t)
    PROVE  MirQV(M2, v, s, g, t)
<1>1. PICK A \in SUBSET Committee[v] :
          /\ Cardinality(A) >= KQuorum[v]
          /\ \A m \in A \cap Honest : <<g, t>> \in M1[v][m][s]
    BY DEF MirQV
<1>. QED BY <1>1 DEF MirQV

(* What evidence covers grows with the evidence ...                         *)
LEMMA CoversMono ==
    ASSUME NEW E1, NEW E2, NEW v1, NEW Fr, NEW Sb, NEW Fz, NEW Mir,
           \A s \in Sigils : E1[s] \subseteq E2[s],
           CoversV(E1, v1, Fr, Sb, Fz, Mir)
    PROVE  CoversV(E2, v1, Fr, Sb, Fz, Mir)
<1>1. CASE FrozeIntoV(E1, v1, Fr, Sb)
    <2>1. PICK F \in SUBSET Members[v1] :
              /\ Cardinality(F) >= Quorum[v1]
              /\ F \cap Honest \subseteq Fr[v1]
              /\ \A h \in F \cap Honest, s \in Sigils : Sb[v1][h][s] \subseteq E1[s]
        BY <1>1 DEF FrozeIntoV
    <2>2. \A h \in F \cap Honest, s \in Sigils : Sb[v1][h][s] \subseteq E2[s] BY <2>1
    <2>3. FrozeIntoV(E2, v1, Fr, Sb) BY <2>1, <2>2 DEF FrozeIntoV
    <2>. QED BY <2>3 DEF CoversV
<1>2. CASE FencedIntoV(E1, v1, Fz, Mir)
    <2>1. PICK T \in SUBSET Committee[v1] :
              /\ HasSucc(v1)
              /\ Cardinality(T) >= KQuorum[v1]
              /\ T \cap Honest \subseteq Fz[v1]
              /\ \A m \in T \cap Honest, s \in Sigils : Mir[v1][m][s] \subseteq E1[s]
        BY <1>2 DEF FencedIntoV
    <2>2. \A m \in T \cap Honest, s \in Sigils : Mir[v1][m][s] \subseteq E2[s] BY <2>1
    <2>3. FencedIntoV(E2, v1, Fz, Mir) BY <2>1, <2>2 DEF FencedIntoV
    <2>. QED BY <2>3 DEF CoversV
<1>. QED BY <1>1, <1>2 DEF CoversV

(* ... and survives more frozen keys and fenced standby members, as long as *)
(* the snapshots of frozen keys and the mirror logs of fenced members stay. *)
LEMMA CoversFrame ==
    ASSUME NEW E, NEW v1, NEW Fr1, NEW Fr2, NEW Sb1, NEW Sb2, NEW Fz1, NEW Fz2,
           NEW Mir1, NEW Mir2,
           Fr1[v1] \subseteq Fr2[v1],
           \A h \in Honest : h \in Fr1[v1] => \A s \in Sigils : Sb2[v1][h][s] = Sb1[v1][h][s],
           Fz1[v1] \subseteq Fz2[v1],
           \A m \in Honest : m \in Fz1[v1] => \A s \in Sigils : Mir2[v1][m][s] = Mir1[v1][m][s],
           CoversV(E, v1, Fr1, Sb1, Fz1, Mir1)
    PROVE  CoversV(E, v1, Fr2, Sb2, Fz2, Mir2)
<1>1. CASE FrozeIntoV(E, v1, Fr1, Sb1)
    <2>1. PICK F \in SUBSET Members[v1] :
              /\ Cardinality(F) >= Quorum[v1]
              /\ F \cap Honest \subseteq Fr1[v1]
              /\ \A h \in F \cap Honest, s \in Sigils : Sb1[v1][h][s] \subseteq E[s]
        BY <1>1 DEF FrozeIntoV
    <2>2. F \cap Honest \subseteq Fr2[v1] BY <2>1
    <2>3. \A h \in F \cap Honest, s \in Sigils : Sb2[v1][h][s] \subseteq E[s] BY <2>1
    <2>4. FrozeIntoV(E, v1, Fr2, Sb2) BY <2>1, <2>2, <2>3 DEF FrozeIntoV
    <2>. QED BY <2>4 DEF CoversV
<1>2. CASE FencedIntoV(E, v1, Fz1, Mir1)
    <2>1. PICK T \in SUBSET Committee[v1] :
              /\ HasSucc(v1)
              /\ Cardinality(T) >= KQuorum[v1]
              /\ T \cap Honest \subseteq Fz1[v1]
              /\ \A m \in T \cap Honest, s \in Sigils : Mir1[v1][m][s] \subseteq E[s]
        BY <1>2 DEF FencedIntoV
    <2>2. T \cap Honest \subseteq Fz2[v1] BY <2>1
    <2>3. \A m \in T \cap Honest, s \in Sigils : Mir2[v1][m][s] \subseteq E[s] BY <2>1
    <2>4. FencedIntoV(E, v1, Fz2, Mir2) BY <2>1, <2>2, <2>3 DEF FencedIntoV
    <2>. QED BY <2>4 DEF CoversV
<1>. QED BY <1>1, <1>2 DEF CoversV

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
(* THE cross-version transfer, for rotations AND successions.  If A is a  *)
(* quorum of an OLDER version v1, the evidence any honest key adopted for  *)
(* v2 contains the binds behind every v1-vote of some honest member h of   *)
(* A.  The lineage says how that evidence covers v1:                        *)
(*  * by a freezing quorum F of v1: A and F share an honest member h       *)
(*    (quorum intersection, proved); h froze in v1, and its snapshot holds *)
(*    the bind behind each of its v1 votes;                                 *)
(*  * by a fenced quorum T of v1's committee: take ANY honest h in A.  Each *)
(*    of h's v1 votes was cast with a committee quorum A2 holding its bind  *)
(*    (mirror before vote); A2 and T share an honest standby member, whose  *)
(*    mirror log -- frozen since it fenced -- is in the evidence.           *)
LEMMA InheritVote ==
    ASSUME Inv, NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv[w], v1 < v2,
           NEW A, A \subseteq Members[v1], Cardinality(A) >= Quorum[v1]
    PROVE  \E h \in A : /\ h \in Honest
                        /\ \A s \in Sigils, g \in Nat, u \in Tids :
                               HV(v1, h, s, g, u) => <<g, u>> \in hev[v2][w][s]
<1>0. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY DEF Inv, Lineage, Covers
<1>1. CASE FrozeIntoV(hev[v2][w], v1, fr, sb)
    <2>1. PICK F \in SUBSET Members[v1] :
            /\ Cardinality(F) >= Quorum[v1]
            /\ F \cap Honest \subseteq fr[v1]
            /\ \A h \in F \cap Honest, s \in Sigils : sb[v1][h][s] \subseteq hev[v2][w][s]
        BY <1>1 DEF FrozeIntoV
    <2>2. PICK h \in A \cap F : h \in Honest BY <2>1, HonestInBothQuorums
    <2>3. h \in fr[v1] BY <2>1, <2>2
    <2>4. \A s \in Sigils, g \in Nat, u \in Tids : HV(v1, h, s, g, u) => <<g, u>> \in sb[v1][h][s]
        BY <2>2, <2>3 DEF Inv, SnapVotes
    <2>. QED BY <2>1, <2>2, <2>4
<1>2. CASE FencedIntoV(hev[v2][w], v1, fz, mir)
    <2>1. PICK T \in SUBSET Committee[v1] :
            /\ HasSucc(v1)
            /\ Cardinality(T) >= KQuorum[v1]
            /\ T \cap Honest \subseteq fz[v1]
            /\ \A m \in T \cap Honest, s \in Sigils : mir[v1][m][s] \subseteq hev[v2][w][s]
        BY <1>2 DEF FencedIntoV
    <2>2. PICK h \in A : h \in Honest BY QuorumHasHonest
    <2>3. \A s \in Sigils, g \in Nat, u \in Tids : HV(v1, h, s, g, u) => <<g, u>> \in hev[v2][w][s]
        <3> SUFFICES ASSUME NEW s \in Sigils, NEW g \in Nat, NEW u \in Tids, HV(v1, h, s, g, u)
                     PROVE  <<g, u>> \in hev[v2][w][s]
            OBVIOUS
        <3>1. MirQ(v1, s, g, u) BY <2>1, <2>2 DEF Inv, MirVotes
        <3>2. PICK A2 \in SUBSET Committee[v1] :
                /\ Cardinality(A2) >= KQuorum[v1]
                /\ \A m \in A2 \cap Honest : <<g, u>> \in mir[v1][m][s]
            BY <3>1 DEF MirQ, MirQV
        <3>3. PICK m \in A2 \cap T : m \in Honest BY <2>1, <3>2, HonestInBothKQuorums
        <3>. QED BY <2>1, <3>2, <3>3
    <2>. QED BY <2>2, <2>3
<1>. QED BY <1>0, <1>1, <1>2 DEF CoversV

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
          /\ mir \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]]
          /\ fz \in [Vers -> SUBSET Honest]
          /\ sa \in [Vers -> SUBSET Honest]
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
<1>F2. FenceShape BY <1>r DEF InitRecords, FenceShape
<1>M2. MirVotes BY <1>v DEF MirVotes, HV
<1>S2. StandbyLin BY <1>r DEF InitRecords, StandbyLin
<1>. QED BY <1>T, <1>A, <1>C, <1>B, <1>V1, <1>V2, <1>V3, <1>L1, <1>L2, <1>L3, <1>L4,
            <1>L5, <1>L6, <1>L7, <1>N, <1>S, <1>F2, <1>M2, <1>S2 DEF Inv

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
      /\ FenceShape /\ MirVotes /\ StandbyLin
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
         /\ UNCHANGED <<act, kv, adv, frz, cand, abst, ld, fr, sb, sd, hev, mir, fz, sa>>
    BY DEF Spend
<1>mq. HasSucc(v0) => MirQ(v0, s0, g0, t0) BY DEF Spend
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
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage, Covers
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
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v \in Vers, NEW s \in Sigils, NEW g \in Nat,
                        NEW t \in Tids, HV(v, w, s, g, t)', HasSucc(v)
                 PROVE  MirQ(v, s, g, t)'
        BY DEF MirVotes
    <2>0. MirQ(v, s, g, t)' <=> MirQ(v, s, g, t) BY <1>post DEF MirQ
    <2>1. CASE HV(v, w, s, g, t) BY <2>1, <2>0, <1>i DEF MirVotes
    <2>2. CASE v = v0 /\ w = w0 /\ s = s0 /\ g = g0 /\ t = t0 BY <2>2, <2>0, <1>mq
    <2>. QED BY <1>hv, <2>1, <2>2
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* -------------------------------------------------------------- Release  *)
LEMMA ReleaseInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, Release(w0, s0)
    PROVE  Inv'
<1> DEFINE tb == bnd[w0][s0]
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
      /\ FenceShape /\ MirVotes /\ StandbyLin
    BY DEF Inv
<1>a. act[w0] /\ ~frz[w0] /\ tb \in Tids /\ DeathProof(tb) BY DEF Release
<1>post. /\ gen'  = [gen  EXCEPT ![w0][s0] = @ + 1]
         /\ bnd'  = [bnd  EXCEPT ![w0][s0] = NoTid]
         /\ abst' = [abst EXCEPT ![w0][s0] = FALSE]
         /\ ld'   = [ld   EXCEPT ![w0][s0] = @ \cup {tb}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, cand, lg, fr, sb, sd, hev, mir, fz, sa>>
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
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage, Covers
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* ------------------------------------------------- contested release  *)
LEMMA ReleaseCandInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW s0 \in Sigils, NEW c, NEW ng, ReleaseCand(w0, s0, c, ng)
    PROVE  Inv'
<1> DEFINE rest == cand[w0][s0] \ {c}
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
      /\ FenceShape /\ MirVotes /\ StandbyLin
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
         /\ UNCHANGED <<votes, act, kv, adv, frz, abst, lg, fr, sb, sd, hev, mir, fz, sa>>
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
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage, Covers
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

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
      /\ FenceShape /\ MirVotes /\ StandbyLin
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
         /\ UNCHANGED <<votes, act, kv, adv, frz, lg, fr, sb, sd, hev, mir, fz, sa>>
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
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage, Covers
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* --------------------------------------------------------------- Freeze  *)
LEMMA FreezeInv ==
    ASSUME Inv, NEW w0 \in Honest, Freeze(w0)
    PROVE  Inv'
<1> DEFINE v0 == kv[w0]
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
      /\ FenceShape /\ MirVotes /\ StandbyLin
    BY DEF Inv
<1>a. act[w0] /\ ~frz[w0] BY DEF Freeze
<1>post. /\ frz' = [frz EXCEPT ![w0] = TRUE]
         /\ fr'  = [fr  EXCEPT ![v0] = @ \cup {w0}]
         /\ sb'  = [sb  EXCEPT ![v0][w0] = lg[w0]]
         /\ sd'  = [sd  EXCEPT ![v0][w0] = ld[w0]]
         /\ UNCHANGED <<votes, act, kv, adv, gen, bnd, cand, abst, lg, ld, hev, mir, fz, sa>>
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
(* Freezing adds w0's snapshot; what any evidence covers is unchanged.     *)
<1>cf. \A E : \A v1 \in Vers : CoversV(E, v1, fr, sb, fz, mir) => CoversV(E, v1, fr', sb', fz', mir')
    <2> SUFFICES ASSUME NEW E, NEW v1 \in Vers, CoversV(E, v1, fr, sb, fz, mir)
                 PROVE  CoversV(E, v1, fr', sb', fz', mir')
        OBVIOUS
    <2>1. fr[v1] \subseteq fr'[v1] BY <1>fr
    <2>2. \A h \in Honest : h \in fr[v1] => \A s \in Sigils : sb'[v1][h][s] = sb[v1][h][s]
        BY <1>sb, <1>nf
    <2>3. fz[v1] \subseteq fz'[v1] BY <1>post
    <2>4. \A m \in Honest : m \in fz[v1] => \A s \in Sigils : mir'[v1][m][s] = mir[v1][m][s]
        BY <1>post
    <2>. QED BY <2>1, <2>2, <2>3, <2>4, CoversFrame
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
                 PROVE  CoversV(hev'[v2][w], v1, fr', sb', fz', mir')
        BY DEF Lineage, Covers
    <2>1. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF Lineage, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>VJ. VoteJust' BY <1>i, <1>hv, <1>nm, <1>ns DEF VoteJust
<1>SN. SealedNormal' BY <1>i, <1>sl, <1>ns DEF SealedNormal
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW m \in Honest, NEW v1 \in Vers, m \in sa'[v], v1 < v
                 PROVE  CoversV(mir'[v][m], v1, fr', sb', fz', mir')
        BY DEF StandbyLin, Covers
    <2>1. CoversV(mir[v][m], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF StandbyLin, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* ---------------------------------------------------------------- Adopt  *)
(* The ADOPT step itself, for any evidence of the right type that covers *)
(* every earlier version (rotation and succession, below, provide it).   *)
LEMMA AdoptCoreInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW v0, NEW EBf, NEW EDf, NEW XS, NEW NG,
           AdoptCore(w0, v0, EBf, EDf, XS, NG),
           EBf \in [Sigils -> SUBSET (Nat \X Tids)],
           EDf \in [Sigils -> SUBSET Tids],
           \A s \in Sigils : \A t \in EDf[s] : DeathProof(t),
           \A v1 \in Vers : v1 < v0 => Covers(EBf, v1)
    PROVE  Inv'
<1> DEFINE EB(s) == EBf[s]
           ED(s) == EDf[s]
           O(s)  == Own(w0, s)
           R(s)  == NewRec(EB(s), ED(s), XS[s], O(s), NG[s])
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
      /\ FenceShape /\ MirVotes /\ StandbyLin
    BY DEF Inv
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ w0 \in Members[v0]
      /\ act[w0] => kv[w0] < v0
      /\ XS \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ \A s \in Sigils : \A b \in XS[s] : Sealed(s, b[1], b[2])
      /\ NG \in [Sigils -> Nat]
      /\ \A s \in Sigils : GenOK(EB(s), ED(s), O(s), NG[s])
    BY DEF AdoptCore
<1>post. /\ gen'  = [gen  EXCEPT ![w0] = [s \in Sigils |-> R(s).g]]
         /\ bnd'  = [bnd  EXCEPT ![w0] = [s \in Sigils |-> R(s).t]]
         /\ cand' = [cand EXCEPT ![w0] = [s \in Sigils |-> R(s).c]]
         /\ abst' = [abst EXCEPT ![w0] = [s \in Sigils |-> R(s).a]]
         /\ lg'   = [lg   EXCEPT ![w0] = EBf]
         /\ ld'   = [ld   EXCEPT ![w0] = EDf]
         /\ hev'  = [hev  EXCEPT ![v0][w0] = EBf]
         /\ act'  = [act  EXCEPT ![w0] = TRUE]
         /\ kv'   = [kv   EXCEPT ![w0] = v0]
         /\ adv'  = [adv  EXCEPT ![w0] = @ \cup {v0}]
         /\ frz'  = [frz  EXCEPT ![w0] = FALSE]
         /\ UNCHANGED <<votes, fr, sb, sd, mir, fz, sa>>
    BY DEF AdoptCore
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
    BY <1>i, OwnType
<1>k5. \A s \in Sigils : \A t \in ED(s) : DeathProof(t) OBVIOUS
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
                 PROVE  CoversV(hev'[v2][w], v1, fr', sb', fz', mir')
        BY DEF Lineage, Covers
    <2>fr. fr' = fr /\ sb' = sb /\ fz' = fz /\ mir' = mir BY <1>post
    <2>1. CASE w = w0 /\ v2 = v0
        <3>1. hev'[v0][w0] = EBf BY <1>post, <1>a, <1>i DEF TypeOK
        <3>2. CoversV(EBf, v1, fr, sb, fz, mir) BY <2>1 DEF Covers
        <3>. QED BY <2>1, <3>1, <3>2, <2>fr
    <2>2. CASE ~(w = w0 /\ v2 = v0)
        <3>1. v2 \in adv[w] BY <2>2, <1>adv
        <3>2. hev'[v2][w] = hev[v2][w] BY <2>2, <1>post, <1>a, <1>i DEF TypeOK
        <3>3. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY <3>1, <1>i DEF Lineage, Covers
        <3>. QED BY <3>2, <3>3, <2>fr
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
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* --------------------------------------------- the evidence of ADOPT/STANDBY *)
LEMMA EvBType ==
    ASSUME Inv, NEW v \in Vers, NEW F, NEW XB, XB \in [Sigils -> SUBSET (Nat \X Tids)]
    PROVE  [s \in Sigils |-> EvB(v, F, XB, s)] \in [Sigils -> SUBSET (Nat \X Tids)]
<1> SUFFICES ASSUME NEW s \in Sigils, NEW b \in EvB(v, F, XB, s) PROVE b \in Nat \X Tids OBVIOUS
<1>1. b \in UNION { sb[v][h][s] : h \in F \cap Honest } \/ b \in XB[s] BY DEF EvB
<1>2. CASE b \in XB[s] BY <1>2
<1>3. CASE b \in UNION { sb[v][h][s] : h \in F \cap Honest }
    <2>1. PICK h \in F \cap Honest : b \in sb[v][h][s] BY <1>3
    <2>. QED BY <2>1 DEF Inv, TypeOK
<1>. QED BY <1>1, <1>2, <1>3

LEMMA EvDType ==
    ASSUME Inv, NEW v \in Vers, NEW F, NEW XD, XD \in [Sigils -> SUBSET Tids],
           \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    PROVE  /\ [s \in Sigils |-> EvD(v, F, XD, s)] \in [Sigils -> SUBSET Tids]
           /\ \A s \in Sigils : \A t \in EvD(v, F, XD, s) : t \in Tids /\ DeathProof(t)
<1>1. \A s \in Sigils : \A t \in EvD(v, F, XD, s) : t \in Tids /\ DeathProof(t)
    <2> SUFFICES ASSUME NEW s \in Sigils, NEW t \in EvD(v, F, XD, s) PROVE t \in Tids /\ DeathProof(t)
        OBVIOUS
    <2>1. t \in UNION { sd[v][h][s] : h \in F \cap Honest } \/ t \in XD[s] BY DEF EvD
    <2>2. CASE t \in XD[s] BY <2>2
    <2>3. CASE t \in UNION { sd[v][h][s] : h \in F \cap Honest }
        <3>1. PICK h \in F \cap Honest : t \in sd[v][h][s] BY <2>3
        <3>. QED BY <3>1 DEF Inv, TypeOK, SnapDead
    <2>. QED BY <2>1, <2>2, <2>3
<1>. QED BY <1>1

LEMMA EvMType ==
    ASSUME Inv, NEW v \in Vers, NEW T, NEW XB, XB \in [Sigils -> SUBSET (Nat \X Tids)]
    PROVE  [s \in Sigils |-> EvM(v, T, XB, s)] \in [Sigils -> SUBSET (Nat \X Tids)]
<1> SUFFICES ASSUME NEW s \in Sigils, NEW b \in EvM(v, T, XB, s) PROVE b \in Nat \X Tids OBVIOUS
<1>1. b \in UNION { mir[v][m][s] : m \in T \cap Honest } \/ b \in XB[s] BY DEF EvM
<1>2. CASE b \in XB[s] BY <1>2
<1>3. CASE b \in UNION { mir[v][m][s] : m \in T \cap Honest }
    <2>1. PICK m \in T \cap Honest : b \in mir[v][m][s] BY <1>3
    <2>. QED BY <2>1 DEF Inv, TypeOK
<1>. QED BY <1>1, <1>2, <1>3

(* The evidence of a rotation of v0-1 covers every earlier version: v0-1   *)
(* by the freezing quorum itself, older ones through the evidence an honest *)
(* member of that quorum adopted (it is in its snapshot).                   *)
LEMMA EvBCovers ==
    ASSUME Inv, NEW v0 \in Vers, v0 >= 1, v0 - 1 \in Vers, NEW F0, NEW XB,
           F0 \subseteq Members[v0 - 1], Cardinality(F0) >= Quorum[v0 - 1],
           F0 \cap Honest \subseteq fr[v0 - 1]
    PROVE  \A v1 \in Vers : v1 < v0 => Covers([s \in Sigils |-> EvB(v0 - 1, F0, XB, s)], v1)
<1> DEFINE EBf == [s \in Sigils |-> EvB(v0 - 1, F0, XB, s)]
<1> SUFFICES ASSUME NEW v1 \in Vers, v1 < v0 PROVE CoversV(EBf, v1, fr, sb, fz, mir)
    BY DEF Covers
<1>vn. v1 \in Nat /\ v0 \in Nat BY VersType
<1>sub. \A h \in F0 \cap Honest, s \in Sigils : sb[v0 - 1][h][s] \subseteq EBf[s] BY DEF EvB
<1>1. CASE v1 = v0 - 1
    <2>1. FrozeIntoV(EBf, v0 - 1, fr, sb) BY <1>sub DEF FrozeIntoV
    <2>. QED BY <1>1, <2>1 DEF CoversV
<1>2. CASE v1 < v0 - 1
    <2>1. PICK h0 \in F0 : h0 \in Honest BY QuorumHasHonest
    <2>2. h0 \in fr[v0 - 1] BY <2>1
    <2>3. v0 - 1 \in adv[h0] BY <2>1, <2>2 DEF Inv, FrozenAdv
    <2>4. CoversV(hev[v0 - 1][h0], v1, fr, sb, fz, mir) BY <2>1, <2>3, <1>2 DEF Inv, Lineage, Covers
    <2>5. \A s \in Sigils : hev[v0 - 1][h0][s] \subseteq sb[v0 - 1][h0][s] BY <2>1, <2>2 DEF Inv, SnapEv
    <2>6. \A s \in Sigils : hev[v0 - 1][h0][s] \subseteq EBf[s] BY <2>1, <2>5, <1>sub
    <2>. QED BY <2>4, <2>6, CoversMono
<1>. QED BY <1>vn, <1>1, <1>2

(* The evidence of a succession of v0-1 covers every earlier version: v0-1 *)
(* by the fenced committee quorum itself, older ones through the mirror log *)
(* of an honest member of that quorum (it entered standby with them).      *)
LEMMA EvMCovers ==
    ASSUME Inv, NEW v0 \in Vers, v0 >= 1, v0 - 1 \in Vers, NEW T0, NEW XB,
           HasSucc(v0 - 1), T0 \subseteq Committee[v0 - 1], Cardinality(T0) >= KQuorum[v0 - 1],
           T0 \cap Honest \subseteq fz[v0 - 1]
    PROVE  \A v1 \in Vers : v1 < v0 => Covers([s \in Sigils |-> EvM(v0 - 1, T0, XB, s)], v1)
<1> DEFINE EMf == [s \in Sigils |-> EvM(v0 - 1, T0, XB, s)]
<1> SUFFICES ASSUME NEW v1 \in Vers, v1 < v0 PROVE CoversV(EMf, v1, fr, sb, fz, mir)
    BY DEF Covers
<1>vn. v1 \in Nat /\ v0 \in Nat BY VersType
<1>sub. \A m \in T0 \cap Honest, s \in Sigils : mir[v0 - 1][m][s] \subseteq EMf[s] BY DEF EvM
<1>1. CASE v1 = v0 - 1
    <2>1. FencedIntoV(EMf, v0 - 1, fz, mir) BY <1>sub DEF FencedIntoV
    <2>. QED BY <1>1, <2>1 DEF CoversV
<1>2. CASE v1 < v0 - 1
    <2>1. PICK m0 \in T0 : m0 \in Honest BY KQuorumHasHonest
    <2>2. m0 \in sa[v0 - 1] BY <2>1 DEF Inv, FenceShape
    <2>3. CoversV(mir[v0 - 1][m0], v1, fr, sb, fz, mir) BY <2>1, <2>2, <1>2 DEF Inv, StandbyLin, Covers
    <2>4. \A s \in Sigils : mir[v0 - 1][m0][s] \subseteq EMf[s] BY <2>1, <1>sub
    <2>. QED BY <2>3, <2>4, CoversMono
<1>. QED BY <1>vn, <1>1, <1>2

(* ------------------------------------------- frame for the standby actions  *)
(* MIRROR, FENCE and STANDBY touch only the succession variables, which    *)
(* the rotation conjuncts never mention.                                   *)
LEMMA OldFrame ==
    ASSUME Inv, UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev>>
    PROVE  /\ VotesShape' /\ AdvShape' /\ NoEquiv' /\ ContestedSilent' /\ AbstBound'
           /\ OldVotes' /\ CurVote' /\ RelDisc' /\ LogOK' /\ LogDead' /\ SnapDead'
           /\ VoteLogged' /\ FrozenAdv' /\ FrozenStays' /\ SnapVotes' /\ EvLogged'
           /\ SnapEv' /\ VoteJust' /\ SealedNormal'
<1>1. /\ votes' = votes /\ act' = act /\ kv' = kv /\ adv' = adv /\ frz' = frz
      /\ gen' = gen /\ bnd' = bnd /\ cand' = cand /\ abst' = abst /\ lg' = lg /\ ld' = ld
      /\ fr' = fr /\ sb' = sb /\ sd' = sd /\ hev' = hev
    OBVIOUS
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv
      /\ VoteJust /\ SealedNormal
    BY DEF Inv
<1>dp. \A t : DeathProof(t)' <=> DeathProof(t) BY <1>1 DEF DeathProof
<1>hv. \A v, w, s, g, t : HV(v, w, s, g, t)' <=> HV(v, w, s, g, t) BY <1>1 DEF HV
<1>ns. \A s, g, t : NSealed(s, g, t)' <=> NSealed(s, g, t) BY <1>1 DEF NSealed
<1>nm. \A v, w, s, g, t : NormalVote(v, w, s, g, t)' <=> NormalVote(v, w, s, g, t)
    BY <1>1 DEF NormalVote
<1>sl. \A s, g, t : Sealed(s, g, t)' <=> Sealed(s, g, t) BY <1>1 DEF Sealed
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
<1>VJ. VoteJust' BY <1>hv, <1>nm, <1>ns, <1>i DEF VoteJust
<1>SN. SealedNormal' BY <1>sl, <1>ns, <1>i DEF SealedNormal
<1>. QED BY <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD, <1>SD,
            <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>VJ, <1>SN

(* ------------------------------------------- ADOPT after a ROTATION of v0-1 *)
LEMMA AdoptInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW v0, NEW F0, NEW XB, NEW XD, NEW XS, NEW NG,
           Adopt(w0, v0, F0, XB, XD, XS, NG)
    PROVE  Inv'
<1> DEFINE EBf == [s \in Sigils |-> EvB(v0 - 1, F0, XB, s)]
           EDf == [s \in Sigils |-> EvD(v0 - 1, F0, XD, s)]
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ F0 \subseteq Members[v0 - 1]
      /\ Cardinality(F0) >= Quorum[v0 - 1]
      /\ F0 \cap Honest \subseteq fr[v0 - 1]
      /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ XD \in [Sigils -> SUBSET Tids]
      /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
      /\ AdoptCore(w0, v0, EBf, EDf, XS, NG)
    BY DEF Adopt
<1>1. EBf \in [Sigils -> SUBSET (Nat \X Tids)] BY <1>a, EvBType
<1>2. /\ EDf \in [Sigils -> SUBSET Tids]
      /\ \A s \in Sigils : \A t \in EvD(v0 - 1, F0, XD, s) : t \in Tids /\ DeathProof(t)
    BY <1>a, EvDType
<1>3. \A s \in Sigils : \A t \in EDf[s] : DeathProof(t) BY <1>2
<1>4. \A v1 \in Vers : v1 < v0 => Covers(EBf, v1) BY <1>a, EvBCovers
<1>. QED BY <1>a, <1>1, <1>2, <1>3, <1>4, AdoptCoreInv

(* -------------------------------------- ADOPT after a SUCCESSION of v0-1 *)
LEMMA AdoptSInv ==
    ASSUME Inv, NEW w0 \in Honest, NEW v0, NEW T0, NEW XB, NEW XD, NEW XS, NEW NG,
           AdoptS(w0, v0, T0, XB, XD, XS, NG)
    PROVE  Inv'
<1> DEFINE EMf == [s \in Sigils |-> EvM(v0 - 1, T0, XB, s)]
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ HasSucc(v0 - 1)
      /\ T0 \subseteq Committee[v0 - 1]
      /\ Cardinality(T0) >= KQuorum[v0 - 1]
      /\ T0 \cap Honest \subseteq fz[v0 - 1]
      /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ XD \in [Sigils -> SUBSET Tids]
      /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
      /\ AdoptCore(w0, v0, EMf, XD, XS, NG)
    BY DEF AdoptS
<1>1. EMf \in [Sigils -> SUBSET (Nat \X Tids)] BY <1>a, EvMType
<1>2. \A v1 \in Vers : v1 < v0 => Covers(EMf, v1) BY <1>a, EvMCovers
<1>. QED BY <1>a, <1>1, <1>2, AdoptCoreInv

(* ------------------------------------------------------------- MIRROR  *)
LEMMA MirrorAckInv ==
    ASSUME Inv, NEW m0 \in Honest, NEW v0 \in Vers, NEW s0 \in Sigils, NEW b0 \in Nat \X Tids,
           MirrorAck(m0, v0, s0, b0)
    PROVE  Inv'
<1>i. /\ TypeOK /\ Lineage /\ FenceShape /\ MirVotes /\ StandbyLin BY DEF Inv
<1>a. m0 \in Committee[v0] /\ m0 \notin fz[v0] BY DEF MirrorAck
<1>post. /\ mir' = [mir EXCEPT ![v0][m0][s0] = @ \cup {b0}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, fz, sa>>
    BY DEF MirrorAck
<1>mir. \A v \in Vers, m \in Honest, s \in Sigils :
          mir'[v][m][s] = IF v = v0 /\ m = m0 /\ s = s0 THEN mir[v][m][s] \cup {b0} ELSE mir[v][m][s]
    BY <1>i, <1>post DEF TypeOK
<1>grow. \A v \in Vers, m \in Honest, s \in Sigils : mir[v][m][s] \subseteq mir'[v][m][s] BY <1>mir
<1>cf. \A E : \A v1 \in Vers : CoversV(E, v1, fr, sb, fz, mir) => CoversV(E, v1, fr', sb', fz', mir')
    <2> SUFFICES ASSUME NEW E, NEW v1 \in Vers, CoversV(E, v1, fr, sb, fz, mir)
                 PROVE  CoversV(E, v1, fr', sb', fz', mir')
        OBVIOUS
    <2>1. \A m \in Honest : m \in fz[v1] => \A s \in Sigils : mir'[v1][m][s] = mir[v1][m][s]
        BY <1>mir, <1>a
    <2>. QED BY <2>1, <1>post, CoversFrame
<1>old. /\ VotesShape' /\ AdvShape' /\ NoEquiv' /\ ContestedSilent' /\ AbstBound'
        /\ OldVotes' /\ CurVote' /\ RelDisc' /\ LogOK' /\ LogDead' /\ SnapDead'
        /\ VoteLogged' /\ FrozenAdv' /\ FrozenStays' /\ SnapVotes' /\ EvLogged'
        /\ SnapEv' /\ VoteJust' /\ SealedNormal'
    BY <1>post, OldFrame
<1>T. TypeOK'
    <2>1. mir' \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]] BY <1>i, <1>post DEF TypeOK
    <2>. QED BY <2>1, <1>i, <1>post DEF TypeOK
<1>LI. Lineage'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv'[w], v1 < v2
                 PROVE  CoversV(hev'[v2][w], v1, fr', sb', fz', mir')
        BY DEF Lineage, Covers
    <2>1. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF Lineage, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v \in Vers, NEW s \in Sigils, NEW g \in Nat,
                        NEW t \in Tids, HV(v, w, s, g, t)', HasSucc(v)
                 PROVE  MirQV(mir', v, s, g, t)
        BY DEF MirVotes, MirQ
    <2>1. MirQV(mir, v, s, g, t) BY <1>i, <1>post DEF MirVotes, MirQ, HV
    <2>2. \A m \in Honest : <<g, t>> \in mir[v][m][s] => <<g, t>> \in mir'[v][m][s] BY <1>grow
    <2>. QED BY <2>1, <2>2, MirQMono
<1>SY. StandbyLin'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW m \in Honest, NEW v1 \in Vers, m \in sa'[v], v1 < v
                 PROVE  CoversV(mir'[v][m], v1, fr', sb', fz', mir')
        BY DEF StandbyLin, Covers
    <2>1. CoversV(mir[v][m], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF StandbyLin, Covers
    <2>2. \A s \in Sigils : mir[v][m][s] \subseteq mir'[v][m][s] BY <1>grow
    <2>3. CoversV(mir'[v][m], v1, fr, sb, fz, mir) BY <2>1, <2>2, CoversMono
    <2>. QED BY <2>3, <1>cf
<1>. QED BY <1>old, <1>T, <1>LI, <1>FN, <1>MV, <1>SY DEF Inv

(* ------------------------------------------------------------- FENCE  *)
LEMMA FenceInv ==
    ASSUME Inv, NEW m0 \in Honest, NEW v0 \in Vers, Fence(m0, v0)
    PROVE  Inv'
<1>i. /\ TypeOK /\ Lineage /\ FenceShape /\ MirVotes /\ StandbyLin BY DEF Inv
<1>a. m0 \in Committee[v0] /\ m0 \in sa[v0] BY DEF Fence
<1>post. /\ fz' = [fz EXCEPT ![v0] = @ \cup {m0}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, mir, sa>>
    BY DEF Fence
<1>fz. \A v \in Vers : fz'[v] = IF v = v0 THEN fz[v] \cup {m0} ELSE fz[v] BY <1>i, <1>post DEF TypeOK
<1>cf. \A E : \A v1 \in Vers : CoversV(E, v1, fr, sb, fz, mir) => CoversV(E, v1, fr', sb', fz', mir')
    <2> SUFFICES ASSUME NEW E, NEW v1 \in Vers, CoversV(E, v1, fr, sb, fz, mir)
                 PROVE  CoversV(E, v1, fr', sb', fz', mir')
        OBVIOUS
    <2>1. fz[v1] \subseteq fz'[v1] BY <1>fz
    <2>. QED BY <2>1, <1>post, CoversFrame
<1>old. /\ VotesShape' /\ AdvShape' /\ NoEquiv' /\ ContestedSilent' /\ AbstBound'
        /\ OldVotes' /\ CurVote' /\ RelDisc' /\ LogOK' /\ LogDead' /\ SnapDead'
        /\ VoteLogged' /\ FrozenAdv' /\ FrozenStays' /\ SnapVotes' /\ EvLogged'
        /\ SnapEv' /\ VoteJust' /\ SealedNormal'
    BY <1>post, OldFrame
<1>T. TypeOK'
    <2>1. fz' \in [Vers -> SUBSET Honest] BY <1>i, <1>post DEF TypeOK
    <2>. QED BY <2>1, <1>i, <1>post DEF TypeOK
<1>LI. Lineage'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv'[w], v1 < v2
                 PROVE  CoversV(hev'[v2][w], v1, fr', sb', fz', mir')
        BY DEF Lineage, Covers
    <2>1. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF Lineage, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>FN. FenceShape'
    <2> SUFFICES ASSUME NEW v \in Vers PROVE fz'[v] \subseteq sa'[v] BY DEF FenceShape
    <2>. QED BY <1>fz, <1>a, <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>post DEF MirVotes, MirQ, HV
<1>SY. StandbyLin'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW m \in Honest, NEW v1 \in Vers, m \in sa'[v], v1 < v
                 PROVE  CoversV(mir'[v][m], v1, fr', sb', fz', mir')
        BY DEF StandbyLin, Covers
    <2>1. CoversV(mir[v][m], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF StandbyLin, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>. QED BY <1>old, <1>T, <1>LI, <1>FN, <1>MV, <1>SY DEF Inv

(* ------------------------------------------------------------ STANDBY  *)
(* Entering standby with evidence E that covers every earlier version.    *)
LEMMA StandbyCoreInv ==
    ASSUME Inv, NEW m0 \in Honest, NEW v0 \in Vers, NEW E, StandbyCore(m0, v0, E),
           E \in [Sigils -> SUBSET (Nat \X Tids)],
           \A v1 \in Vers : v1 < v0 => Covers(E, v1)
    PROVE  Inv'
<1>i. /\ TypeOK /\ Lineage /\ FenceShape /\ MirVotes /\ StandbyLin BY DEF Inv
<1>a. m0 \in Committee[v0] /\ m0 \notin sa[v0] BY DEF StandbyCore
<1>post. /\ mir' = [mir EXCEPT ![v0][m0] = [s \in Sigils |-> mir[v0][m0][s] \cup E[s]]]
         /\ sa'  = [sa  EXCEPT ![v0] = @ \cup {m0}]
         /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, fz>>
    BY DEF StandbyCore
<1>nf. m0 \notin fz[v0] BY <1>a, <1>i DEF FenceShape
<1>mir. \A v \in Vers, m \in Honest, s \in Sigils :
          mir'[v][m][s] = IF v = v0 /\ m = m0 THEN mir[v][m][s] \cup E[s] ELSE mir[v][m][s]
    BY <1>i, <1>post DEF TypeOK
<1>sa. \A v \in Vers : sa'[v] = IF v = v0 THEN sa[v] \cup {m0} ELSE sa[v] BY <1>i, <1>post DEF TypeOK
<1>grow. \A v \in Vers, m \in Honest, s \in Sigils : mir[v][m][s] \subseteq mir'[v][m][s] BY <1>mir
<1>cf. \A E2 : \A v1 \in Vers : CoversV(E2, v1, fr, sb, fz, mir) => CoversV(E2, v1, fr', sb', fz', mir')
    <2> SUFFICES ASSUME NEW E2, NEW v1 \in Vers, CoversV(E2, v1, fr, sb, fz, mir)
                 PROVE  CoversV(E2, v1, fr', sb', fz', mir')
        OBVIOUS
    <2>1. \A m \in Honest : m \in fz[v1] => \A s \in Sigils : mir'[v1][m][s] = mir[v1][m][s]
        BY <1>mir, <1>nf
    <2>. QED BY <2>1, <1>post, CoversFrame
<1>old. /\ VotesShape' /\ AdvShape' /\ NoEquiv' /\ ContestedSilent' /\ AbstBound'
        /\ OldVotes' /\ CurVote' /\ RelDisc' /\ LogOK' /\ LogDead' /\ SnapDead'
        /\ VoteLogged' /\ FrozenAdv' /\ FrozenStays' /\ SnapVotes' /\ EvLogged'
        /\ SnapEv' /\ VoteJust' /\ SealedNormal'
    BY <1>post, OldFrame
<1>T. TypeOK'
    <2>1. mir' \in [Vers -> [Honest -> [Sigils -> SUBSET (Nat \X Tids)]]] BY <1>i, <1>post DEF TypeOK
    <2>2. sa' \in [Vers -> SUBSET Honest] BY <1>i, <1>post DEF TypeOK
    <2>. QED BY <2>1, <2>2, <1>i, <1>post DEF TypeOK
<1>LI. Lineage'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v2 \in Vers, NEW v1 \in Vers, v2 \in adv'[w], v1 < v2
                 PROVE  CoversV(hev'[v2][w], v1, fr', sb', fz', mir')
        BY DEF Lineage, Covers
    <2>1. CoversV(hev[v2][w], v1, fr, sb, fz, mir) BY <1>i, <1>post DEF Lineage, Covers
    <2>. QED BY <2>1, <1>cf, <1>post
<1>FN. FenceShape' BY <1>sa, <1>i, <1>post DEF FenceShape
<1>MV. MirVotes'
    <2> SUFFICES ASSUME NEW w \in Honest, NEW v \in Vers, NEW s \in Sigils, NEW g \in Nat,
                        NEW t \in Tids, HV(v, w, s, g, t)', HasSucc(v)
                 PROVE  MirQV(mir', v, s, g, t)
        BY DEF MirVotes, MirQ
    <2>1. MirQV(mir, v, s, g, t) BY <1>i, <1>post DEF MirVotes, MirQ, HV
    <2>2. \A m \in Honest : <<g, t>> \in mir[v][m][s] => <<g, t>> \in mir'[v][m][s] BY <1>grow
    <2>. QED BY <2>1, <2>2, MirQMono
<1>SY. StandbyLin'
    <2> SUFFICES ASSUME NEW v \in Vers, NEW m \in Honest, NEW v1 \in Vers, m \in sa'[v], v1 < v
                 PROVE  CoversV(mir'[v][m], v1, fr', sb', fz', mir')
        BY DEF StandbyLin, Covers
    <2>1. CASE v = v0 /\ m = m0
        <3>1. CoversV(E, v1, fr, sb, fz, mir) BY <2>1 DEF Covers
        <3>2. \A s \in Sigils : E[s] \subseteq mir'[v][m][s] BY <2>1, <1>mir
        <3>3. CoversV(mir'[v][m], v1, fr, sb, fz, mir) BY <3>1, <3>2, CoversMono
        <3>. QED BY <3>3, <1>cf
    <2>2. CASE ~(v = v0 /\ m = m0)
        <3>1. m \in sa[v] BY <2>2, <1>sa
        <3>2. CoversV(mir[v][m], v1, fr, sb, fz, mir) BY <3>1, <1>i DEF StandbyLin, Covers
        <3>3. \A s \in Sigils : mir[v][m][s] \subseteq mir'[v][m][s] BY <1>grow
        <3>4. CoversV(mir'[v][m], v1, fr, sb, fz, mir) BY <3>2, <3>3, CoversMono
        <3>. QED BY <3>4, <1>cf
    <2>. QED BY <2>1, <2>2
<1>. QED BY <1>old, <1>T, <1>LI, <1>FN, <1>MV, <1>SY DEF Inv

LEMMA Standby0Inv ==
    ASSUME Inv, NEW m0 \in Honest, NEW XB, Standby0(m0, XB)
    PROVE  Inv'
<1>a. 0 \in Vers /\ XB \in [Sigils -> SUBSET (Nat \X Tids)] /\ StandbyCore(m0, 0, XB) BY DEF Standby0
<1>1. \A v1 \in Vers : v1 < 0 => Covers(XB, v1) BY VersType
<1>. QED BY <1>a, <1>1, StandbyCoreInv

LEMMA StandbyRInv ==
    ASSUME Inv, NEW m0 \in Honest, NEW v0, NEW F0, NEW XB, StandbyR(m0, v0, F0, XB)
    PROVE  Inv'
<1> DEFINE EBf == [s \in Sigils |-> EvB(v0 - 1, F0, XB, s)]
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ F0 \subseteq Members[v0 - 1]
      /\ Cardinality(F0) >= Quorum[v0 - 1]
      /\ F0 \cap Honest \subseteq fr[v0 - 1]
      /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ StandbyCore(m0, v0, EBf)
    BY DEF StandbyR
<1>1. EBf \in [Sigils -> SUBSET (Nat \X Tids)] BY <1>a, EvBType
<1>2. \A v1 \in Vers : v1 < v0 => Covers(EBf, v1) BY <1>a, EvBCovers
<1>. QED BY <1>a, <1>1, <1>2, StandbyCoreInv

LEMMA StandbySInv ==
    ASSUME Inv, NEW m0 \in Honest, NEW v0, NEW T0, NEW XB, StandbyS(m0, v0, T0, XB)
    PROVE  Inv'
<1> DEFINE EMf == [s \in Sigils |-> EvM(v0 - 1, T0, XB, s)]
<1>a. /\ v0 \in Vers /\ v0 >= 1 /\ v0 - 1 \in Vers
      /\ HasSucc(v0 - 1)
      /\ T0 \subseteq Committee[v0 - 1]
      /\ Cardinality(T0) >= KQuorum[v0 - 1]
      /\ T0 \cap Honest \subseteq fz[v0 - 1]
      /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
      /\ StandbyCore(m0, v0, EMf)
    BY DEF StandbyS
<1>1. EMf \in [Sigils -> SUBSET (Nat \X Tids)] BY <1>a, EvMType
<1>2. \A v1 \in Vers : v1 < v0 => Covers(EMf, v1) BY <1>a, EvMCovers
<1>. QED BY <1>a, <1>1, <1>2, StandbyCoreInv

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
      /\ FenceShape /\ MirVotes /\ StandbyLin
    BY DEF Inv
<1>post. /\ votes' = votes \cup {bv}
         /\ UNCHANGED <<act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, mir, fz, sa>>
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
<1>LI. Lineage' BY <1>i, <1>post DEF Lineage, Covers
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
<1>FN. FenceShape' BY <1>i, <1>post DEF FenceShape
<1>MV. MirVotes' BY <1>i, <1>hv, <1>post DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>i, <1>post DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

(* ------------------------------------------------------------ stuttering *)
LEMMA StutterInv ==
    ASSUME Inv, UNCHANGED vars
    PROVE  Inv'
<1>1. /\ votes' = votes /\ act' = act /\ kv' = kv /\ adv' = adv /\ frz' = frz
      /\ gen' = gen /\ bnd' = bnd /\ cand' = cand /\ abst' = abst /\ lg' = lg /\ ld' = ld
      /\ fr' = fr /\ sb' = sb /\ sd' = sd /\ hev' = hev
      /\ mir' = mir /\ fz' = fz /\ sa' = sa
    BY DEF vars
<1>i. /\ TypeOK /\ VotesShape /\ AdvShape /\ NoEquiv /\ ContestedSilent /\ AbstBound
      /\ OldVotes /\ CurVote /\ RelDisc /\ LogOK /\ LogDead /\ SnapDead /\ VoteLogged
      /\ FrozenAdv /\ FrozenStays /\ SnapVotes /\ EvLogged /\ SnapEv /\ Lineage
      /\ VoteJust /\ SealedNormal
      /\ FenceShape /\ MirVotes /\ StandbyLin
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
<1>LI. Lineage' BY <1>1, <1>i DEF Lineage, Covers
<1>VJ. VoteJust' BY <1>hv, <1>nm, <1>ns, <1>i DEF VoteJust
<1>SN. SealedNormal' BY <1>sl, <1>ns, <1>i DEF SealedNormal
<1>FN. FenceShape' BY <1>1, <1>i DEF FenceShape
<1>MV. MirVotes' BY <1>1, <1>hv, <1>i DEF MirVotes, MirQ
<1>SY. StandbyLin' BY <1>1, <1>i DEF StandbyLin, Covers
<1>. QED BY <1>T, <1>VS, <1>AS, <1>NE, <1>CS, <1>AB, <1>OV, <1>CV, <1>RD, <1>LO, <1>LD,
            <1>SD, <1>VL, <1>FA, <1>FS, <1>SV, <1>EL, <1>SE, <1>LI, <1>VJ, <1>SN,
            <1>FN, <1>MV, <1>SY DEF Inv

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
<1>7. CASE \E w \in Honest, v \in Vers, T \in SUBSET Witnesses,
              XB \in ForgeBinds, XD \in ForgeDead, XS \in ForgeSeals, NG \in [Sigils -> Nat] :
                AdoptS(w, v, T, XB, XD, XS, NG)
    BY <1>7, AdoptSInv
<1>8. CASE \E m \in Honest, v \in Vers, s \in Sigils, b \in Nat \X Tids : MirrorAck(m, v, s, b)
    BY <1>8, MirrorAckInv
<1>9. CASE \E m \in Honest, v \in Vers : Fence(m, v)
    BY <1>9, FenceInv
<1>10. CASE \E m \in Honest, XB \in ForgeBinds : Standby0(m, XB)
    BY <1>10, Standby0Inv
<1>11. CASE \E m \in Honest, v \in Vers, F \in SUBSET Witnesses, XB \in ForgeBinds : StandbyR(m, v, F, XB)
    BY <1>11, StandbyRInv
<1>12. CASE \E m \in Honest, v \in Vers, T \in SUBSET Witnesses, XB \in ForgeBinds : StandbyS(m, v, T, XB)
    BY <1>12, StandbySInv
<1>13. CASE \E b \in Byz, v \in Vers, s \in Sigils, g \in Nat, t \in Tids : ByzVote(b, v, s, g, t)
    BY <1>13, ByzVoteInv
<1>14. CASE UNCHANGED vars
    BY <1>14, StutterInv
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12,
            <1>13, <1>14 DEF Next, HonestNext

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

(* SPEC 5.5: the committee is the one authority over the successor of a    *)
(* version with a committee.  An honest standby member of v signs at most  *)
(* one successor, succ[h] (it fences for it); Byzantine members may sign   *)
(* anything.  Two different successors then never both collect a quorum  *)
(* of the committee's signatures (the validity condition of SPEC 3.7 for  *)
(* a version with a committee), so the charter chain -- the constants     *)
(* Members and Committee -- is the only one a holder can verify, whether   *)
(* the next version came from a rotation or a succession.                 *)
THEOREM OneSuccessorK ==
    ASSUME NEW v \in Vers, HasSucc(v), NEW succ, NEW S1, NEW S2, S1 # S2,
           NEW Q1, NEW Q2, Q1 \subseteq Committee[v], Q2 \subseteq Committee[v],
           Cardinality(Q1) >= KQuorum[v], Cardinality(Q2) >= KQuorum[v],
           \A h \in Q1 \cap Honest : succ[h] = S1,
           \A h \in Q2 \cap Honest : succ[h] = S2
    PROVE  FALSE
<1>1. PICK h \in Q1 \cap Q2 : h \in Honest BY HonestInBothKQuorums
<1>. QED BY <1>1
================================================================================
