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

=============================================================================
