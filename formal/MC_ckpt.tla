------------------------------- MODULE MC_ckpt -------------------------------
(* Compaction (SPEC Section 5.7, docs/COMPACTION.md): settlement and charter *)
(* checkpoints on top of the PROVED rotation spec (SigilRotProofs.tla, via   *)
(* its TLC instance module MC_rotp.tla), over THREE charter versions so that *)
(* a checkpoint is carried through a second rotation (configs MC_ckpt*.cfg). *)
(*                                                                         *)
(* What is added to the rotation spec:                                      *)
(*   * Settle(w, s, t): an honest witness shown a settlement certificate     *)
(*     (SPEC 3.12: t is COMPLETE, every input sealed) marks its record of s  *)
(*     settled at <<GenOf(t, s), t>>.  A settled record never votes, never  *)
(*     releases and never takes part in a contested release (the rotation   *)
(*     spec's actions are guarded by Free(w, s)); it keeps its log.         *)
(*   * Charter(v, S): whoever drives the rotation fixes version v's charter, *)
(*     including its checkpoint set S (any set of input entries, one per     *)
(*     sigil): the driver is adversarial.                                   *)
(*   * CFreeze(w): an honest member of v freezes for charter v+1 only if     *)
(*     FreezeOK (SPEC 5.7: every entry of S matches a settled record, and   *)
(*     every checkpointed record is in S -- the extension rule), and its    *)
(*     snapshot omits the sigils in S.                                      *)
(*   * CAdopt: as Adopt, but every sigil in S becomes a checkpointed record *)
(*     (settled at the entry, no log) whatever the snapshots say.           *)
(*                                                                         *)
(* Mutations (each must be caught):                                        *)
(*   CkAdoptRec <- CkForget        the adopter forgets checkpointed sigils  *)
(*                                 (treats them as fresh): double spend     *)
(*   FreezeOK   <- FreezeNoExtend  no extension rule: a checkpointed sigil  *)
(*                                 is dropped by the next charter and its   *)
(*                                 (empty) log handed over: double spend    *)
(*   FreezeOK   <- FreezeNoCheck   freezers do not check S against their    *)
(*                                 settled records: CkSound (liveness of    *)
(*                                 owners: S names only complete tids)      *)
(*   SettleOK   <- SettleSealOnly  settle on one input's seal, not a        *)
(*                                 completion certificate: CkSound          *)
EXTENDS MC_rotp

CONSTANT M2     \* members of version 2

VARIABLES
    stl,    \* stl[w][s] : <<g, t>> if w's record of s is settled (or checkpointed), else NoS
    ckd,    \* ckd[w][s] : w's record of s came from a checkpoint (it has no log)
    ck,     \* ck[v]     : the checkpoint set of version v's charter
    chd     \* chd[v]    : version v's charter body has been fixed

cvars == <<vars, stl, ckd, ck, chd>>

NoS == <<>>

CkVers    == {0, 1, 2}
CkMembers == [v \in CkVers |-> CASE v = 0 -> M0 [] v = 1 -> M1 [] OTHER -> M2]
CkQuorum  == [v \in CkVers |-> Cardinality(CkMembers[v]) - (Cardinality(CkMembers[v]) - 1) \div 3]

Dom(S) == { e[1] : e \in S }
Entry(S, s) == CHOOSE e \in S : e[1] = s
Functional(S) == \A e1, e2 \in S : e1[1] = e2[1] => e1 = e2
\* The checkpoint sets a driver can offer: input entries <<s, g, t>> of real
\* transitions, one per sigil (SPEC 3.7).
InputEntries == UNION { { <<p[1], p[2], t>> : p \in Header[t] } : t \in Tids }
CkChoices == { S \in SUBSET InputEntries : Functional(S) }

Free(w, s) == stl[w][s] = NoS

\* Smaller transition sets (Hdr, TidsSib: MC_rotp.tla).
\*   TidsDS: Ta = {(s,0)} and Tg = {(s,1)}: a consumed sigil and its re-spend.
\*   TidsKS: Tb = {(s,0),(x,0)} and Ty = {(x,0)}: Tb sealed at s, killed through x.
SigilsS == {"s"}
TidsDS == {"Ta", "Tg"}
HdrDS  == [t \in TidsDS |-> Hdr(t)]
\*   TidsDX: TidsDS and Ty = {(x,0)}, which later versions can still seal.
TidsDX == {"Ta", "Tg", "Ty"}
HdrDX  == [t \in TidsDX |-> Hdr(t)]
TidsKS == {"Tb", "Ty"}
HdrKS  == [t \in TidsKS |-> Hdr(t)]

\* ---- The rules (overridden by the mutants) ----
\* SPEC 5.7 SETTLE: the certificate shows t complete.
SettleOK(s, t) == Complete(t)
SettleSealOnly(s, t) == Sealed(s, GenOf(t, s), t)
\* SPEC 5.7, rules for signers: (1) every entry matches a settled record;
\* (2) every checkpointed record is in S (extension rule).
FreezeOK(w, S) ==
    /\ \A e \in S : stl[w][e[1]] = <<e[2], e[3]>>
    /\ \A s \in Sigils : ckd[w][s] => s \in Dom(S)
FreezeNoExtend(w, S) == \A e \in S : stl[w][e[1]] = <<e[2], e[3]>>
FreezeNoCheck(w, S)  == \A s \in Sigils : ckd[w][s] => s \in Dom(S)
\* SPEC 5.4 ADOPT of a checkpoint entry: a checkpointed record.
CkAdoptRec(S, s) == [g |-> Entry(S, s)[2], t |-> Entry(S, s)[3], c |-> {}, a |-> FALSE, keep |-> TRUE]
CkForget(S, s)   == [g |-> 0, t |-> NoTid, c |-> {}, a |-> FALSE, keep |-> FALSE]

-----------------------------------------------------------------------------
CInit ==
    /\ MCInit
    /\ stl = [w \in Honest |-> [s \in Sigils |-> NoS]]
    /\ ckd = [w \in Honest |-> [s \in Sigils |-> FALSE]]
    /\ ck  = [v \in CkVers |-> {}]
    /\ chd = [v \in CkVers |-> v = 0]

Keep == <<stl, ckd, ck, chd>>

CSpend(w, s, t)               == Free(w, s) /\ Spend(w, s, t) /\ UNCHANGED Keep
CRelease(w, s)                == Free(w, s) /\ Release(w, s) /\ UNCHANGED Keep
\* The generation is the one sigil/witness.py picks (MCCandGenOK / MCGenOK are
\* equalities), computed here instead of enumerated, for speed.
CandGen(w, s, c) == Max({gen[w][s], c[1] + 1} \cup
                        (IF cand[w][s] \ {c} = {} THEN { o[1] + 1 : o \in Own(w, s) } ELSE {}))
CReleaseCand(w, s, c)         == Free(w, s) /\ ReleaseCand(w, s, c, CandGen(w, s, c)) /\ UNCHANGED Keep
CResolveContested(w, s, b)    == Free(w, s) /\ ResolveContested(w, s, b) /\ UNCHANGED Keep

Settle(w, s, t) ==
    /\ act[w] /\ ~frz[w]
    /\ Free(w, s)
    /\ s \in SigilsOf(t)
    /\ SettleOK(s, t)
    /\ stl' = [stl EXCEPT ![w][s] = <<GenOf(t, s), t>>]
    /\ UNCHANGED <<vars, ckd, ck, chd>>

Charter(v, S) ==
    /\ v \in CkVers /\ v >= 1 /\ ~chd[v]
    /\ S \in CkChoices
    /\ chd' = [chd EXCEPT ![v] = TRUE]
    /\ ck'  = [ck  EXCEPT ![v] = S]
    /\ UNCHANGED <<vars, stl, ckd>>

CFreeze(w) ==
    /\ act[w] /\ ~frz[w]
    /\ kv[w] + 1 \in CkVers
    /\ chd[kv[w] + 1]
    /\ FreezeOK(w, ck[kv[w] + 1])
    /\ frz' = [frz EXCEPT ![w] = TRUE]
    /\ fr'  = [fr  EXCEPT ![kv[w]] = @ \cup {w}]
    /\ sb'  = [sb  EXCEPT ![kv[w]][w] =
                  [s \in Sigils |-> IF s \in Dom(ck[kv[w] + 1]) THEN {} ELSE lg[w][s]]]
    /\ sd'  = [sd  EXCEPT ![kv[w]][w] =
                  [s \in Sigils |-> IF s \in Dom(ck[kv[w] + 1]) THEN {} ELSE ld[w][s]]]
    /\ UNCHANGED <<votes, act, kv, adv, gen, bnd, cand, abst, lg, ld, hev, stl, ckd, ck, chd>>

\* The generation ADOPT gives a contested or unbound record (MCGenOK).
NGen(w, v, F, XB, XD) == [s \in Sigils |-> IF s \in Dom(ck[v]) THEN 0
                            ELSE AdoptGen(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), Own(w, s))]

\* The record CAdopt gives sigil s: a checkpoint entry, or the proved rule.
CRec(w, v, F, XB, XD, XS, NG, s) ==
    IF s \in Dom(ck[v]) THEN CkAdoptRec(ck[v], s)
    ELSE LET r == NewRec(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), XS[s], Own(w, s), NG[s])
         IN [g |-> r.g, t |-> r.t, c |-> r.c, a |-> r.a, keep |-> FALSE]

CAdopt(w, v, F, XB, XD, XS) == LET NG == NGen(w, v, F, XB, XD) IN
    /\ v \in CkVers /\ v >= 1 /\ chd[v]
    /\ w \in CkMembers[v]
    /\ act[w] => kv[w] < v
    /\ F \subseteq CkMembers[v - 1]
    /\ Cardinality(F) >= CkQuorum[v - 1]
    /\ F \cap Honest \subseteq fr[v - 1]
    /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    /\ \A s \in Sigils : \A b \in XS[s] : Sealed(s, b[1], b[2])
    /\ \A s \in Sigils :
          IF s \in Dom(ck[v]) THEN NG[s] = 0
          ELSE GenOK(EvB(v - 1, F, XB, s), EvD(v - 1, F, XD, s), Own(w, s), NG[s])
    /\ gen'  = [gen  EXCEPT ![w] = [s \in Sigils |-> CRec(w, v, F, XB, XD, XS, NG, s).g]]
    /\ bnd'  = [bnd  EXCEPT ![w] = [s \in Sigils |-> CRec(w, v, F, XB, XD, XS, NG, s).t]]
    /\ cand' = [cand EXCEPT ![w] = [s \in Sigils |-> CRec(w, v, F, XB, XD, XS, NG, s).c]]
    /\ abst' = [abst EXCEPT ![w] = [s \in Sigils |-> CRec(w, v, F, XB, XD, XS, NG, s).a]]
    /\ lg'   = [lg   EXCEPT ![w] = [s \in Sigils |->
                    IF s \in Dom(ck[v]) THEN {} ELSE EvB(v - 1, F, XB, s)]]
    /\ ld'   = [ld   EXCEPT ![w] = [s \in Sigils |->
                    IF s \in Dom(ck[v]) THEN {} ELSE EvD(v - 1, F, XD, s)]]
    /\ hev'  = [hev  EXCEPT ![v][w] = [s \in Sigils |->
                    IF s \in Dom(ck[v]) THEN {} ELSE EvB(v - 1, F, XB, s)]]
    /\ stl'  = [stl  EXCEPT ![w] = [s \in Sigils |->
                    IF CRec(w, v, F, XB, XD, XS, NG, s).keep
                    THEN <<CRec(w, v, F, XB, XD, XS, NG, s).g, CRec(w, v, F, XB, XD, XS, NG, s).t>>
                    ELSE NoS]]
    /\ ckd'  = [ckd  EXCEPT ![w] = [s \in Sigils |-> CRec(w, v, F, XB, XD, XS, NG, s).keep]]
    /\ act'  = [act  EXCEPT ![w] = TRUE]
    /\ kv'   = [kv   EXCEPT ![w] = v]
    /\ adv'  = [adv  EXCEPT ![w] = @ \cup {v}]
    /\ frz'  = [frz  EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<votes, fr, sb, sd, ck, chd>>

CNext ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : CSpend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : CRelease(w, s)
    \/ \E w \in Honest, s \in Sigils, c \in G \X Tids : CReleaseCand(w, s, c)
    \/ \E w \in Honest, s \in Sigils, b \in G \X Tids : CResolveContested(w, s, b)
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Settle(w, s, t)
    \/ \E v \in CkVers, S \in CkChoices : Charter(v, S)
    \/ \E w \in Honest : CFreeze(w)
    \/ \E w \in Honest, v \in CkVers \ {0} :
          \E F \in SUBSET CkMembers[v - 1], XB \in ForgeBinds, XD \in ForgeDead, XS \in ForgeSeals :
            CAdopt(w, v, F, XB, XD, XS)

\* Byzantine votes are eager (MCInit, as MCSpec), for every version.
CSpec == CInit /\ [][CNext]_cvars

-----------------------------------------------------------------------------
\* Liveness of owners, as an invariant: a checkpoint that some version adopted
\* names only sigils whose transition is complete (so nothing it freezes could
\* ever have been released).
CkSound ==
    \A v \in CkVers :
        (v >= 1 /\ \E w \in Honest : v \in adv[w]) => \A e \in ck[v] : Complete(e[3])

\* ---- Non-vacuity probes (each must be VIOLATED, MC_ckpt_witness*.cfg) ----
\* A checkpointed record reaches version 2 (carried through two rotations).
NoCheckpointAtV2 == ~(\E w \in Honest : kv[w] = 2 /\ \E s \in Sigils : ckd[w][s])
\* ... while version 2 still works: it seals some transition.
NoCheckpointAndProgress ==
    ~(  (\E w \in Honest : kv[w] = 2 /\ \E s \in Sigils : ckd[w][s])
     /\ (\E s \in Sigils, g \in G, t \in Tids : SealedIn(2, s, g, t)))
=============================================================================
