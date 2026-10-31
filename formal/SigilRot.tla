------------------------------- MODULE SigilRot -------------------------------
(* Charter rotation: FREEZE / ADOPT with evidence logs, the contested state, *)
(* own-vote abstention and re-used keys (SPEC Section 5.4), over TWO charter  *)
(* versions of one home constellation.                                       *)
(*                                                                         *)
(* This is the model the single-version proof (formal/SigilProofs.tla) does  *)
(* NOT cover.  It reproduces a real double-spend in the reference ADOPT and  *)
(* shows the one-line fix removes it.                                        *)
(*                                                                         *)
(* Version 0 members: Honest0 + {Z} (n=4, q=3, f=1).  A quorum of v0 freezes *)
(* and signs v1; v1 members: Honest1 + {Z} (fresh honest keys, Byzantine key *)
(* re-used).  Each new honest witness ADOPTs the union of the freezing        *)
(* quorum's honest logs.  Seals count votes of EITHER version (holders accept *)
(* a seal from any version, SPEC 6.4), so a v0 seal and a v1 seal both bind.  *)
(*                                                                         *)
(* The reference ADOPT keeps every alive binding; with FloorGuard = FALSE    *)
(* (the current code) a surviving same-generation sibling of a sealed-then-   *)
(* dead binding re-opens that generation, and TLC finds the double-spend.    *)
(* With FloorGuard = TRUE (the proposed fix) an alive binding below the floor *)
(* is dropped, and TLC finds no violation.                                   *)
(*                                                                         *)
(* Abstractions, as in Sigil.tla: cryptography is identifiers; the owner is  *)
(* adversarial (every spend request may reach any honest witness); votes are *)
(* public and monotone; the Byzantine witness may sign any vote for itself.  *)
(* The freezing quorum's honest logs are faithful (a lying predecessor only  *)
(* omits, which the union of an honest quorum covers -- the forged-snapshot   *)
(* case is exercised by the Python explorer, tests/test_model_check_ext...). *)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Honest0, Honest1,   \* honest witnesses of v0 and v1 (disjoint, fresh keys)
    Z,                  \* the Byzantine witness (its key is re-used in v1)
    Sigils, Home,       \* sigils and their home (the single constellation "C")
    Tids, Header,       \* transitions and their input sets
    MaxGen,
    AdoptMode           \* "real": the current SPEC 5.4 / witness.py ADOPT
                        \* "sealaware": idealised fix (ADOPT reads v0 SEALS directly)
                        \* "sibling": the implemented fix (a same-generation
                        \*   sibling makes the sigil CONTESTED; it is released
                        \*   once every live candidate is proven dead)

Q == 3
NoTid == "none"
CONTESTED == "!contested"
Gens == 0..MaxGen

Members(v) == IF v = 0 THEN Honest0 \cup {Z} ELSE Honest1 \cup {Z}
HonestV(v) == IF v = 0 THEN Honest0 ELSE Honest1
AllHonest  == Honest0 \cup Honest1

ASSUME Honest0 \cap Honest1 = {}
ASSUME Z \notin AllHonest
ASSUME Cardinality(Honest0 \cup {Z}) = 4 /\ Cardinality(Honest1 \cup {Z}) = 4
ASSUME NoTid \notin Tids /\ CONTESTED \notin Tids
ASSUME Home \in [Sigils -> {"C"}]

SigilsOf(t) == { p[1] : p \in Header[t] }
GenOf(t, s) == CHOOSE g \in Gens : <<s, g>> \in Header[t]

VARIABLES
    ver,        \* current active version: 0, then 1 after rotation
    gen, bound, \* gen[v][w][s], bound[v][w][s] for honest w of version v
    votes,      \* set of <<v, w, s, g, t>> : every vote ever cast (both versions)
    binds,      \* binds[s] : set of <<g,t>> ever bound by an honest v0 witness (log union)
    rel,        \* rel[s]   : set of tids an honest v0 witness released (death-proof-backed)
    adopted,    \* TRUE once v1 has adopted
    cand        \* cand[v][w][s] : live <<g,t>> candidates of a CONTESTED record

vars == <<ver, gen, bound, votes, binds, rel, adopted, cand>>

Vote(v, w, s, g, t) == <<v, w, s, g, t>>

\* Members of version v that voted t at (s,g); a seal needs Q of them.
Voters(v, s, g, t) == { w \in Members(v) : Vote(v, w, s, g, t) \in votes }
SealedIn(v, s, g, t) == Cardinality(Voters(v, s, g, t)) >= Q
\* Holders accept a seal from ANY version of the home (SPEC 6.4).
Sealed(s, g, t) == \E v \in {0, 1} : SealedIn(v, s, g, t)
Complete(t) == \A p \in Header[t] : Sealed(p[1], p[2], t)

\* A death proof for t exists if some input (s,g) of t is sealed to another
\* tid, or a single charter version has Q votes against t at (s,g).  The
\* evidence must come from ONE version's quorum (SPEC 3.9 / proves_dead):
\* votes are NOT pooled across versions.  Home-only: this one constellation.
VotersAgainst(v, s, g, t) ==
    { w \in Members(v) : \E u \in Tids : u # t /\ Vote(v, w, s, g, u) \in votes }
DeathProof(t) ==
    \E p \in Header[t] :
        LET s == p[1] g == p[2] IN
            \/ \E u \in Tids : u # t /\ Sealed(s, g, u)
            \/ \E v \in {0,1} : Cardinality(VotersAgainst(v, s, g, t)) >= Q

MaxOr0(F) == IF F = {} THEN 0 ELSE CHOOSE m \in F : \A k \in F : k <= m

\* A CONTESTED record may also be settled by a SEAL (any version) for one of
\* its candidates: the other candidates are dead by that seal, and binding
\* the sealed tid at its generation creates no second seal (witness.py
\* _sealed_candidate). Only if no later generation is passed over.
ResolveContested(w, s) ==
    /\ w \in HonestV(ver)
    /\ bound[ver][w][s] = CONTESTED
    /\ \E b \in cand[ver][w][s] :
        LET killed == { c \in cand[ver][w][s] \ {b} : DeathProof(c[2]) }
            top    == MaxOr0({gen[ver][w][s]} \cup { c[1] + 1 : c \in killed })
        IN /\ Sealed(s, b[1], b[2])
           /\ cand[ver][w][s] = killed \cup {b}
           /\ top <= b[1] + 1
           /\ gen' = [gen EXCEPT ![ver][w][s] = b[1]]
           /\ bound' = [bound EXCEPT ![ver][w][s] = b[2]]
           /\ cand' = [cand EXCEPT ![ver][w][s] = {}]
    /\ UNCHANGED <<ver, votes, binds, rel, adopted>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ ver \in {0, 1}
    /\ gen \in [{0,1} -> [AllHonest -> [Sigils -> 0..(MaxGen+1)]]]
    /\ bound \in [{0,1} -> [AllHonest -> [Sigils -> Tids \cup {NoTid, CONTESTED}]]]
    /\ adopted \in BOOLEAN
    /\ cand \in [{0,1} -> [AllHonest -> [Sigils -> SUBSET (Gens \X Tids)]]]

\* Byzantine votes are EAGER: every vote the re-used Byzantine key Z could
\* ever sign (in either version, for any sigil/gen/tid) exists from the start.
\* This is the standard sound reduction (Sigil.tla): Spend never reads votes,
\* and Release's guard and Sealed are monotone in votes, so any lazy-Byzantine
\* behaviour -- and any violation -- is covered by the eager one. It also
\* removes the ByzVote branching that otherwise blows up the state space.
ByzVotes == { Vote(v, Z, s, g, t) : v \in {0,1}, s \in Sigils, g \in Gens, t \in Tids }

Init ==
    /\ ver = 0
    /\ gen = [v \in {0,1} |-> [w \in AllHonest |-> [s \in Sigils |-> 0]]]
    /\ bound = [v \in {0,1} |-> [w \in AllHonest |-> [s \in Sigils |-> NoTid]]]
    /\ votes = ByzVotes
    /\ binds = [s \in Sigils |-> {}]
    /\ rel = [s \in Sigils |-> {}]
    /\ adopted = FALSE
    /\ cand = [v \in {0,1} |-> [w \in AllHonest |-> [s \in Sigils |-> {}]]]

\* ---- Active-version dynamics (SPEC 5.1 / 5.2), honest witness w of ver ----
Spend(w, s, t) ==
    /\ w \in HonestV(ver)
    /\ s \in SigilsOf(t)
    /\ LET g == GenOf(t, s) IN
        /\ \/ g > gen[ver][w][s] /\ bound[ver][w][s] = NoTid
           \/ g = gen[ver][w][s] /\ bound[ver][w][s] \in {NoTid, t}
        /\ gen' = [gen EXCEPT ![ver][w][s] = g]
        /\ bound' = [bound EXCEPT ![ver][w][s] = t]
        /\ votes' = votes \cup {Vote(ver, w, s, g, t)}
        \* Record the bind in the v0 evidence log (only v0 logs feed ADOPT).
        /\ binds' = IF ver = 0 THEN [binds EXCEPT ![s] = @ \cup {<<g, t>>}] ELSE binds
        /\ UNCHANGED <<ver, rel, adopted, cand>>

Release(w, s) ==
    /\ w \in HonestV(ver)
    /\ bound[ver][w][s] \notin {NoTid, CONTESTED}
    /\ DeathProof(bound[ver][w][s])
    /\ rel' = IF ver = 0 THEN [rel EXCEPT ![s] = @ \cup {bound[ver][w][s]}] ELSE rel
    /\ gen' = [gen EXCEPT ![ver][w][s] = @ + 1]
    /\ bound' = [bound EXCEPT ![ver][w][s] = NoTid]
    /\ UNCHANGED <<ver, votes, binds, adopted, cand>>

\* A CONTESTED record (sibling mode) drops each candidate proven dead and
\* moves past its generation; once none is left it is unbound.
ReleaseContested(w, s) ==
    /\ w \in HonestV(ver)
    /\ bound[ver][w][s] = CONTESTED
    /\ \E b \in cand[ver][w][s] :
        /\ DeathProof(b[2])
        /\ LET rest == cand[ver][w][s] \ {b} IN
            /\ cand' = [cand EXCEPT ![ver][w][s] = rest]
            \* No votes while contested, so gen may rise with each dead candidate.
            /\ gen' = [gen EXCEPT ![ver][w][s] = IF b[1] + 1 > @ THEN b[1] + 1 ELSE @]
            /\ bound' = IF rest = {} THEN [bound EXCEPT ![ver][w][s] = NoTid] ELSE bound
    /\ UNCHANGED <<ver, votes, binds, rel, adopted>>

\* ---- Rotation: freeze v0 and adopt v1 (SPEC 5.4) ----

\* (a) The CURRENT algorithm (SPEC 5.4 / witness.py adopt), computed from the
\* union of the freezing quorum's honest logs: the binds made and the tids
\* released (shown dead).  A generation's floor advances past DEAD bindings.
Floor(s)    == MaxOr0({ IF t \in rel[s] THEN g + 1 ELSE g : <<g, t>> \in binds[s] })
AliveReal(s) == { b \in binds[s] : b[2] \notin rel[s] }
AdoptReal(s) ==
    IF Cardinality(AliveReal(s)) = 1
        THEN LET b == CHOOSE b \in AliveReal(s) : TRUE IN [g |-> b[1], tid |-> b[2]]
    ELSE IF Cardinality(AliveReal(s)) > 1 THEN [g |-> Floor(s), tid |-> CONTESTED]
    ELSE [g |-> Floor(s), tid |-> NoTid]

\* (b) The FIX: ADOPT keys off the v0 SEALS, not the bindings.  A generation
\* is "settled" by whichever tid a v0 quorum sealed there (Lemma 1: at most
\* one per generation); an UNSEALED bind is a mere attempt and is ignored, so
\* it can never be resurrected into a second seal.  This needs FREEZE evidence
\* to carry the seals (or q votes per sealed generation), which the current
\* log does not -- see docs/VERIFICATION.md.
Sealed0(s)      == { <<g, t>> \in Gens \X Tids : SealedIn(0, s, g, t) }
SealFloor(s)    == MaxOr0({ IF t \in rel[s] THEN g + 1 ELSE g : <<g, t>> \in Sealed0(s) })
AliveSealed(s)  == { b \in Sealed0(s) : b[2] \notin rel[s] }
AdoptSeal(s) ==
    IF Cardinality(AliveSealed(s)) = 1
        THEN LET b == CHOOSE b \in AliveSealed(s) : TRUE IN [g |-> b[1], tid |-> b[2]]
    ELSE IF Cardinality(AliveSealed(s)) > 1 THEN [g |-> SealFloor(s), tid |-> CONTESTED]
    ELSE [g |-> SealFloor(s), tid |-> NoTid]

\* (c) The IMPLEMENTED fix (witness.py adopt). It uses only the evidence log.
\* If two different tids were bound at one generation the owner equivocated
\* there, and the log cannot tell which one a v0 quorum sealed (if either).
\* So a lone live binding with a same-generation sibling, dead or alive, is
\* not inherited: the sigil becomes CONTESTED with every live binding as a
\* candidate, and is only released once each candidate is proven dead.
HasSibling(s, b) == \E u \in Tids : u # b[2] /\ <<b[1], u>> \in binds[s]
AdoptSib(s) ==
    IF AliveReal(s) = {}
        THEN [g |-> Floor(s), tid |-> NoTid, cand |-> {}]
    ELSE IF Cardinality(AliveReal(s)) = 1
            /\ ~HasSibling(s, CHOOSE b \in AliveReal(s) : TRUE)
        THEN LET b == CHOOSE b \in AliveReal(s) : TRUE IN [g |-> b[1], tid |-> b[2], cand |-> {}]
    ELSE [g |-> Floor(s), tid |-> CONTESTED, cand |-> AliveReal(s)]

AdoptRec(s) ==
    CASE AdoptMode = "sealaware" -> [g |-> AdoptSeal(s).g, tid |-> AdoptSeal(s).tid, cand |-> {}]
      [] AdoptMode = "sibling"   -> AdoptSib(s)
      [] OTHER                   -> [g |-> AdoptReal(s).g, tid |-> AdoptReal(s).tid, cand |-> {}]

Adopt ==
    /\ ver = 0
    /\ ~adopted
    \* A quorum of v0 must be able to have frozen; we simply allow rotation.
    /\ ver' = 1
    /\ adopted' = TRUE
    /\ gen' = [gen EXCEPT ![1] = [w \in AllHonest |-> [s \in Sigils |-> AdoptRec(s).g]]]
    /\ bound' = [bound EXCEPT ![1] = [w \in AllHonest |-> [s \in Sigils |-> AdoptRec(s).tid]]]
    /\ cand' = [cand EXCEPT ![1] = [w \in AllHonest |-> [s \in Sigils |-> AdoptRec(s).cand]]]
    /\ UNCHANGED <<votes, binds, rel>>

Next ==
    \/ \E w \in HonestV(ver), s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in HonestV(ver), s \in Sigils : Release(w, s)
    \/ \E w \in HonestV(ver), s \in Sigils : ReleaseContested(w, s)
    \/ AdoptMode = "sibling" /\ \E w \in HonestV(ver), s \in Sigils : ResolveContested(w, s)
    \/ Adopt

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* SPEC Section 8 across versions: no sigil consumed by two complete tids.
Safety ==
    \A t1, t2 \in Tids :
        (t1 # t2 /\ Complete(t1) /\ Complete(t2))
            => SigilsOf(t1) \cap SigilsOf(t2) = {}

\* Lemma 1 must survive rotation: at most one tid sealed per (s,g), counting
\* BOTH versions.  The bug breaks exactly this.
OneSealAcrossVersions ==
    \A s \in Sigils, g \in Gens, t1, t2 \in Tids :
        (Sealed(s, g, t1) /\ Sealed(s, g, t2)) => t1 = t2

\* No honest key signs two tids at one (s,g) -- within a version here, since
\* v0 and v1 honest keys are disjoint (re-used keys: own-vote abstention is
\* exercised by SigilRotReuse.cfg).
HonestNoEquiv ==
    \A v \in {0,1} : \A w \in HonestV(v) :
        \A s \in Sigils, g \in Gens, t1, t2 \in Tids :
            (Vote(v, w, s, g, t1) \in votes /\ Vote(v, w, s, g, t2) \in votes) => t1 = t2

\* Non-vacuity (MC_rot_sibling_witness.cfg, EXPECTED to be violated): after
\* rotation the owner can still recover s and complete Tg at generation 1.
TgNeverCompletes == ~(adopted /\ "Tg" \in Tids /\ Complete("Tg"))
\* ...and a CONTESTED record really is released (binds and rel are frozen after
\* ADOPT, so AdoptRec(s) is still what each v1 witness adopted).
NoContestedRelease ==
    ~(adopted /\ \E w \in Honest1, s \in Sigils :
        AdoptRec(s).tid = CONTESTED /\ bound[1][w][s] = NoTid)
\* ...and a CONTESTED record really is settled by a seal (ResolveContested).
NoContestedResolve ==
    ~(adopted /\ \E w \in Honest1, s \in Sigils :
        AdoptRec(s).tid = CONTESTED /\ bound[1][w][s] \in Tids)
================================================================================
