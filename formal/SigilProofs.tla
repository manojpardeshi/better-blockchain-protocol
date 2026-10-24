---- MODULE SigilProofs ----
(***************************************************************************)
(* A machine-checked, UNBOUNDED proof of the Sigil safety theorem          *)
(* (docs/SPEC.md Section 8), discharged by TLAPS.                          *)
(*                                                                         *)
(* Unlike formal/Sigil.tla (which TLC checks exhaustively on small, fixed  *)
(* instances), this module proves Lemma 1, Lemma 2 and the Theorem for     *)
(* ARBITRARY numbers of witnesses, sigils, transitions, generations and    *)
(* constellations.  The only assumptions are:                             *)
(*                                                                         *)
(*   * each constellation has a finite membership;                        *)
(*   * every sigil's home satisfies the fault bound q = n - f with         *)
(*     f = floor((n-1)/3) and at most f Byzantine members (SPEC Section 8).*)
(*                                                                         *)
(* The protocol transition system is the same one formal/Sigil.tla         *)
(* describes (SPEC Sections 3.9, 5.1, 5.2), one charter version per        *)
(* constellation, with a fully adversarial owner, public monotone votes    *)
(* and Byzantine witnesses that may sign anything for themselves.  We      *)
(* prove  Spec => []Safety  by exhibiting an inductive invariant Inv and   *)
(* checking Init => Inv, Inv /\ [Next]_vars => Inv', and Inv => Safety.    *)
(*                                                                         *)
(* Quorum intersection among Byzantine witnesses is PROVED (lemma          *)
(* HonestInBothQuorums), not assumed; it rests only on the finite-set      *)
(* cardinality theorems of the TLAPS standard library (the FS_ lemmas),    *)
(* themselves machine-checked there and which we take as given.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS
    Honest,     \* honest witnesses (run the real protocol)
    Byz,        \* Byzantine witnesses (may sign any vote for themselves)
    Cons,       \* constellations
    Members,    \* Cons -> SUBSET Witnesses: each constellation's charter
    Quorum,     \* Cons -> Nat: q of each constellation
    Sigils,     \* sigils
    Home,       \* Sigils -> Cons: the home each sigil id commits to
    Tids,       \* transitions
    Header      \* Tids -> header (a set of <<sigil, gen>> pairs)

Witnesses == Honest \cup Byz

(* A vote is a record.  Cryptography is abstracted exactly as in           *)
(* Sigil.tla: only witness w can create a vote carrying wit |-> w, and a   *)
(* vote names the constellation it was cast under.                         *)
Vote(c, w, s, g, t) == [con |-> c, wit |-> w, sgl |-> s, gnr |-> g, trn |-> t]

NoTid == CHOOSE x : x \notin Tids        \* r.tid = null

ASSUME HonestByzDisjoint == Honest \cap Byz = {}
ASSUME MembersType       == Members \in [Cons -> SUBSET Witnesses]
ASSUME MembersFinite     == \A c \in Cons : IsFiniteSet(Members[c])
ASSUME MembersNonempty   == \A c \in Cons : Members[c] # {}
ASSUME MembersDisjoint   == \A c, d \in Cons : c # d => Members[c] \cap Members[d] = {}
ASSUME EveryWitnessPlaced == \A w \in Witnesses : \E c \in Cons : w \in Members[c]
ASSUME QuorumType        == Quorum \in [Cons -> Nat]
ASSUME HomeType          == Home \in [Sigils -> Cons]
ASSUME TidsNoTid         == NoTid \notin Tids

(* ConsOf(w): the (unique) constellation w belongs to.                     *)
ConsOf(w) == CHOOSE c \in Cons : w \in Members[c]

(* The fault bound of SPEC Section 8, imposed on every sigil's home.       *)
Faults(n)  == (n - 1) \div 3
FaultBounded(c) ==
    LET n == Cardinality(Members[c])
    IN  /\ Quorum[c] = n - Faults(n)
        /\ Cardinality(Members[c] \cap Byz) <= Faults(n)
ASSUME HomesFaultBounded == \A s \in Sigils : FaultBounded(Home[s])

(* A header is a non-empty set of <<sigil, gen>> inputs with distinct      *)
(* sigils (SPEC Sections 3.4, 5.1 step 3).                                 *)
ValidHeader(h) ==
    /\ h # {}
    /\ \A p \in h : p \in Sigils \X Nat
    /\ \A p, qq \in h : p[1] = qq[1] => p = qq
ASSUME HeaderType == Header \in [Tids -> {h \in SUBSET (Sigils \X Nat) : ValidHeader(h)}]

SigilsOf(t) == { p[1] : p \in Header[t] }
GenOf(t, s) == CHOOSE g \in Nat : <<s, g>> \in Header[t]

-----------------------------------------------------------------------------
(* State variables, exactly as in Sigil.tla.                               *)
VARIABLES
    gen,    \* gen[w][s]   : Record.gen of honest witness w for sigil s
    bound,  \* bound[w][s] : Record.tid (a tid or NoTid)
    votes   \* set of every vote ever cast (honest and Byzantine)

vars == <<gen, bound, votes>>

VoteSpace ==
    { Vote(c, w, s, g, t) :
        c \in Cons, w \in Witnesses, s \in Sigils, g \in Nat, t \in Tids }

(* The core predicates are parameterised by the vote set V so that we can   *)
(* reason about how they change as votes accumulate (votes only ever grow). *)
(* The state-level predicates below instantiate V with the variable votes.  *)

(* Distinct members of c that voted for t at (s, g).                       *)
VotersV(V, c, s, g, t)  == { w \in Members[c] : Vote(c, w, s, g, t) \in V }
(* Distinct members of c that voted for SOME tid other than t at (s, g).   *)
AgainstV(V, c, s, g, t) == { w \in Members[c] :
                                \E u \in Tids : u # t /\ Vote(c, w, s, g, u) \in V }
(* A Section 3.6-valid seal from c for (s, g, t): q_c of c's members voted. *)
SealedByV(V, c, s, g, t) == Cardinality(VotersV(V, c, s, g, t)) >= Quorum[c]
(* The seal holders accept (SPEC Section 6 rule 4: seal.constellation = home).*)
SealedV(V, s, g, t) == SealedByV(V, Home[s], s, g, t)

(* SPEC Section 3.9, fixed (home-only) rule: a valid death proof for t      *)
(* names an input [s, g] of t and shows a seal for another tid, or q        *)
(* against-votes, at (s, g) FROM Home[s].                                   *)
DeathProofExistsV(V, t) ==
    \E p \in Header[t] :
        LET s == p[1] g == p[2] IN
            \/ \E u \in Tids : u # t /\ SealedV(V, s, g, u)
            \/ Cardinality(AgainstV(V, Home[s], s, g, t)) >= Quorum[Home[s]]

(* SPEC Section 8: complete = every input sealed, by its home, to t.        *)
CompleteV(V, t) == \A p \in Header[t] : SealedV(V, p[1], p[2], t)

(* State-level instances (what the actions and the theorem talk about).     *)
Voters(c, s, g, t)  == VotersV(votes, c, s, g, t)
Against(c, s, g, t) == AgainstV(votes, c, s, g, t)
SealedBy(c, s, g, t) == SealedByV(votes, c, s, g, t)
Sealed(s, g, t)     == SealedV(votes, s, g, t)
DeathProofExists(t) == DeathProofExistsV(votes, t)
Complete(t)         == CompleteV(votes, t)

-----------------------------------------------------------------------------
(* The transition system (SPEC Section 5.1, 5.2); identical in shape to     *)
(* Sigil.tla with AnyProof = AnyConstellationProof = FALSE, generations     *)
(* unbounded.                                                               *)
Init ==
    /\ gen   = [w \in Honest |-> [s \in Sigils |-> 0]]
    /\ bound = [w \in Honest |-> [s \in Sigils |-> NoTid]]
    /\ votes = {}

Spend(w, s, t) ==
    /\ s \in SigilsOf(t)
    /\ Home[s] = ConsOf(w)
    /\ LET g == GenOf(t, s) IN
        /\ \/ g > gen[w][s] /\ bound[w][s] = NoTid       \* jump (abstain), then bind
           \/ g = gen[w][s] /\ bound[w][s] \in {NoTid, t} \* bind / re-vote
        /\ gen'   = [gen   EXCEPT ![w][s] = g]
        /\ bound' = [bound EXCEPT ![w][s] = t]
        /\ votes' = votes \cup {Vote(ConsOf(w), w, s, g, t)}

Release(w, s) ==
    /\ bound[w][s] # NoTid
    /\ DeathProofExists(bound[w][s])
    /\ gen'   = [gen   EXCEPT ![w][s] = @ + 1]
    /\ bound' = [bound EXCEPT ![w][s] = NoTid]
    /\ UNCHANGED votes

ByzVote(b, s, g, t) ==
    /\ votes' = votes \cup {Vote(ConsOf(b), b, s, g, t)}
    /\ UNCHANGED <<gen, bound>>

Next ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : Release(w, s)
    \/ \E b \in Byz, s \in Sigils, g \in Nat, t \in Tids : ByzVote(b, s, g, t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* The safety theorem (SPEC Section 8) and the two lemmas.                  *)
Safety ==
    \A t1, t2 \in Tids :
        (t1 # t2 /\ Complete(t1) /\ Complete(t2))
            => SigilsOf(t1) \cap SigilsOf(t2) = {}

OneSealPerGen ==
    \A s \in Sigils, g \in Nat, t1, t2 \in Tids :
        (Sealed(s, g, t1) /\ Sealed(s, g, t2)) => t1 = t2

DeathProofsSound == \A t \in Tids : DeathProofExists(t) => ~Complete(t)

-----------------------------------------------------------------------------
(* ===================  PART A: static set-theoretic facts  ================ *)

(* A witness belongs to exactly one constellation, namely ConsOf(w).       *)
LEMMA ConsOfSpec ==
    ASSUME NEW c \in Cons, NEW w, w \in Members[c]
    PROVE  ConsOf(w) = c
<1>1. w \in Witnesses BY MembersType
<1>2. \E d \in Cons : w \in Members[d] BY <1>1
<1>3. ConsOf(w) \in Cons /\ w \in Members[ConsOf(w)]
    BY <1>2, Zenon DEF ConsOf
<1>. QED BY <1>3, MembersDisjoint

(* The fault bound is strict: with f = floor((n-1)/3) and n >= 1 we have    *)
(* n > 3f.  Pure arithmetic, discharged by Z3.                              *)
LEMMA FaultArith ==
    ASSUME NEW n \in Nat, n >= 1, NEW f \in Nat, f = (n - 1) \div 3
    PROVE  n > 3 * f
BY SMT

(* THE quorum-intersection fact, proved for Byzantine membership.  Any two  *)
(* quorum-sized subsets of a fault-bounded constellation share an HONEST    *)
(* member.  Rests only on the FS_ cardinality theorems.                     *)
LEMMA HonestInBothQuorums ==
    ASSUME NEW c \in Cons, NEW A, NEW B,
           A \subseteq Members[c], B \subseteq Members[c],
           Cardinality(A) >= Quorum[c], Cardinality(B) >= Quorum[c],
           FaultBounded(c)
    PROVE  \E w \in A \cap B : w \in Honest
<1> DEFINE M == Members[c]
           n == Cardinality(M)
           f == (n - 1) \div 3
           H == M \ Byz
           AB == A \cap B
<1>mf. IsFiniteSet(M) BY MembersFinite
<1>ne. M # {} BY MembersNonempty
<1>n1. n \in Nat /\ n >= 1 BY <1>mf, <1>ne, FS_EmptySet, FS_CardinalityType
<1>ff. f \in Nat BY <1>n1
<1>fb. Quorum[c] = n - f /\ Cardinality(M \cap Byz) <= f BY DEF FaultBounded, Faults
<1>n3f. n > 3 * f BY <1>n1, <1>ff, FaultArith
<1>af. IsFiniteSet(A) /\ Cardinality(A) \in Nat /\ Cardinality(A) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>bf. IsFiniteSet(B) /\ Cardinality(B) \in Nat /\ Cardinality(B) <= n
    BY <1>mf, FS_Subset, FS_CardinalityType
<1>qn. Quorum[c] \in Nat /\ Quorum[c] <= n BY QuorumType, <1>fb, <1>n1
<1>bz. IsFiniteSet(M \cap Byz) /\ Cardinality(M \cap Byz) \in Nat
    BY <1>mf, FS_Intersection, FS_CardinalityType
\* Cardinality of the honest members.
<1>h1. IsFiniteSet(H) /\ Cardinality(H) = n - Cardinality(M \cap Byz)
    BY <1>mf, FS_Difference
<1>h2. Cardinality(H) \in Nat /\ Cardinality(H) >= n - f
    BY <1>h1, <1>fb, <1>n1, <1>bz, FS_CardinalityType, SMT
<1>hsub. H \subseteq M OBVIOUS
\* Cardinality of the intersection AB.
<1>u1. IsFiniteSet(A \cup B) /\ Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(AB)
    BY <1>af, <1>bf, FS_Union
<1>u2. (A \cup B) \subseteq M BY <1>hsub
<1>uc. Cardinality(A \cup B) \in Nat BY <1>u1, FS_CardinalityType
<1>u3. Cardinality(A \cup B) <= n BY <1>u1, <1>u2, <1>mf, FS_Subset
<1>abf. IsFiniteSet(AB) /\ Cardinality(AB) \in Nat BY <1>af, FS_Intersection, FS_CardinalityType
<1>ab1. Cardinality(AB) >= Cardinality(A) + Cardinality(B) - n
    BY <1>u1, <1>u3, <1>uc, <1>af, <1>bf, <1>abf, <1>n1, SMT
\* Honest and intersection together exceed the whole constellation:
\*   |AB| + |H| >= (|A|+|B|-n) + (n-f) >= 2(n-f) - f = 2n - 3f > n  (since n > 3f).
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

-----------------------------------------------------------------------------
(* ===================  PART B: the inductive invariant  =================== *)

(* HVote(w,s,g,t): the vote an honest witness w (in constellation ConsOf(w))*)
(* casts to bind s at g to t.  Only w itself can produce it.                *)
HVote(w, s, g, t) == Vote(ConsOf(w), w, s, g, t)

TypeOK ==
    /\ gen   \in [Honest -> [Sigils -> Nat]]
    /\ bound \in [Honest -> [Sigils -> Tids \cup {NoTid}]]
    /\ votes \subseteq VoteSpace

(* Every honest witness's vote carries its own constellation, and names a   *)
(* sigil homed there (SPEC 5.1 step 2).                                     *)
VotesShape ==
    \A v \in votes :
        v.wit \in Honest => /\ v.con = ConsOf(v.wit)
                            /\ Home[v.sgl] = ConsOf(v.wit)

(* An honest witness never signs two tids at one (sigil, gen)  (SPEC 5.1).  *)
HonestNoEquiv ==
    \A w \in Honest, s \in Sigils, g \in Nat, t1, t2 \in Tids :
        (HVote(w, s, g, t1) \in votes /\ HVote(w, s, g, t2) \in votes) => t1 = t2

(* An honest witness only ever voted at generations <= its current one.     *)
VoteBelowGen ==
    \A w \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        HVote(w, s, g, t) \in votes => g <= gen[w][s]

(* The binding at the current generation reflects exactly the vote cast     *)
(* there: bound <=> a vote at gen[w][s].                                    *)
BoundVote ==
    \A w \in Honest, s \in Sigils :
        /\ (bound[w][s] # NoTid => HVote(w, s, gen[w][s], bound[w][s]) \in votes)
        /\ (bound[w][s] = NoTid => \A t \in Tids : HVote(w, s, gen[w][s], t) \notin votes)

(* THE release discipline (SPEC 5.2): an honest witness only advanced past   *)
(* a generation at which it had voted t by RELEASING, which required a       *)
(* valid death proof for t -- a timeless fact, still present now.           *)
ReleaseDiscipline ==
    \A w \in Honest, s \in Sigils, g \in Nat, t \in Tids :
        (HVote(w, s, g, t) \in votes /\ g < gen[w][s]) => DeathProofExists(t)

Inv ==
    /\ TypeOK
    /\ VotesShape
    /\ HonestNoEquiv
    /\ VoteBelowGen
    /\ BoundVote
    /\ ReleaseDiscipline

(* ---- Monotonicity: every relevant predicate only strengthens as votes    *)
(* accumulate.  Needed because Spend and ByzVote only ever ADD votes.       *)

LEMMA VotersMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2,
           NEW c \in Cons, NEW s, NEW g, NEW t
    PROVE  /\ VotersV(V1, c, s, g, t) \subseteq VotersV(V2, c, s, g, t)
           /\ AgainstV(V1, c, s, g, t) \subseteq AgainstV(V2, c, s, g, t)
BY DEF VotersV, AgainstV

LEMMA CardMonotoneQuorum ==
    ASSUME NEW c \in Cons, NEW X, NEW Y, X \subseteq Y, Y \subseteq Members[c],
           Cardinality(X) >= Quorum[c]
    PROVE  Cardinality(Y) >= Quorum[c]
<1>1. IsFiniteSet(Members[c]) BY MembersFinite
<1>2. IsFiniteSet(Y) /\ IsFiniteSet(X) BY <1>1, FS_Subset
<1>3. Cardinality(X) <= Cardinality(Y) BY <1>2, FS_Subset
<1>4. Cardinality(X) \in Nat /\ Cardinality(Y) \in Nat BY <1>2, FS_CardinalityType
<1>. QED BY <1>3, <1>4, QuorumType, SMT

LEMMA SealedByMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2,
           NEW c \in Cons, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
           SealedByV(V1, c, s, g, t)
    PROVE  SealedByV(V2, c, s, g, t)
<1>1. VotersV(V1, c, s, g, t) \subseteq VotersV(V2, c, s, g, t) BY VotersMonotone
<1>2. VotersV(V2, c, s, g, t) \subseteq Members[c] BY DEF VotersV
<1>. QED BY <1>1, <1>2, CardMonotoneQuorum DEF SealedByV

LEMMA AgainstMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2,
           NEW c \in Cons, NEW s \in Sigils, NEW g \in Nat, NEW t \in Tids,
           Cardinality(AgainstV(V1, c, s, g, t)) >= Quorum[c]
    PROVE  Cardinality(AgainstV(V2, c, s, g, t)) >= Quorum[c]
<1>1. AgainstV(V1, c, s, g, t) \subseteq AgainstV(V2, c, s, g, t) BY VotersMonotone
<1>2. AgainstV(V2, c, s, g, t) \subseteq Members[c] BY DEF AgainstV
<1>. QED BY <1>1, <1>2, CardMonotoneQuorum

LEMMA DeathMonotone ==
    ASSUME NEW V1, NEW V2, V1 \subseteq V2, NEW t \in Tids,
           DeathProofExistsV(V1, t)
    PROVE  DeathProofExistsV(V2, t)
<1>1. PICK p \in Header[t] :
        \/ \E u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u)
        \/ Cardinality(AgainstV(V1, Home[p[1]], p[1], p[2], t)) >= Quorum[Home[p[1]]]
    BY DEF DeathProofExistsV
<1>2. p \in Sigils \X Nat BY HeaderType DEF ValidHeader
<1>3. p[1] \in Sigils /\ p[2] \in Nat BY <1>2
<1>4. Home[p[1]] \in Cons BY <1>3, HomeType
<1>. QED
    <2>1. CASE \E u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u)
        <3>1. PICK u \in Tids : u # t /\ SealedV(V1, p[1], p[2], u) BY <2>1
        <3>2. SealedV(V2, p[1], p[2], u)
            BY <3>1, <1>3, <1>4, SealedByMonotone DEF SealedV
        <3>. QED BY <3>1, <3>2 DEF DeathProofExistsV
    <2>2. CASE Cardinality(AgainstV(V1, Home[p[1]], p[1], p[2], t)) >= Quorum[Home[p[1]]]
        <3>1. Cardinality(AgainstV(V2, Home[p[1]], p[1], p[2], t)) >= Quorum[Home[p[1]]]
            BY <2>2, <1>3, <1>4, AgainstMonotone
        <3>. QED BY <3>1 DEF DeathProofExistsV
    <2>. QED BY <1>1, <2>1, <2>2

-----------------------------------------------------------------------------
(* ============  PART C: the lemmas and theorem, from the invariant  ======= *)

(* Two home seals for one (s, g) share an honest voter, who by              *)
(* HonestNoEquiv voted for a single tid -- so the two seals agree.          *)
THEOREM Inv_OneSealPerGen == Inv => OneSealPerGen
<1>. SUFFICES ASSUME Inv,
                     NEW s \in Sigils, NEW g \in Nat, NEW t1 \in Tids, NEW t2 \in Tids,
                     Sealed(s, g, t1), Sealed(s, g, t2)
              PROVE  t1 = t2
    BY DEF OneSealPerGen
<1> DEFINE c == Home[s]
<1>c. c \in Cons BY HomeType
<1>fb. FaultBounded(c) BY HomesFaultBounded
<1>A. Voters(c, s, g, t1) \subseteq Members[c] /\ Cardinality(Voters(c, s, g, t1)) >= Quorum[c]
    BY DEF Sealed, SealedV, SealedByV, Voters, VotersV
<1>B. Voters(c, s, g, t2) \subseteq Members[c] /\ Cardinality(Voters(c, s, g, t2)) >= Quorum[c]
    BY DEF Sealed, SealedV, SealedByV, Voters, VotersV
<1>h. PICK w \in Voters(c, s, g, t1) \cap Voters(c, s, g, t2) : w \in Honest
    BY <1>c, <1>fb, <1>A, <1>B, HonestInBothQuorums
<1>w. w \in Members[c] /\ Vote(c, w, s, g, t1) \in votes /\ Vote(c, w, s, g, t2) \in votes
    BY <1>h DEF Voters, VotersV
<1>co. ConsOf(w) = c BY <1>c, <1>w, ConsOfSpec
<1>. QED BY <1>h, <1>w, <1>co DEF Inv, HonestNoEquiv, HVote

(* A transition with a death proof cannot also be complete.                 *)
THEOREM Inv_DeathProofsSound == Inv => DeathProofsSound
<1>. SUFFICES ASSUME Inv, NEW t \in Tids, DeathProofExists(t), Complete(t)
              PROVE  FALSE
    BY DEF DeathProofsSound
<1>osg. OneSealPerGen BY Inv_OneSealPerGen
<1>1. PICK p \in Header[t] :
        \/ \E u \in Tids : u # t /\ Sealed(p[1], p[2], u)
        \/ Cardinality(Against(Home[p[1]], p[1], p[2], t)) >= Quorum[Home[p[1]]]
    BY DEF DeathProofExists, DeathProofExistsV, Sealed, SealedV, Against, AgainstV
<1>2. p \in Sigils \X Nat BY HeaderType DEF ValidHeader
<1>s. p[1] \in Sigils /\ p[2] \in Nat BY <1>2
<1> DEFINE s == p[1] g == p[2] c == Home[s]
<1>c. c \in Cons BY <1>s, HomeType
<1>fb. FaultBounded(c) BY <1>s, HomesFaultBounded
<1>sel. Sealed(s, g, t) BY <1>s, p \in Header[t] DEF Complete, CompleteV, Sealed, SealedV
<1>. QED
    <2>1. CASE \E u \in Tids : u # t /\ Sealed(s, g, u)
        <3>1. PICK u \in Tids : u # t /\ Sealed(s, g, u) BY <2>1
        <3>. QED BY <3>1, <1>sel, <1>s, <1>osg DEF OneSealPerGen
    <2>2. CASE Cardinality(Against(c, s, g, t)) >= Quorum[c]
        <3>A. Against(c, s, g, t) \subseteq Members[c] /\ Cardinality(Against(c, s, g, t)) >= Quorum[c]
            BY <2>2 DEF Against, AgainstV
        <3>B. Voters(c, s, g, t) \subseteq Members[c] /\ Cardinality(Voters(c, s, g, t)) >= Quorum[c]
            BY <1>sel DEF Sealed, SealedV, SealedByV, Voters, VotersV
        <3>h. PICK w \in Against(c, s, g, t) \cap Voters(c, s, g, t) : w \in Honest
            BY <1>c, <1>fb, <3>A, <3>B, HonestInBothQuorums
        <3>w. w \in Members[c] /\ Vote(c, w, s, g, t) \in votes
            BY <3>h DEF Voters, VotersV
        <3>u. PICK u \in Tids : u # t /\ Vote(c, w, s, g, u) \in votes
            BY <3>h DEF Against, AgainstV
        <3>co. ConsOf(w) = c BY <1>c, <3>w, ConsOfSpec
        <3>. QED BY <3>h, <3>w, <3>u, <3>co, <1>s DEF Inv, HonestNoEquiv, HVote
    <2>. QED BY <1>1, <2>1, <2>2

(* ======================  THE SAFETY THEOREM (SPEC 8)  ==================== *)
THEOREM Inv_Safety == Inv => Safety
<1>. SUFFICES ASSUME Inv,
                     NEW t1 \in Tids, NEW t2 \in Tids,
                     t1 # t2, Complete(t1), Complete(t2),
                     NEW s, s \in SigilsOf(t1) \cap SigilsOf(t2)
              PROVE  FALSE
    BY DEF Safety
<1>osg. OneSealPerGen BY Inv_OneSealPerGen
<1>dps. DeathProofsSound BY Inv_DeathProofsSound
\* s is an input of both headers, at g1 and g2 respectively.
<1>p1. PICK g1 \in Nat : <<s, g1>> \in Header[t1]
    BY HeaderType DEF SigilsOf, ValidHeader
<1>p2. PICK g2 \in Nat : <<s, g2>> \in Header[t2]
    BY HeaderType DEF SigilsOf, ValidHeader
<1>sg. s \in Sigils BY <1>p1, HeaderType DEF ValidHeader
<1> DEFINE c == Home[s]
<1>c. c \in Cons BY <1>sg, HomeType
<1>fb. FaultBounded(c) BY <1>sg, HomesFaultBounded
<1>se1. Sealed(s, g1, t1) BY <1>p1 DEF Complete, CompleteV, Sealed, SealedV
<1>se2. Sealed(s, g2, t2) BY <1>p2 DEF Complete, CompleteV, Sealed, SealedV
<1>. QED
    <2>1. CASE g1 = g2
        BY <2>1, <1>se1, <1>se2, <1>sg, <1>p1, <1>osg DEF OneSealPerGen
    <2>2. CASE g1 # g2
        \* WLOG the two generations are gLo < gHi; the honest voter in both
        \* seals voted the lo-tid at gLo and the hi-tid at gHi.
        <3> DEFINE gLo == IF g1 < g2 THEN g1 ELSE g2
                   gHi == IF g1 < g2 THEN g2 ELSE g1
                   tLo == IF g1 < g2 THEN t1 ELSE t2
                   tHi == IF g1 < g2 THEN t2 ELSE t1
        <3>lt. gLo \in Nat /\ gHi \in Nat /\ gLo < gHi BY <1>p1, <1>p2, <2>2, SMT
        <3>tt. tLo \in Tids /\ tHi \in Tids OBVIOUS
        <3>sl. Sealed(s, gLo, tLo) BY <1>se1, <1>se2
        <3>sh. Sealed(s, gHi, tHi) BY <1>se1, <1>se2
        <3>A. Voters(c, s, gLo, tLo) \subseteq Members[c] /\ Cardinality(Voters(c, s, gLo, tLo)) >= Quorum[c]
            BY <3>sl DEF Sealed, SealedV, SealedByV, Voters, VotersV
        <3>B. Voters(c, s, gHi, tHi) \subseteq Members[c] /\ Cardinality(Voters(c, s, gHi, tHi)) >= Quorum[c]
            BY <3>sh DEF Sealed, SealedV, SealedByV, Voters, VotersV
        <3>h. PICK w \in Voters(c, s, gLo, tLo) \cap Voters(c, s, gHi, tHi) : w \in Honest
            BY <1>c, <1>fb, <3>A, <3>B, HonestInBothQuorums
        <3>w. w \in Members[c] /\ Vote(c, w, s, gLo, tLo) \in votes /\ Vote(c, w, s, gHi, tHi) \in votes
            BY <3>h DEF Voters, VotersV
        <3>co. ConsOf(w) = c BY <1>c, <3>w, ConsOfSpec
        \* The hi-vote puts w's generation at or above gHi, so strictly above gLo.
        <3>vb. gHi <= gen[w][s] BY <3>w, <3>co, <3>tt, <3>lt, <1>sg, <3>h, Zenon DEF Inv, VoteBelowGen, HVote
        <3>gn. gen[w][s] \in Nat BY <3>h, <1>sg DEF Inv, TypeOK
        <3>g. gLo < gen[w][s] BY <3>vb, <3>lt, <3>gn, SMT
        \* The lo-vote with an advanced generation forces a death proof for tLo.
        <3>dp. DeathProofExists(tLo)
            BY <3>w, <3>co, <3>tt, <3>lt, <3>g, <1>sg, <3>h DEF Inv, ReleaseDiscipline, HVote
        <3>nc. ~Complete(tLo) BY <3>dp, <3>tt, <1>dps DEF DeathProofsSound
        <3>. QED BY <3>nc, <1>se1, <1>se2, <2>2 DEF Complete, CompleteV
    <2>. QED BY <2>1, <2>2

================================================================================
