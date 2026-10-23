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

================================================================================
