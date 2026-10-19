-------------------------------- MODULE Sigil --------------------------------
(***************************************************************************)
(* The Sigil witness protocol (docs/SPEC.md §3.9, §5.1, §5.2) and its      *)
(* safety theorem (§8): no sigil is an input of two different complete     *)
(* transitions.                                                            *)
(*                                                                         *)
(* Several constellations, one charter version each (no rotation).  Each  *)
(* witness is a member of exactly one constellation and is Honest or Byz;  *)
(* a constellation may be entirely Byzantine (an attacker-run "rogue"      *)
(* constellation that is in the registry).  Every sigil has a fixed home   *)
(* constellation: the sigil id commits to it (§3.2), so it cannot be       *)
(* faked.  A vote carries its constellation, and a seal for a sigil counts *)
(* only votes from the sigil's home, as holders require (§6 rule 4).       *)
(*                                                                         *)
(* Owners are fully adversarial: every owner authorises every transition,  *)
(* so any honest witness may receive a spend request for any (sigil,       *)
(* transition) pair at any time.  Cryptography is abstracted: a vote is    *)
(* the tuple <<c, w, s, g, t>> and only w can create it, so Byzantine      *)
(* witnesses can create any vote for themselves (under their own           *)
(* constellation, for any sigil) and no vote for anyone else.  Votes are   *)
(* public (STATUS, §5.3) and never disappear, so the adversary can always  *)
(* assemble any seal or death proof that the current set of votes          *)
(* supports.                                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Honest,         \* honest witnesses
    Byz,            \* Byzantine witnesses (vote anything, any time)
    Cons,           \* constellations (cids)
    Members,        \* Cons -> SUBSET witnesses: each constellation's charter
    Quorum,         \* Cons -> Nat: q of each constellation
    Sigils,         \* sigils
    Home,           \* Sigils -> Cons: the home each sigil id commits to
    Tids,           \* transitions
    MaxGen,         \* generations in headers range over 0..MaxGen
    HeaderSpace,    \* set of functions Tids -> headers; Init picks one
    ByzEager,       \* TRUE: Byzantine votes exist from the start (see below)
    AnyProof,       \* MUTATION: TRUE makes Release accept any proof
    AnyConstellationProof
                    \* MUTATION: TRUE makes Release accept a death proof
                    \* whose seal/votes come from ANY constellation, not
                    \* only from the home of the sigil the proof names
                    \* (the behaviour before the fix)

ASSUME Honest \cap Byz = {}
Witnesses == Honest \cup Byz

ASSUME Members \in [Cons -> SUBSET Witnesses]
ASSUME \A c, d \in Cons : c # d => Members[c] \cap Members[d] = {}
ASSUME \A w \in Witnesses : \E c \in Cons : w \in Members[c]
ASSUME Quorum \in [Cons -> Nat]
ASSUME \A c \in Cons : 1 <= Quorum[c] /\ Quorum[c] <= Cardinality(Members[c])
ASSUME Home \in [Sigils -> Cons]

ConsOf(w) == CHOOSE c \in Cons : w \in Members[c]

(* The §8 theorem assumes every home satisfies the fault bound: q = n - f  *)
(* with f = floor((n-1)/3), and at most f Byzantine members.  Other        *)
(* constellations (e.g. all-Byzantine rogue ones) are unconstrained but    *)
(* home no sigil of the model: a holder that trusts a rogue home has no    *)
(* guarantee for sigils homed there, by assumption.                        *)
FaultBounded(c) ==
    LET n == Cardinality(Members[c])
        f == (n - 1) \div 3
    IN  /\ Quorum[c] = n - f
        /\ Cardinality(Members[c] \cap Byz) <= f
ASSUME \A s \in Sigils : FaultBounded(Home[s])

Gens      == 0..MaxGen
NoTid     == "none"            \* r.tid = null
ASSUME NoTid \notin Tids

(* A header is a non-empty set of <<sigil, gen>> inputs with distinct      *)
(* sigils (§3.4, §5.1 step 3).  The body hash is folded into the tid.      *)
ValidHeaders ==
    { h \in SUBSET (Sigils \X Gens) :
        h # {} /\ \A p, q \in h : p[1] = q[1] => p = q }

ASSUME HeaderSpace \subseteq [Tids -> ValidHeaders]

VARIABLES
    header,     \* Tids -> header; chosen in Init, constant afterwards
    gen,        \* gen[w][s]   : Record.gen of honest witness w for sigil s
    bound,      \* bound[w][s] : Record.tid (a tid or NoTid)
    votes       \* set of <<c, w, s, g, t>>: every vote ever cast (honest
                \* and Byz); c is the vote's constellation, w \in Members[c]

vars == <<header, gen, bound, votes>>

SigilsOf(t)    == { p[1] : p \in header[t] }
GenOf(t, s)    == CHOOSE g \in Gens : <<s, g>> \in header[t]

(* Distinct members of constellation c that voted for t at (s, g).        *)
VotersFor(c, s, g, t) ==
    { w \in Members[c] : <<c, w, s, g, t>> \in votes }

(* Distinct members of c that voted for some tid other than t at (s, g).   *)
VotersAgainst(c, s, g, t) ==
    { w \in Members[c] : \E u \in Tids \ {t} : <<c, w, s, g, u>> \in votes }

(* A seal from constellation c for (s, g, t) that is valid in the sense of *)
(* §3.6: q_c distinct members of c voted.  Any constellation in the        *)
(* registry can produce such a seal for any sigil, a rogue one included.  *)
SealedBy(c, s, g, t) == Cardinality(VotersFor(c, s, g, t)) >= Quorum[c]

(* The seal holders accept (§6 rule 4: seal.constellation = home).         *)
Sealed(s, g, t) == SealedBy(Home[s], s, g, t)

(* Constellations whose seal/votes a death proof naming sigil s may carry. *)
(* Fixed rule: only Home[s].  The proof carries the target's {home, lock,  *)
(* salt}; the witness checks sigil_of(...) = s and that the seal/votes are *)
(* from that home.  Since the sigil id commits to its home, this is        *)
(* exactly Home[s].                                                        *)
ProofCons(s) == IF AnyConstellationProof THEN Cons ELSE {Home[s]}

(* §3.9: a valid death proof for transition t exists.  It names an input   *)
(* [s, g] of t's header -- not necessarily the sigil being released -- and *)
(* is either a seal for another tid at (s, g) or q votes for other tids at *)
(* (s, g), from one constellation in ProofCons(s).  Byzantine votes count. *)
DeathProofExists(t) ==
    \E p \in header[t] :
        LET s == p[1]  g == p[2] IN
        \E c \in ProofCons(s) :
            \/ \E u \in Tids \ {t} : SealedBy(c, s, g, u)             \* "seal"
            \/ Cardinality(VotersAgainst(c, s, g, t)) >= Quorum[c]    \* "votes"

(* §8: complete = every input sealed, by its home, to t at the generation  *)
(* t names.                                                                *)
Complete(t) == \A p \in header[t] : Sealed(p[1], p[2], t)

VoteSpace ==
    { v \in Cons \X Witnesses \X Sigils \X Gens \X Tids : v[2] \in Members[v[1]] }

(* Byzantine members sign any vote, for any sigil, homed there or not.     *)
ByzVotes == { v \in VoteSpace : v[2] \in Byz }

-----------------------------------------------------------------------------
TypeOK ==
    /\ header \in [Tids -> ValidHeaders]
    /\ gen    \in [Honest -> [Sigils -> 0..(MaxGen + 1)]]
    /\ bound  \in [Honest -> [Sigils -> Tids \cup {NoTid}]]
    /\ votes  \subseteq VoteSpace

(* THEOREM (§8).                                                           *)
Safety ==
    \A t1, t2 \in Tids :
        (t1 # t2 /\ Complete(t1) /\ Complete(t2))
            => SigilsOf(t1) \cap SigilsOf(t2) = {}

(* Auxiliary invariants (the lemmas, and the honest-witness discipline).   *)

\* An honest witness votes at most once per (s, g)  (§5.1, last sentence),
\* and only for sigils homed at its own constellation (§5.1 step 2).
HonestNoEquivocation ==
    \A c \in Cons, w \in Honest, s \in Sigils, g \in Gens, t1, t2 \in Tids :
        /\ (<<c, w, s, g, t1>> \in votes /\ <<c, w, s, g, t2>> \in votes)
               => t1 = t2
        /\ <<c, w, s, g, t1>> \in votes => Home[s] = c

\* Lemma 1: at most one tid sealed (by the home) per (s, g).
OneSealPerGen ==
    \A s \in Sigils, g \in Gens, t1, t2 \in Tids :
        (Sealed(s, g, t1) /\ Sealed(s, g, t2)) => t1 = t2

\* Lemma 2: a transition with a death proof is never complete.
DeathProofsSound == \A t \in Tids : DeathProofExists(t) => ~Complete(t)

-----------------------------------------------------------------------------
Init ==
    /\ header \in HeaderSpace
    /\ gen    = [w \in Honest |-> [s \in Sigils |-> 0]]
    /\ bound  = [w \in Honest |-> [s \in Sigils |-> NoTid]]
    /\ votes  = IF ByzEager THEN ByzVotes ELSE {}

(* §5.1 SPEND, honest witness w, request to consume s by t.  The owner is  *)
(* adversarial so authorisation (step 3) always passes; step 1 (stamps) is *)
(* irrelevant to safety.  Step 2: w serves only sigils homed at its own    *)
(* constellation.  Rejections and Conflict replies change no state, so     *)
(* they are modelled as the action being disabled.                         *)
Spend(w, s, t) ==
    /\ s \in SigilsOf(t)
    /\ Home[s] = ConsOf(w)
    /\ LET g == GenOf(t, s)
           r == [gen |-> gen[w][s], tid |-> bound[w][s]]
       IN
       \* g < r.gen                         -> reject (stale)
       \* g > r.gen /\ r.tid # null         -> reject (release first)
       \* g = r.gen /\ r.tid \notin {null,t} -> Conflict
       /\ \/ g > r.gen /\ r.tid = NoTid               \* jump, then bind
          \/ g = r.gen /\ r.tid \in {NoTid, t}        \* bind / re-vote
       /\ gen'   = [gen   EXCEPT ![w][s] = g]
       /\ bound' = [bound EXCEPT ![w][s] = t]
       /\ votes' = votes \cup {<<ConsOf(w), w, s, g, t>>}
       /\ UNCHANGED header

(* §5.2 RELEASE, honest witness w on sigil s.  The death proof may name    *)
(* another input s' of the bound header; its seal/votes must then come     *)
(* from Home[s'] (ProofCons), which may differ from w's constellation.     *)
Release(w, s) ==
    /\ bound[w][s] # NoTid
    /\ AnyProof \/ DeathProofExists(bound[w][s])
    /\ gen'   = [gen   EXCEPT ![w][s] = @ + 1]
    /\ bound' = [bound EXCEPT ![w][s] = NoTid]
    /\ UNCHANGED <<header, votes>>

(* A Byzantine witness signs any vote for itself at any time.  With        *)
(* ByzEager = TRUE all such votes exist from Init instead; this is the     *)
(* strongest adversary because Spend does not read `votes` and every other *)
(* guard (Release) is monotone in `votes`, so any behaviour with lazily    *)
(* added Byzantine votes is simulated, and any Safety violation preserved, *)
(* by the eager one.  MC_lazy.cfg checks the lazy variant on a smaller     *)
(* instance as a cross-check.                                              *)
ByzVote(b, s, g, t) ==
    /\ ~ByzEager
    /\ <<ConsOf(b), b, s, g, t>> \notin votes
    /\ votes' = votes \cup {<<ConsOf(b), b, s, g, t>>}
    /\ UNCHANGED <<header, gen, bound>>

Next ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : Release(w, s)
    \/ \E b \in Byz, s \in Sigils, g \in Gens, t \in Tids : ByzVote(b, s, g, t)

Spec == Init /\ [][Next]_vars

=============================================================================
