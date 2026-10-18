-------------------------------- MODULE Sigil --------------------------------
(***************************************************************************)
(* The Sigil witness protocol (docs/SPEC.md §3.9, §5.1, §5.2) and its      *)
(* safety theorem (§8): no sigil is an input of two different complete     *)
(* transitions.                                                            *)
(*                                                                         *)
(* One constellation version (no rotation).  Witnesses are split into      *)
(* Honest and Byz.  Owners are fully adversarial: every owner authorises   *)
(* every transition, so any honest witness may receive a spend request for *)
(* any (sigil, transition) pair at any time.  Cryptography is abstracted:  *)
(* a vote is the tuple <<w, s, g, t>> and only w can create it, so         *)
(* Byzantine witnesses can create any vote for themselves and no vote for  *)
(* anyone else.  Votes are public (STATUS, §5.3) and never disappear, so   *)
(* the adversary can always assemble any seal or death proof that the      *)
(* current set of votes supports.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Honest,         \* honest witnesses
    Byz,            \* Byzantine witnesses (vote anything, any time)
    Quorum,         \* q
    Sigils,         \* sigils (all homed at this constellation)
    Tids,           \* transitions
    MaxGen,         \* generations in headers range over 0..MaxGen
    HeaderSpace,    \* set of functions Tids -> headers; Init picks one
    ByzEager,       \* TRUE: Byzantine votes exist from the start (see below)
    AnyProof        \* MUTATION: TRUE makes Release accept any proof

ASSUME Honest \cap Byz = {}
ASSUME Quorum \in Nat /\ Quorum <= Cardinality(Honest \cup Byz)

Witnesses == Honest \cup Byz
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
    votes       \* set of <<w, s, g, t>>: every vote ever cast (honest + Byz)

vars == <<header, gen, bound, votes>>

SigilsOf(t)    == { p[1] : p \in header[t] }
GenOf(t, s)    == CHOOSE g \in Gens : <<s, g>> \in header[t]

(* Distinct witnesses that voted for t at (s, g).                          *)
VotersFor(s, g, t) == { w \in Witnesses : <<w, s, g, t>> \in votes }

(* Distinct witnesses that voted for some tid other than t at (s, g).      *)
VotersAgainst(s, g, t) ==
    { w \in Witnesses : \E u \in Tids \ {t} : <<w, s, g, u>> \in votes }

(* A valid seal for (s, g, t) exists (§3.6).                               *)
Sealed(s, g, t) == Cardinality(VotersFor(s, g, t)) >= Quorum

(* §3.9: a valid death proof for transition t exists.  It names an input   *)
(* [s, g] of t's header -- not necessarily the sigil being released -- and *)
(* is either a seal for another tid at (s, g) or q votes for other tids at *)
(* (s, g).  Byzantine votes count.                                         *)
DeathProofExists(t) ==
    \E p \in header[t] :
        LET s == p[1]  g == p[2] IN
        \/ \E u \in Tids \ {t} : Sealed(s, g, u)                \* kind "seal"
        \/ Cardinality(VotersAgainst(s, g, t)) >= Quorum        \* kind "votes"

(* §8: complete = every input sealed to t at the generation t names.       *)
Complete(t) == \A p \in header[t] : Sealed(p[1], p[2], t)

ByzVotes == Byz \X Sigils \X Gens \X Tids

-----------------------------------------------------------------------------
TypeOK ==
    /\ header \in [Tids -> ValidHeaders]
    /\ gen    \in [Honest -> [Sigils -> 0..(MaxGen + 1)]]
    /\ bound  \in [Honest -> [Sigils -> Tids \cup {NoTid}]]
    /\ votes  \subseteq Witnesses \X Sigils \X Gens \X Tids

(* THEOREM (§8).                                                           *)
Safety ==
    \A t1, t2 \in Tids :
        (t1 # t2 /\ Complete(t1) /\ Complete(t2))
            => SigilsOf(t1) \cap SigilsOf(t2) = {}

(* Auxiliary invariants (the lemmas, and the honest-witness discipline).   *)

\* An honest witness votes at most once per (s, g)  (§5.1, last sentence).
HonestNoEquivocation ==
    \A w \in Honest, s \in Sigils, g \in Gens, t1, t2 \in Tids :
        (<<w, s, g, t1>> \in votes /\ <<w, s, g, t2>> \in votes) => t1 = t2

\* Lemma 1: at most one tid sealed per (s, g).
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
(* adversarial so authorisation (step 3) always passes; steps 1-2 (stamps, *)
(* home) are irrelevant to safety.  Rejections and Conflict replies change *)
(* no state, so they are modelled as the action being disabled.            *)
Spend(w, s, t) ==
    /\ s \in SigilsOf(t)
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
       /\ votes' = votes \cup {<<w, s, g, t>>}
       /\ UNCHANGED header

(* §5.2 RELEASE, honest witness w on sigil s.                              *)
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
    /\ <<b, s, g, t>> \notin votes
    /\ votes' = votes \cup {<<b, s, g, t>>}
    /\ UNCHANGED <<header, gen, bound>>

Next ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : Release(w, s)
    \/ \E b \in Byz, s \in Sigils, g \in Gens, t \in Tids : ByzVote(b, s, g, t)

Spec == Init /\ [][Next]_vars

=============================================================================
