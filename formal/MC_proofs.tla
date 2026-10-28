------------------------------- MODULE MC_proofs -------------------------------
(* Non-vacuity cross-check for the TLAPS proof in SigilProofs.tla.          *)
(*                                                                         *)
(* TLC runs the SAME specification that SigilProofs.tla proves safe, on a  *)
(* concrete instance.  This shows two things the proof itself cannot:       *)
(*   1. the module's ASSUMEs are satisfiable (TLC evaluates every one of    *)
(*      them on this instance), so the unbounded proof is not vacuous;      *)
(*   2. the proved inductive invariant really holds on every reachable      *)
(*      state of the instance, and the instance reaches interesting states  *)
(*      (MC_proofs_witness.cfg must FAIL: some transition becomes complete  *)
(*      and some binding gets released).                                   *)
(* Only two definitions are overridden, and only to make them computable:   *)
(* NoTid (an unbounded CHOOSE) and GenOf (a CHOOSE over Nat; the bounded    *)
(* version returns the same value because headers only use 0..MaxGen).      *)
(* ByzVote's generation is drawn from 0..MaxGen (MCNext), and the           *)
(* invariant's "\A g \in Nat" is restricted to 0..MaxGen+1, which loses     *)
(* nothing: no vote in a reachable state has a larger generation.           *)
EXTENDS SigilProofs, TLC

CONSTANT MaxGen
G == 0..(MaxGen + 1)

MCNoTid == "none"
MCGenOf(t, s) == CHOOSE g \in G : <<s, g>> \in Header[t]

MCNext ==
    \/ \E w \in Honest, s \in Sigils, t \in Tids : Spend(w, s, t)
    \/ \E w \in Honest, s \in Sigils : Release(w, s)
    \/ \E b \in Byz, s \in Sigils, g \in 0..MaxGen, t \in Tids : ByzVote(b, s, g, t)
MCSpec == Init /\ [][MCNext]_vars

(* One constellation C = Honest \cup Byz, q = n - f.                        *)
MCCons    == {"C"}
MCMembers == [c \in MCCons |-> Honest \cup Byz]
MCQuorum  == [c \in MCCons |-> Cardinality(Honest \cup Byz) - (Cardinality(Honest \cup Byz) - 1) \div 3]
MCSigils  == {"a", "b"}
MCHome    == [s \in MCSigils |-> "C"]
MCTids    == {"t1", "t2", "t3"}
(* t1 and t2 conflict on (a,0); t3 spends a at generation 1, so it needs   *)
(* a release of a at generation 0 (possible once t1 or t2 is provably dead) *)
(* or a generation jump by a witness that never bound a at generation 0.   *)
MCHeader  ==
    [t \in MCTids |->
        CASE t = "t1" -> {<<"a", 0>>, <<"b", 0>>}
          [] t = "t2" -> {<<"a", 0>>}
          [] t = "t3" -> {<<"a", 1>>}]

(* The proved invariant, with "g \in Nat" read as "g \in G" (see above).   *)
InvB ==
    /\ TypeOK
    /\ VotesShape
    /\ \A w \in Honest, s \in Sigils, g \in G, t1, t2 \in Tids :
          (HVote(w, s, g, t1) \in votes /\ HVote(w, s, g, t2) \in votes) => t1 = t2
    /\ \A w \in Honest, s \in Sigils, g \in G, t \in Tids :
          HVote(w, s, g, t) \in votes => g <= gen[w][s]
    /\ BoundVote
    /\ \A w \in Honest, s \in Sigils, g \in G, t \in Tids :
          (HVote(w, s, g, t) \in votes /\ g < gen[w][s]) => DeathProofExists(t)
    /\ \A v \in votes : v.gnr \in 0..MaxGen          \* justifies the restriction
OneSealPerGenB ==
    \A s \in Sigils, g \in G, t1, t2 \in Tids :
        (Sealed(s, g, t1) /\ Sealed(s, g, t2)) => t1 = t2

(* Reachability probes: MC_proofs_witness.cfg checks these as invariants    *)
(* and MUST report a violation (i.e. the interesting states are reached).   *)
NoCompletion == \A t \in Tids : ~Complete(t)
NoRelease    == \A w \in Honest, s \in Sigils : gen[w][s] = 0 \/ bound[w][s] # NoTid

SymHonest == Permutations(Honest)
================================================================================
