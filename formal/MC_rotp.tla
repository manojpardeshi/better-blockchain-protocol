------------------------------- MODULE MC_rotp -------------------------------
(* TLC instances of SigilRotProofs.tla, the rotation spec the TLAPS proof   *)
(* is about (configs MC_rotp*.cfg).  TLC explores the PROVED spec itself:   *)
(* it re-checks the inductive invariant Inv and the theorems on reachable   *)
(* states, shows the spec is not vacuous (MC_rotp_witness*.cfg, module      *)
(* MC_rotpw.tla), and shows that the conditions of the proved ADOPT rule    *)
(* and of W9 seal settlement are needed (the *_mutant configs).             *)
(*                                                                         *)
(* Only computability overrides, in the .cfg files:                        *)
(*   Nat <- G (0..MaxGen+1, and the quorum sizes); NoTid, Contested, GenOf  *)
(*   (unbounded CHOOSE); GenOK / CandGenOK <- the EXACT generation that     *)
(*   sigil/witness.py picks (the spec allows any generation at least that   *)
(*   high); ForgeBinds / ForgeDead / ForgeSeals <- small sets of evidence   *)
(*   the Byzantine member of a freezing quorum may add (Adopt still checks  *)
(*   a forged release has a death proof and a forged seal really exists).   *)
(* Byzantine votes are eager (MCSpec): every vote a Byzantine key could    *)
(* sign exists from the start.  Every MCSpec state is reachable in Spec    *)
(* (Spec can cast those votes first, ByzVote is always enabled), so Inv    *)
(* must hold on all of them, and a safety violation of Spec is never       *)
(* hidden: Spend, Freeze and Adopt's quorum conditions never read votes,   *)
(* and the guards that do (death proofs, seals) are monotone in votes.     *)
(*                                                                         *)
(* Mutations, by overriding the proved rule:                                *)
(*   LoneOK    <- LoneSibling  the FIRST sibling rule (inherit a lone live  *)
(*                             binding if nothing else is bound AT its gen) *)
(*   LoneOK    <- LoneNoOwn    the implemented rule minus the own-vote      *)
(*                             condition (re-used keys)                     *)
(*   ResolveOK <- ResolveAny   W9 seal settlement minus the own-vote        *)
(*                             condition                                    *)
(*   ResolveTop <- ResolveTopAny  W9 seal settlement minus `top <= g + 1`   *)
EXTENDS SigilRotProofs, TLC

CONSTANTS MaxGen, M0, M1     \* header generations 0..MaxGen; members of v0, v1

MCVers    == {0, 1}
MCMembers == [v \in MCVers |-> IF v = 0 THEN M0 ELSE M1]
MCQuorum  == [v \in MCVers |-> Cardinality(MCMembers[v]) - (Cardinality(MCMembers[v]) - 1) \div 3]

\* Nat is read as G: generations reach at most MaxGen + 1 (a release at
\* MaxGen), and G must also contain the quorum sizes (QuorumType).
MaxQ == IF MCQuorum[0] > MCQuorum[1] THEN MCQuorum[0] ELSE MCQuorum[1]
G    == 0..(IF MaxGen + 1 > MaxQ THEN MaxGen + 1 ELSE MaxQ)

MCNoTid     == "none"
MCContested == "!contested"
MCGenOf(t, s) == CHOOSE g \in G : <<s, g>> \in Header[t]

Max(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S : \A k \in S : k <= m

\* The generation sigil/witness.py gives a contested or unbound record
\* (Witness.adopt: floor, raised past the own votes when nothing is alive).
AdoptGen(EB, ED, O) ==
    Max({ IF b[2] \in ED THEN b[1] + 1 ELSE b[1] : b \in EB }
        \cup (IF Alive(EB, ED) = {} THEN { o[1] + 1 : o \in O } ELSE {}))
MCGenOK(EB, ED, O, ng) == ng = AdoptGen(EB, ED, O)
\* Witness._release_contested: past the killed candidate; once none is
\* left, past the key's own votes.
MCCandGenOK(g0, c, rest, O, ng) ==
    ng = Max({g0, c[1] + 1} \cup (IF rest = {} THEN { o[1] + 1 : o \in O } ELSE {}))

\* ---- Mutations of the proved rule (each must be caught by TLC) ----
\* The first sibling rule (the first fix of Bug 1): a lone live binding is
\* inherited if no other binding is AT its generation (Bugs 3 and 4).
LoneSibling(EB, ES, O, b) == \A b2 \in EB : b2 # b => b2[1] # b[1]
\* The implemented rule without "and the key's own votes are at most g".
LoneNoOwn(EB, ES, O, b) ==
    \A b2 \in EB : b2 # b => (b2[1] < b[1] \/ (b \in ES /\ b2[1] = b[1]))
\* W9 seal settlement without "the key's own votes are at most g".
ResolveAny(w, s, b) == TRUE
\* W9 seal settlement without "top <= g + 1" (a later generation passed over).
ResolveTopAny(w, s, b) == TRUE

\* ---- Byzantine evidence a freezing quorum's Byzantine member may add ----
NoForgeB == { [s \in Sigils |-> {}] }
NoForgeD == { [s \in Sigils |-> {}] }
\* Seal entries: none, or every seal that exists in the current state.  The
\* evidence's seals only matter through LoneOK ("is the lone binding
\* sealed?"), and these two choices give both answers whenever a seal
\* exists, so the reachable states are those of any other choice of seals.
NoOrAllSeals == { [s \in Sigils |-> {}],
                  [s \in Sigils |-> { b \in G \X Tids : Sealed(s, b[1], b[2]) }] }

ByzVotes == { Vote(v, b, s, g, t) : v \in Vers, b \in Byz, s \in Sigils,
                                    g \in 0..MaxGen, t \in Tids }
MCInit == votes = ByzVotes /\ InitRecords
MCSpec == MCInit /\ [][HonestNext]_vars

(* Sigils s, x.  Transitions (x consumed by Ty kills Tb and Tu):           *)
(*   Ty = {(x,0)}   Tb = {(s,0),(x,0)}   Ta = {(s,0)}                       *)
(*   Tu = {(s,1),(x,0)}   Tg = {(s,1)}                                      *)
MCSigils == {"s", "x"}
Hdr(t) ==
    CASE t = "Tb" -> {<<"s", 0>>, <<"x", 0>>}
      [] t = "Ta" -> {<<"s", 0>>}
      [] t = "Ty" -> {<<"x", 0>>}
      [] t = "Tu" -> {<<"s", 1>>, <<"x", 0>>}
      [] t = "Tg" -> {<<"s", 1>>}
\* The Bug 1 scenario: two tids bound at (s,0), Tb killed through x; Tg is
\* the recovery spend at generation 1 (contested state, contested release,
\* W9 seal settlement, lone inheritance, own-vote abstention).
TidsSib == {"Tb", "Ta", "Ty", "Tg"}
\* The Bugs 3/4 scenario: Tb bound at (s,0) below Tu, sealed at (s,1) and
\* then killed through x; Tg spends s at generation 1 again.
TidsCex == {"Tb", "Tu", "Ty", "Tg"}
HdrSib == [t \in TidsSib |-> Hdr(t)]
HdrCex == [t \in TidsCex |-> Hdr(t)]

\* h2 and h3 play the same role in both instances.
MCSymmetry == Permutations(M0 \ (M1 \cup Byz))
=============================================================================
