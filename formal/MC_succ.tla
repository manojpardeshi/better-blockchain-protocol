------------------------------- MODULE MC_succ -------------------------------
(* TLC instances of SigilSuccProofs.tla, the succession spec the TLAPS     *)
(* proof is about (configs MC_succ*.cfg).  TLC explores the PROVED spec    *)
(* itself: it re-checks the inductive invariant Inv and the theorems on    *)
(* reachable states, shows that the spec is not vacuous (MC_succ_witness*, *)
(* module MC_succw.tla), and that each part of the succession discipline   *)
(* is needed (the *_mutant configs).                                        *)
(*                                                                         *)
(* Only computability overrides, in the .cfg files, as in MC_rotp.tla:     *)
(*   Nat <- G; NoTid, Contested, GenOf; GenOK / CandGenOK <- the exact     *)
(*   generation sigil/witness.py picks; ForgeBinds / ForgeDead /            *)
(*   ForgeSeals <- small sets of Byzantine evidence.                        *)
(* Byzantine votes are eager (MCSpec), a sound over-approximation (see     *)
(* MC_rotp.tla).                                                            *)
(*                                                                         *)
(* Mutations, by overriding one definition of the proved spec:              *)
(*   MirQ      <- MirAny            witnesses vote without mirror acks      *)
(*                                  (no mirror before vote)                 *)
(*   MirrorAck <- MirrorAckNoFence  standby members keep storing after they *)
(*                                  signed a successor (no fence)           *)
(*   AdoptS    <- AdoptSNoQuorum    the successor adopts from fewer than a  *)
(*                                  committee quorum                         *)
(*   StandbyR  <- StandbyRNoEvidence a committee enters standby without the  *)
(*                                  history its version inherited (three    *)
(*                                  versions: module MC_succ3.tla)          *)
EXTENDS SigilSuccProofs, TLC

CONSTANTS MaxGen, M0, M1, K0, K1   \* header generations 0..MaxGen; members and committees

MCVers      == {0, 1}
MCMembers   == [v \in MCVers |-> IF v = 0 THEN M0 ELSE M1]
MCCommittee == [v \in MCVers |-> IF v = 0 THEN K0 ELSE K1]
Q(S)        == Cardinality(S) - (Cardinality(S) - 1) \div 3
MCQuorum    == [v \in MCVers |-> Q(MCMembers[v])]
MCKQuorum   == [v \in MCVers |-> IF MCCommittee[v] = {} THEN 0 ELSE Q(MCCommittee[v])]

\* Nat is read as G: generations reach at most MaxGen + 1 (a release at
\* MaxGen), and G must also contain the quorum sizes (QuorumType).
MaxQ == IF MCQuorum[0] > MCQuorum[1] THEN MCQuorum[0] ELSE MCQuorum[1]
G    == 0..(IF MaxGen + 1 > MaxQ THEN MaxGen + 1 ELSE MaxQ)

MCNoTid     == "none"
MCContested == "!contested"
MCGenOf(t, s) == CHOOSE g \in G : <<s, g>> \in Header[t]

Max(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S : \A k \in S : k <= m

\* The generations sigil/witness.py picks (as in MC_rotp.tla).
AdoptGen(EB, ED, O) ==
    Max({ IF b[2] \in ED THEN b[1] + 1 ELSE b[1] : b \in EB }
        \cup (IF Alive(EB, ED) = {} THEN { o[1] + 1 : o \in O } ELSE {}))
MCGenOK(EB, ED, O, ng) == ng = AdoptGen(EB, ED, O)
MCCandGenOK(g0, c, rest, O, ng) ==
    ng = Max({g0, c[1] + 1} \cup (IF rest = {} THEN { o[1] + 1 : o \in O } ELSE {}))

\* ---- Mutations of the succession discipline (each must be caught) ----
\* No mirror before vote: a witness of a version with a committee votes
\* without a committee quorum having stored the binding.
MirAny(v, s, g, t) == TRUE
\* No fence: a standby member keeps storing after it signed a successor.
MirrorAckNoFence(m, v, s, b) ==
    /\ m \in Committee[v]
    /\ <<s, b[1]>> \in Header[b[2]]
    /\ mir' = [mir EXCEPT ![v][m][s] = @ \cup {b}]
    /\ UNCHANGED <<votes, act, kv, adv, frz, gen, bnd, cand, abst, lg, ld, fr, sb, sd, hev, fz, sa>>
\* A succession signed by fewer than a quorum of the committee (here: by
\* any fenced subset, the empty one included).
AdoptSNoQuorum(w, v, T, XB, XD, XS, NG) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ HasSucc(v - 1)
    /\ T \subseteq Committee[v - 1]
    /\ T \cap Honest \subseteq fz[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ XD \in [Sigils -> SUBSET Tids]
    /\ \A s \in Sigils : \A t \in XD[s] : DeathProof(t)
    /\ AdoptCore(w, v, [s \in Sigils |-> EvM(v - 1, T, XB, s)], XD, XS, NG)
\* A committee enters standby after a rotation WITHOUT the freezing quorum's
\* snapshots (what its version inherited): its mirror then misses history.
StandbyRNoEvidence(m, v, F, XB) ==
    /\ v \in Vers /\ v >= 1 /\ v - 1 \in Vers
    /\ F \subseteq Members[v - 1]
    /\ Cardinality(F) >= Quorum[v - 1]
    /\ F \cap Honest \subseteq fr[v - 1]
    /\ XB \in [Sigils -> SUBSET (Nat \X Tids)]
    /\ StandbyCore(m, v, XB)

\* ---- Byzantine evidence (as in MC_rotp.tla) ----
NoForgeB == { [s \in Sigils |-> {}] }
NoForgeD == { [s \in Sigils |-> {}] }
NoOrAllSeals == { [s \in Sigils |-> {}],
                  [s \in Sigils |-> { b \in G \X Tids : Sealed(s, b[1], b[2]) }] }

ByzVotes == { Vote(v, b, s, g, t) : v \in Vers, b \in Byz, s \in Sigils,
                                    g \in 0..MaxGen, t \in Tids }
MCInit == votes = ByzVotes /\ InitRecords
MCSpec == MCInit /\ [][HonestNext]_vars

(* Instance A, one sigil s: Ta and Tb both spend s at generation 0 (an     *)
(* equivocating owner), Tg spends it at generation 1.                       *)
SigilsA == {"s"}
TidsA   == {"Ta", "Tb", "Tg"}
HdrA    == [t \in TidsA |-> IF t = "Tg" THEN {<<"s", 1>>} ELSE {<<"s", 0>>}]

(* Instance B, sigils s and x: recovery through a succession.              *)
(*   Ty = {(x,0)}  Tb = {(s,0),(x,0)}  Tg = {(s,1)}                         *)
(* Ty consumes x and so kills Tb (sealed at (s,0) or not); Tg is the        *)
(* owner's recovery spend at generation 1.  (With the equivocating          *)
(* Ta = {(s,0)} of instance A added, the state space passes 350,000 states *)
(* without finishing; instance A covers equivocation.)                      *)
SigilsB == {"s", "x"}
TidsB   == {"Tb", "Ty", "Tg"}
HdrB    == [t \in TidsB |->
              CASE t = "Tb" -> {<<"s", 0>>, <<"x", 0>>}
                [] t = "Ty" -> {<<"x", 0>>}
                [] t = "Tg" -> {<<"s", 1>>}]

\* Old members that play the same role are interchangeable.
MCSymmetry == Permutations(M0 \ (M1 \cup K0 \cup K1 \cup Byz))
=============================================================================
