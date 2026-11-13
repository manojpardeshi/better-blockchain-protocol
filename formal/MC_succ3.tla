------------------------------- MODULE MC_succ3 -------------------------------
(* Three-version TLC instances of SigilSuccProofs.tla (configs              *)
(* MC_succ_c*.cfg): version 0 has no committee and is ROTATED into          *)
(* version 1, whose charter names a committee; version 1 is then SUCCEEDED *)
(* by version 2.  The committee of version 1 must enter standby with the    *)
(* history version 1 inherited from version 0, or the succession loses it  *)
(* (StandbyR <- StandbyRNoEvidence, defined in MC_succ.tla).                *)
EXTENDS MC_succ

CONSTANTS M2, K2

MCVers3      == {0, 1, 2}
MCMembers3   == [v \in MCVers3 |-> CASE v = 0 -> M0 [] v = 1 -> M1 [] v = 2 -> M2]
MCCommittee3 == [v \in MCVers3 |-> CASE v = 0 -> K0 [] v = 1 -> K1 [] v = 2 -> K2]
MCQuorum3    == [v \in MCVers3 |-> Q(MCMembers3[v])]
MCKQuorum3   == [v \in MCVers3 |-> IF MCCommittee3[v] = {} THEN 0 ELSE Q(MCCommittee3[v])]
MaxQ3 == Q(M0)
G3    == 0..(IF MaxGen + 1 > MaxQ3 THEN MaxGen + 1 ELSE MaxQ3)
MCGenOf3(t, s) == CHOOSE g \in G3 : <<s, g>> \in Header[t]
NoOrAllSeals3 == { [s \in Sigils |-> {}],
                   [s \in Sigils |-> { b \in G3 \X Tids : Sealed(s, b[1], b[2]) }] }
ByzVotes3 == { Vote(v, b, s, g, t) : v \in Vers, b \in Byz, s \in Sigils,
                                     g \in 0..MaxGen, t \in Tids }
MCInit3 == votes = ByzVotes3 /\ InitRecords
MCSpec3 == MCInit3 /\ [][HonestNext]_vars
(* Instance C: one sigil s; Ta and Tb both spend it at generation 0.        *)
TidsC == {"Ta", "Tb"}
HdrC  == [t \in TidsC |-> {<<"s", 0>>}]
MCSymmetry3 == Permutations(M0 \ (M1 \cup M2 \cup K0 \cup K1 \cup K2 \cup Byz))
=============================================================================
