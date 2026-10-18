------------------------------- MODULE MC_multi -------------------------------
(* Multi-constellation instances for Sigil.tla (MC_multi*.cfg).  See       *)
(* README.md.  Three constellations:                                       *)
(*   C : HonestC + ByzC   (h1 h2 h3 + z1: n = 4, q = 3, f = 1)             *)
(*   D : HonestD          (h4: n = 1, q = 1, f = 0)                        *)
(*   R : ByzR             (r1: a rogue, all-Byzantine constellation in the *)
(*                         registry; homes no sigil, but r1 can sign any   *)
(*                         vote "from R", hence any R seal, for any sigil) *)
EXTENDS MC

CONSTANTS HonestC, ByzC, HonestD, ByzR      \* model values, set in the cfg

MultiHonest  == HonestC \cup HonestD
MultiByz     == ByzC \cup ByzR
MultiCons    == {"C", "D", "R"}
MultiMembers ==
    [c \in MultiCons |->
        CASE c = "C" -> HonestC \cup ByzC
          [] c = "D" -> HonestD
          [] c = "R" -> ByzR]

\* The hand-picked transitions of MC.tla with a, b homed at C and c homed at
\* D, so t3 = {(b,0),(c,0)} and t4 = {(a,1),(c,2)} span two constellations,
\* and releasing c at D for t3 can use a C seal on (b,0) as death proof.
MultiHomeFixed == [s \in FixedSigils |-> IF s = "c" THEN "D" ELSE "C"]

\* Exhaustive variant: s1 homed at C, s2 homed at D.
MultiAllSigils == {"s1", "s2"}
MultiHomeAll   == [s \in MultiAllSigils |-> IF s = "s1" THEN "C" ELSE "D"]

SymHonestC  == Permutations(HonestC)
SymMultiAll == Permutations(HonestC) \cup Permutations(Tids)
===============================================================================
