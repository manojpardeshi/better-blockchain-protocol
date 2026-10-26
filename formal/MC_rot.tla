------------------------------- MODULE MC_rot -------------------------------
(* Concrete rotation instance for SigilRot.tla (MC_rot*.cfg).               *)
(*                                                                         *)
(* One home "C" with two charter versions, each n=4 q=3 f=1:               *)
(*   v0 = {a0,b0,c0} honest + Z Byzantine                                   *)
(*   v1 = {a1,b1,c1} honest + Z Byzantine (fresh honest keys, Z re-used).   *)
(* Two sigils s, x.  Transitions:                                          *)
(*   Tb = {(s,0),(x,0)}   a two-input spend                                 *)
(*   Ta = {(s,0)}         a conflicting single-input spend of s at gen 0    *)
(*   Ty = {(x,0)}         consumes x, which kills Tb                        *)
(*   Tg = {(s,1)}         spends s at generation 1                          *)
(* This is the scenario behind the ADOPT double-spend: v0 seals (s,0)->Tb   *)
(* and binds (s,0)->Ta; x is consumed by Ty so Tb dies and s is released;   *)
(* after rotation a buggy ADOPT re-opens (s,0) for Ta.                      *)
EXTENDS SigilRot

RotSigils == {"s", "x"}
RotTids   == {"Tb", "Ta", "Ty"}
RotHome   == [sg \in RotSigils |-> "C"]
RotHeader ==
    [t \in RotTids |->
        CASE t = "Tb" -> {<<"s", 0>>, <<"x", 0>>}   \* two-input spend of s and x
          [] t = "Ta" -> {<<"s", 0>>}               \* conflicting single-input spend of s
          [] t = "Ty" -> {<<"x", 0>>}]              \* consumes x, which kills Tb

\* Adds Tg = {(s,1)}: the owner's recovery spend of s at generation 1, so the
\* sibling-mode check also covers release out of CONTESTED and respending.
RotTids4   == RotTids \cup {"Tg"}
RotHeader4 == [t \in RotTids4 |-> IF t = "Tg" THEN {<<"s", 1>>} ELSE RotHeader[t]]

SymHonest == Permutations(Honest0) \cup Permutations(Honest1)
=============================================================================
