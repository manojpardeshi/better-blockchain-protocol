------------------------------- MODULE MC_wallet -------------------------------
(* Model-checking instances for SigilWallet.tla (MC_wallet*.cfg).          *)
(* Home: 3 honest witnesses + 1 Byzantine, n = 4, q = 3, f = 1.  Three     *)
(* transitions that could consume the wallet's parcel: t1 and t3 are       *)
(* payments the wallet builds, t2 is a swap whose header the counter-party *)
(* writes.  Generations 0..1, TTL 1, time 0..3.                             *)
EXTENDS SigilWallet, TLC

WTids      == {"t1", "t2", "t3"}
WSwaps     == {"t2"}
NoSwaps    == {}
SymHonestW == Permutations(Honest)

\* A larger instance (MC_wallet_big.cfg): four transitions, two of them swaps.
WTids4  == {"t1", "t2", "t3", "t4"}
WSwaps4 == {"t2", "t4"}
================================================================================
