---------------------------------- MODULE MC ----------------------------------
(* Model-checking instances for Sigil.tla.  See README.md.                 *)
EXTENDS Sigil, TLC

\* Hand-picked transitions over sigils a, b, c that exercise every rule:
\*   t1 vs t2   conflict on (a,0)                     (Lemma 1, Conflict reply)
\*   t1 vs t3   conflict on (b,0): a death proof for  (multi-input death proof:
\*              t1 via b frees a for t2 / t4           release a using b's votes)
\*   t4         a at gen 1 (needs a release of a@0), c at gen 2 (generation jump)
FixedSigils == {"a", "b", "c"}
FixedTids   == {"t1", "t2", "t3", "t4"}
FixedHeader ==
    [t \in FixedTids |->
        CASE t = "t1" -> {<<"a", 0>>, <<"b", 0>>}
          [] t = "t2" -> {<<"a", 0>>}
          [] t = "t3" -> {<<"b", 0>>, <<"c", 0>>}
          [] t = "t4" -> {<<"a", 1>>, <<"c", 2>>}]
FixedHeaders == {FixedHeader}

\* Every possible assignment of valid headers to transitions.
AllHeaders == [Tids -> ValidHeaders]

SymHonest == Permutations(Honest)
SymAll    == Permutations(Honest) \cup Permutations(Sigils) \cup Permutations(Tids)
===============================================================================
