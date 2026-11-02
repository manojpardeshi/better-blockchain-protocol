------------------------------- MODULE MC_rotpw ------------------------------
(* Non-vacuity probes for SigilRotProofs.tla (MC_rotp_witness*.cfg): each   *)
(* config names one probe as an invariant, and TLC must report it VIOLATED, *)
(* i.e. the proved spec really reaches that situation.  The ghost variable  *)
(* ev records which kinds of step happened; the protocol never reads it.    *)
EXTENDS MC_rotp

VARIABLE ev

\* w stays in its version / w enters a version by ADOPT.
Same(w)  == act[w] /\ act'[w] /\ kv'[w] = kv[w]
Moved(w) == act'[w] /\ (~act[w] \/ kv'[w] # kv[w])

\* The kinds of step a transition performs, per honest key and sigil.
Step(k, P(_, _)) == { <<k, p[1], p[2]>> : p \in { q \in Honest \X Sigils : P(q[1], q[2]) } }
Events ==
    \* a contested record is released (every candidate proven dead)
    Step("crel",      LAMBDA w, s : Same(w) /\ bnd[w][s] = Contested /\ bnd'[w][s] = NoTid)
    \* a contested record is settled by a seal (W9)
    \cup Step("resolve",   LAMBDA w, s : Same(w) /\ bnd[w][s] = Contested /\ bnd'[w][s] \in Tids)
    \* ADOPT inherits a lone live binding / makes the record contested
    \cup Step("lone",      LAMBDA w, s : Moved(w) /\ bnd'[w][s] \in Tids)
    \cup Step("contested", LAMBDA w, s : Moved(w) /\ bnd'[w][s] = Contested)
    \* ... in abstention: the key already voted another tid at that generation
    \cup Step("abstain",   LAMBDA w, s : Moved(w) /\ abst'[w][s])

MCSpecW == MCInit /\ ev = {} /\ [][HonestNext /\ ev' = ev \cup Events]_<<vars, ev>>

Happened(k) == \E e \in ev : e[1] = k

\* ---- Probes: each must be VIOLATED ----
NoContestedRelease == ~Happened("crel")
NoContestedResolve == ~Happened("resolve")
NoLoneInherit      == ~Happened("lone")
NoAbstain          == ~Happened("abstain")
\* The owner recovers: Tb was sealed at (s,0) by version 0 (and is dead, x
\* being consumed by Ty, so s is free at generation 1), and after rotation
\* version 1 seals Tg at (s,1).
NoRecoveryAfterRotation == ~(SealedIn(0, "s", 0, "Tb") /\ SealedIn(1, "s", 1, "Tg"))
=============================================================================
