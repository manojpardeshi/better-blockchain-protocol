------------------------------- MODULE MC_succw ------------------------------
(* Non-vacuity probes for SigilSuccProofs.tla (MC_succ_witness*.cfg): each  *)
(* config names one probe as an invariant, and TLC must report it VIOLATED, *)
(* i.e. the proved spec really reaches that situation.  The ghost variable  *)
(* ev records which kinds of step happened; the protocol never reads it.    *)
(* In these instances version 1 can be adopted by rotation only if a        *)
(* freezing quorum of version 0 exists; the probes that are about a         *)
(* SUCCESSION require that no member of version 0 froze (fr[0] = {}).       *)
EXTENDS MC_succ

VARIABLE ev

\* w enters a version by ADOPT.
Moved(w) == act'[w] /\ (~act[w] \/ kv'[w] # kv[w])

Step(k, P(_, _)) == { <<k, p[1], p[2]>> : p \in { q \in Honest \X Sigils : P(q[1], q[2]) } }
Events ==
    \* ADOPT from a succession inherits a lone binding / makes the record contested
    Step("lone_s", LAMBDA w, s : Moved(w) /\ fr[0] = {} /\ bnd'[w][s] \in Tids)
    \cup Step("cont_s", LAMBDA w, s : Moved(w) /\ fr[0] = {} /\ bnd'[w][s] = Contested)
    \* an honest member of version 0 casts a NEW vote after a standby member of
    \* version 0's committee has signed a successor: the old quorum comes back
    \cup { <<"late", x.wit, x.sgl>> : x \in { y \in votes' \ votes :
                                                y.wit \in Honest /\ y.ver = 0 /\ fz[0] # {} } }

MCSpecW == MCInit /\ ev = {} /\ [][HonestNext /\ ev' = ev \cup Events]_<<vars, ev>>

Happened(k) == \E e \in ev : e[1] = k

\* ---- Probes: each must be VIOLATED ----
NoLoneSuccession      == ~Happened("lone_s")
NoContestedSuccession == ~Happened("cont_s")
NoLateOldVote         == ~Happened("late")
\* The successor version seals something after a succession.
NoSuccessorSeal == ~(fr[0] = {} /\ \E g \in 0..MaxGen, t \in Tids : SealedIn(1, "s", g, t))
\* The owner recovers through a succession: version 0 sealed Tb at (s,0)
\* (Tb is dead: Ty consumes x), and after the succession version 1 seals the
\* recovery spend Tg at (s,1) (instance B).
NoRecoveryAfterSuccession ==
    ~(fr[0] = {} /\ SealedIn(0, "s", 0, "Tb") /\ SealedIn(1, "s", 1, "Tg"))
=============================================================================
