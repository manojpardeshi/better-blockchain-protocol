------------------------------- MODULE SigilWallet -------------------------------
(* The honest WALLET (sigil/wallet.py, sigil/wallet_store.py, sigil/swap.py) *)
(* composed with the witness protocol of its parcel's home (SPEC 5.1, 5.2).  *)
(*                                                                         *)
(* One parcel with sigil s, held by an honest wallet.  The home has honest  *)
(* witnesses (SPEC 5.1 SPEND with owner-signed expiry, 5.2 RELEASE) and up  *)
(* to f Byzantine ones, which vote for anything (eagerly, as in Sigil.tla)  *)
(* and always answer STATUS with "unbound".  The wallet wants to spend s in *)
(* one of several transitions: plain payments it builds itself, and SWAPS   *)
(* whose header a counter-party builds (the counter-party's own input is    *)
(* abstracted to cp[t]: it gets sealed to t, or is consumed elsewhere so t  *)
(* is dead, or neither -- at any time, adversarially).                      *)
(*                                                                         *)
(* Adversarial environment: every authorisation the wallet ever signed is   *)
(* "in flight" forever, so any honest witness may receive it at ANY later   *)
(* time (network delay); seal rounds may fail at any point (SealFail);      *)
(* the wallet may crash and restart from its last save (Crash); anybody may *)
(* release an honest witness with a valid death proof (Release).  Time is   *)
(* one global clock: the clock-skew arithmetic of the expiry rule is        *)
(* checked separately, with drifting clocks, in SigilExpiry.tla.            *)
(*                                                                         *)
(* Wallet actions mirror the code:                                          *)
(*   Authorise  Wallet.authorise (pledge (g,t), sign with expiry now+TTL)   *)
(*   SealFail   a seal round raised SealFailed (Wallet.transact / cmd_pay)  *)
(*   Finalise   Wallet.finalise after a complete seal                       *)
(*   Unpledge   Wallet.unpledge_if_unbound (SPEC 4 rule 3)                  *)
(*   Abort      Wallet.abort with a death proof (find_death_proof, SPEC 5.2)*)
(*   Crash      restart from wallet_store.load of the last save              *)
(* and the flags choose between the CURRENT code and the proposed FIXES     *)
(* (docs/VERIFICATION.md, "Wallet"):                                         *)
(*   GenCheck          FALSE = current Wallet.authorise: it signs whatever  *)
(*                     generation a counter-party's header names for our    *)
(*                     sigil, and only refuses a different tid at the SAME  *)
(*                     generation as the pledge (overwriting a pledge at    *)
(*                     another generation).  TRUE = header gen must equal   *)
(*                     the wallet's gen and any other live pledge refuses.  *)
(*   RetainPending     FALSE = current code: after SealFailed the header and *)
(*                     body are dropped and are never persisted, so the     *)
(*                     wallet can neither complete nor abort the transition.*)
(*   AbortNeedsQuorum  TRUE = current Wallet.abort: the pledge is dropped    *)
(*                     only if a quorum of witnesses RELEASED; witnesses     *)
(*                     that were never bound do not count.                  *)
(*   SaveOnAuthorise   TRUE = sigil/cli.py cmd_pay (saves the pledge before  *)
(*                     any request); FALSE = library Wallet.pay/transact,   *)
(*                     where the caller can save only after the call.       *)
(* Pure mutations (each must be caught): IgnoreExpiry (unpledge without the  *)
(* expiry condition), StatusAnswers < |Honest| (unpledge trusting only some *)
(* members' STATUS), AbortNoProof (abort without a death proof).            *)
EXTENDS Integers, FiniteSets

CONSTANTS
    Honest, Byz,        \* witnesses of the parcel's home
    Q,                  \* quorum q = n - f
    Tids,               \* transitions that could consume s
    Swaps,              \* the subset whose header a counter-party writes
    MaxGen,             \* generations 0..MaxGen
    TTL,                \* Wallet.pledge_ttl: expires = now + TTL
    MAXT,               \* bound on time, for TLC (then FOREVER, below)
    GenCheck, RetainPending, AbortNeedsQuorum, SaveOnAuthorise, CrashOn,
    IgnoreExpiry, StatusAnswers, AbortNoProof

ASSUME Honest \cap Byz = {}
ASSUME Q \in Nat /\ Cardinality(Byz) < Q /\ Q <= Cardinality(Honest \cup Byz)
\* q = n - f with f = floor((n-1)/3), at most f Byzantine (SPEC 8).
ASSUME LET n == Cardinality(Honest \cup Byz) IN
       Q = n - (n - 1) \div 3 /\ Cardinality(Byz) <= (n - 1) \div 3
ASSUME Swaps \subseteq Tids
ASSUME StatusAnswers \in 0..Cardinality(Honest)

Witnesses == Honest \cup Byz
Gens  == 0..MaxGen
Times == 0..(MAXT + TTL)
\* "The far future": later than every expiry ever signed.  Time reaches it
\* after MAXT, so a bounded run still lets every authorisation expire (the
\* wallet signs nothing new there).  Without it, liveness counterexamples
\* would be artefacts of the time bound.
FOREVER == MAXT + TTL + 1
NoTid == "none"
NoP   == <<-1, NoTid>>               \* no pledge
ASSUME NoTid \notin Tids

VARIABLES
    now,        \* the clock (wallet and witnesses; skew: SigilExpiry.tla)
    \* -- the wallet's volatile state (lost on a crash) --
    wgen,       \* Holdings gen of the parcel (the generation it will sign)
    pledge,     \* Wallet.pledged[s]: <<g, t>> or NoP
    fin,        \* the tid the wallet finalised (parcel left holdings) or NoTid
    known,      \* tids whose header/body the wallet still has (can retry/abort)
    saved,      \* what wallet_store.load would restore
    \* -- the world --
    hg,         \* hg[t]: the generation t's header names for s (-1: no header yet)
    exp,        \* exp[<<g,t>>]: latest `expires` the wallet ever signed (-1: never)
    relU,       \* ghost: <<g,t>> pledges dropped by Unpledge
    relA,       \* ghost: <<g,t>> pledges dropped by Abort
    gen, bound, \* honest witness records for s (Record.gen / Record.tid)
    votes,      \* every vote on s: <<w, g, t>>
    cp          \* cp[t] for swaps: "none" | "sealed" | "dead" (counter-party leg)

wallet == <<wgen, pledge, fin, known>>
vars == <<now, wgen, pledge, fin, known, saved, hg, exp, relU, relA, gen, bound, votes, cp>>

Max(a, b) == IF a > b THEN a ELSE b

Voters(g, t)  == { w \in Witnesses : <<w, g, t>> \in votes }
Against(g, t) == { w \in Witnesses : \E u \in Tids : u # t /\ <<w, g, u>> \in votes }
Sealed(g, t)  == Cardinality(Voters(g, t)) >= Q

\* t is complete: s sealed to t at the generation its header names, and the
\* counter-party's leg (for a swap) sealed too.
Complete(t) == hg[t] # -1 /\ Sealed(hg[t], t) /\ (t \in Swaps => cp[t] = "sealed")

\* A death proof for t exists (SPEC 3.9): s's generation is sealed to another
\* tid, or q votes there are for other tids, or the counter-party's input is
\* provably consumed elsewhere.
Dead(t) ==
    /\ hg[t] # -1
    /\ \/ \E u \in Tids : u # t /\ Sealed(hg[t], u)
       \/ Cardinality(Against(hg[t], t)) >= Q
       \/ t \in Swaps /\ cp[t] = "dead"

Persist(g, p, f, k) == [wgen |-> g, pledge |-> p, fin |-> f,
                        known |-> IF RetainPending THEN k ELSE {}]

ByzVotes == { <<b, g, t>> : b \in Byz, g \in Gens, t \in Tids }

-----------------------------------------------------------------------------
TypeOK ==
    /\ now \in 0..MAXT \cup {FOREVER}
    /\ wgen \in 0..(MaxGen + 1)
    /\ pledge \in (Gens \X Tids) \cup {NoP}
    /\ fin \in Tids \cup {NoTid}
    /\ known \subseteq Tids
    /\ hg \in [Tids -> Gens \cup {-1}]
    /\ exp \in [Gens \X Tids -> Times \cup {-1}]
    /\ relU \subseteq Gens \X Tids /\ relA \subseteq Gens \X Tids
    /\ gen \in [Honest -> 0..(MaxGen + 1)]
    /\ bound \in [Honest -> Tids \cup {NoTid}]
    /\ votes \subseteq Witnesses \X Gens \X Tids
    /\ cp \in [Tids -> {"none", "sealed", "dead"}]

Init ==
    /\ now = 0
    /\ wgen = 0 /\ pledge = NoP /\ fin = NoTid /\ known = {}
    /\ saved = Persist(0, NoP, NoTid, {})
    /\ hg = [t \in Tids |-> -1]
    /\ exp = [p \in Gens \X Tids |-> -1]
    /\ relU = {} /\ relA = {}
    /\ gen = [w \in Honest |-> 0]
    /\ bound = [w \in Honest |-> NoTid]
    /\ votes = ByzVotes
    /\ cp = [t \in Tids |-> "none"]

Tick == now # FOREVER /\ now' = (IF now < MAXT THEN now + 1 ELSE FOREVER)
        /\ UNCHANGED <<wgen, pledge, fin, known, saved, hg, exp, relU, relA, gen, bound, votes, cp>>

\* ---------------------------------------------------------------- witnesses
\* SPEC 5.1 step 4 for an honest witness, on any authorisation the wallet
\* ever signed for t (delivered at any time).  A NEW binding (including a
\* generation jump) needs now <= expires; re-voting an existing one does not.
Spend(w, t) ==
    LET g == hg[t] IN
    /\ g # -1 /\ exp[<<g, t>>] # -1
    /\ \/ g > gen[w] /\ bound[w] = NoTid
       \/ g = gen[w] /\ bound[w] \in {NoTid, t}
    /\ bound[w] = NoTid => now <= exp[<<g, t>>]
    /\ gen' = [gen EXCEPT ![w] = g]
    /\ bound' = [bound EXCEPT ![w] = t]
    /\ votes' = votes \cup {<<w, g, t>>}
    /\ UNCHANGED <<now, wgen, pledge, fin, known, saved, hg, exp, relU, relA, cp>>

\* SPEC 5.2: anyone holding a death proof may release an honest witness.
Release(w) ==
    /\ bound[w] # NoTid /\ Dead(bound[w])
    /\ gen' = [gen EXCEPT ![w] = @ + 1]
    /\ bound' = [bound EXCEPT ![w] = NoTid]
    /\ UNCHANGED <<now, wgen, pledge, fin, known, saved, hg, exp, relU, relA, votes, cp>>

\* The counter-party's own leg of a swap, at any time.
CpSeal(t) == t \in Swaps /\ hg[t] # -1 /\ cp[t] = "none" /\ cp' = [cp EXCEPT ![t] = "sealed"]
             /\ UNCHANGED <<now, wgen, pledge, fin, known, saved, hg, exp, relU, relA, gen, bound, votes>>
CpKill(t) == t \in Swaps /\ cp[t] = "none" /\ cp' = [cp EXCEPT ![t] = "dead"]
             /\ UNCHANGED <<now, wgen, pledge, fin, known, saved, hg, exp, relU, relA, gen, bound, votes>>

\* ------------------------------------------------------------------- wallet
\* Wallet.authorise of t, whose header names generation g for s.  The wallet
\* builds payment headers itself (g = its gen); a swap header comes from the
\* counter-party, which may name any generation.  Re-authorising a tid needs
\* its header (still known, or re-sent by the counter-party).
Authorise(t, g) ==
    /\ fin = NoTid /\ now # FOREVER
    /\ hg[t] \in {-1, g}
    /\ hg[t] # -1 => (t \in known \/ t \in Swaps)
    /\ IF t \in Swaps /\ ~GenCheck THEN TRUE ELSE g = wgen
    /\ IF GenCheck
         THEN pledge = NoP \/ pledge[2] = t
         ELSE pledge = NoP \/ pledge[1] # g \/ pledge[2] = t   \* the code's guard
    /\ LET e == Max(exp[<<g, t>>], now + TTL) IN
       /\ exp' = [exp EXCEPT ![<<g, t>>] = e]
       /\ hg' = [hg EXCEPT ![t] = g]
       /\ pledge' = <<g, t>>
       /\ known' = known \cup {t}
       /\ relU' = relU \ {<<g, t>>}         \* re-signed: live again
       /\ relA' = relA \ {<<g, t>>}
       /\ saved' = IF SaveOnAuthorise THEN Persist(wgen, <<g, t>>, fin, known \cup {t}) ELSE saved
    /\ UNCHANGED <<now, wgen, fin, gen, bound, votes, cp>>

\* A seal round failed.  The current code forgets the header and body.
SealFail(t) ==
    /\ ~RetainPending /\ fin = NoTid /\ t \in known
    /\ known' = known \ {t}
    /\ saved' = Persist(wgen, pledge, fin, known \ {t})
    /\ UNCHANGED <<now, wgen, pledge, fin, hg, exp, relU, relA, gen, bound, votes, cp>>

\* Wallet.finalise: the wallet saw t complete; the parcel leaves holdings.
Finalise(t) ==
    /\ fin = NoTid /\ t \in known /\ Complete(t)
    /\ fin' = t
    /\ saved' = Persist(wgen, pledge, t, known)
    /\ UNCHANGED <<now, wgen, pledge, known, hg, exp, relU, relA, gen, bound, votes, cp>>

\* Wallet.unpledge_if_unbound (SPEC 4 rule 3): past the expiry, and the
\* STATUS of (all) honest members shows no binding or vote for (g, t).
\* Byzantine members always answer "unbound".
Unpledge ==
    /\ pledge # NoP /\ fin = NoTid
    /\ LET g == pledge[1]  t == pledge[2] IN
       /\ IgnoreExpiry \/ now > exp[<<g, t>>]
       /\ \E S \in SUBSET Honest :
             /\ Cardinality(S) >= StatusAnswers
             /\ \A w \in S : ~(gen[w] = g /\ bound[w] = t) /\ <<w, g, t>> \notin votes
       /\ pledge' = NoP
       /\ relU' = relU \cup {<<g, t>>}
       /\ known' = known \ {t}
       /\ saved' = Persist(wgen, NoP, fin, known \ {t})
    /\ UNCHANGED <<now, wgen, fin, hg, exp, relA, gen, bound, votes, cp>>

\* Wallet.abort: with a death proof, every honest witness bound to t releases
\* (Byzantine ones claim to).  The current code drops the pledge and moves
\* to g+1 only if a quorum released; the fix drops it on the proof alone.
Abort ==
    /\ pledge # NoP /\ fin = NoTid
    /\ LET g == pledge[1]  t == pledge[2]
           R == IF Dead(t) THEN { w \in Honest : gen[w] = g /\ bound[w] = t } ELSE {}
           ok == ~AbortNeedsQuorum \/ Cardinality(R) + Cardinality(Byz) >= Q
       IN
       /\ t \in known
       /\ AbortNoProof \/ Dead(t)
       /\ gen' = [w \in Honest |-> IF w \in R THEN gen[w] + 1 ELSE gen[w]]
       /\ bound' = [w \in Honest |-> IF w \in R THEN NoTid ELSE bound[w]]
       /\ IF ok
            THEN /\ pledge' = NoP /\ wgen' = g + 1 /\ known' = known \ {t}
                 /\ relA' = relA \cup {<<g, t>>}
                 /\ saved' = Persist(g + 1, NoP, fin, known \ {t})
            ELSE UNCHANGED <<pledge, wgen, known, relA, saved>>
    /\ UNCHANGED <<now, fin, hg, exp, relU, votes, cp>>

\* The wallet process dies and restarts from its last save.
Crash ==
    /\ CrashOn
    /\ wgen' = saved.wgen /\ pledge' = saved.pledge /\ fin' = saved.fin /\ known' = saved.known
    /\ UNCHANGED <<now, saved, hg, exp, relU, relA, gen, bound, votes, cp>>

Next ==
    \/ Tick
    \/ \E w \in Honest, t \in Tids : Spend(w, t)
    \/ \E w \in Honest : Release(w)
    \/ \E t \in Tids : CpSeal(t) \/ CpKill(t)
    \/ \E t \in Tids, g \in Gens : Authorise(t, g)
    \/ \E t \in Tids : SealFail(t) \/ Finalise(t)
    \/ Unpledge \/ Abort \/ Crash

Spec == Init /\ [][Next]_vars
\* For the liveness check: time passes, and the wallet keeps trying to
\* recover (Wallet.select calls release_expired_pledges; abort is retried).
LiveSpec == Spec /\ WF_vars(Tick) /\ WF_vars(Unpledge) /\ WF_vars(Abort)

-----------------------------------------------------------------------------
Rel == relU \cup relA

\* (a) No self-equivocation: two different tids the wallet signed at one
\* generation always include one it released (provably unsealable, below).
NoSelfEquiv ==
    \A g \in Gens, t1, t2 \in Tids :
        (t1 # t2 /\ exp[<<g, t1>>] # -1 /\ exp[<<g, t2>>] # -1)
            => (<<g, t1>> \in Rel \/ <<g, t2>> \in Rel)

\* (b) A pledge dropped on expiry is never sealed, ever after; one dropped on
\* a death proof never completes.
UnpledgeSound == \A p \in relU : ~Sealed(p[1], p[2])
AbortSound    == \A p \in relA : ~Complete(p[2])

\* (d) The parcel is consumed at most once (recovery never double-spends).
OneComplete == \A t1, t2 \in Tids : (Complete(t1) /\ Complete(t2)) => t1 = t2

\* (c) A payment the wallet reports complete is complete; and while the wallet
\* still shows the parcel, any transition that consumed it is one the wallet
\* can still finalise (it has the header).
PaidIsComplete == fin # NoTid => Complete(fin)
HeldIsTracked  == fin = NoTid => \A t \in Tids : Complete(t) => t \in known

\* Recovery: a pledged transition that is provably dead is eventually
\* abandoned (the parcel becomes spendable again).
RecoveryLive ==
    \A t \in Tids :
        (fin = NoTid /\ pledge[2] = t /\ Dead(t)) ~> (fin # NoTid \/ pledge[2] # t)

\* Non-vacuity (MC_wallet_witness*.cfg, EXPECTED to be violated).
NoPaymentAfterAbort    == ~(relA # {} /\ fin # NoTid)
NoPaymentAfterUnpledge == ~(relU # {} /\ fin # NoTid)
================================================================================
