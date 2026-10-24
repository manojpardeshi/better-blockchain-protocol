------------------------------- MODULE SigilExpiry -------------------------------
(* Owner-signed spend expiry (SPEC Section 5.1) and the wallet rule that     *)
(* relies on it (sigil/wallet.py Wallet.unpledge_if_unbound).               *)
(*                                                                         *)
(* An unlock carries an integer ``expires``.  An honest witness refuses to  *)
(* NEWLY bind once its own clock is past ``expires`` (witness.py:           *)
(* ``int(self.clock()) > auth["unlock"]["expires"]``).  The wallet drops a  *)
(* failed pledge -- and so may sign a different transition for the same     *)
(* (sigil, gen) -- only when its own clock is past ``expires + max_skew``   *)
(* and every member of the home reported no binding or vote for the tid.   *)
(*                                                                         *)
(* CLAIM (checked):  once the wallet has dropped the pledge, no honest      *)
(* witness ever binds the sigil to that tid, so the tid can never be sealed *)
(* -- PROVIDED max_skew is at least the largest amount a witness's clock can *)
(* lag the wallet's.  Clocks drift: every clock (witnesses' and the         *)
(* wallet's) stays within SKEW of real time ``now`` and never runs          *)
(* backwards.  The owner's signed request can be delivered to any honest    *)
(* witness at ANY later time (network delay), and Byzantine witnesses vote  *)
(* and report whatever they like.                                           *)
(*                                                                         *)
(* Mutations (each must be caught by TLC):                                 *)
(*   IgnoreExpiry      honest witnesses bind regardless of expiry;          *)
(*   MAXSKEW < 2*SKEW  the wallet's margin is smaller than the real         *)
(*                     wallet-to-witness skew (MC_expiry_skew_mutant.cfg).  *)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Honest, Byz,        \* witnesses of the sigil's home
    Quorum,             \* q = n - f
    EXPIRES,            \* the owner-signed expiry
    SKEW,               \* every clock stays within SKEW of real time
    MAXSKEW,            \* the wallet's margin (Wallet.max_skew)
    MAXTIME,            \* bound on real time, for TLC
    IgnoreExpiry        \* MUTATION: honest witnesses ignore the expiry guard

ASSUME Honest \cap Byz = {}
ASSUME Quorum \in Nat /\ Cardinality(Byz) < Quorum
ASSUME {EXPIRES, SKEW, MAXSKEW, MAXTIME} \subseteq Nat

Witnesses == Honest \cup Byz
Times     == 0..(MAXTIME + SKEW)

VARIABLES
    now,        \* real time
    clock,      \* clock[w]: honest witness w's clock
    wclock,     \* the wallet's clock
    voted,      \* witnesses holding a vote for the target tid t
    voteClock,  \* voteClock[w]: w's clock when it (honest) voted t
    dropped     \* the wallet has dropped the pledge (unpledge_if_unbound returned True)

vars == <<now, clock, wclock, voted, voteClock, dropped>>

Within(c) == c + SKEW >= now /\ c <= now + SKEW     \* |c - now| <= SKEW

HonestVoted == voted \cap Honest
SealedT     == Cardinality(voted) >= Quorum

TypeOK ==
    /\ now \in 0..MAXTIME
    /\ clock \in [Honest -> Times]
    /\ wclock \in Times
    /\ voted \subseteq Witnesses
    /\ voteClock \in [Honest -> Times]
    /\ dropped \in BOOLEAN

Init ==
    /\ now = 0
    /\ clock \in [Honest -> 0..SKEW]
    /\ wclock \in 0..SKEW
    /\ voted = {}
    /\ voteClock = [w \in Honest |-> 0]
    /\ dropped = FALSE

\* Real time advances only while no clock would fall more than SKEW behind.
Tick ==
    /\ now < MAXTIME
    /\ \A w \in Honest : clock[w] + SKEW >= now + 1
    /\ wclock + SKEW >= now + 1
    /\ now' = now + 1
    /\ UNCHANGED <<clock, wclock, voted, voteClock, dropped>>

\* A clock runs forward, never more than SKEW ahead of real time.
AdvanceClock(w) ==
    /\ clock[w] + 1 <= now + SKEW
    /\ clock' = [clock EXCEPT ![w] = @ + 1]
    /\ UNCHANGED <<now, wclock, voted, voteClock, dropped>>
AdvanceWallet ==
    /\ wclock + 1 <= now + SKEW
    /\ wclock' = wclock + 1
    /\ UNCHANGED <<now, clock, voted, voteClock, dropped>>

\* A (possibly long-delayed) copy of the owner's signed request reaches an
\* honest witness, which newly binds and votes t only if not yet expired.
HonestVote(w) ==
    /\ w \notin voted
    /\ IgnoreExpiry \/ clock[w] <= EXPIRES
    /\ voted' = voted \cup {w}
    /\ voteClock' = [voteClock EXCEPT ![w] = clock[w]]
    /\ UNCHANGED <<now, clock, wclock, dropped>>

ByzVote(b) ==
    /\ b \notin voted
    /\ voted' = voted \cup {b}
    /\ UNCHANGED <<now, clock, wclock, voteClock, dropped>>

\* Wallet.unpledge_if_unbound: past expires + max_skew on the WALLET's clock,
\* and every member answered with no binding/vote for t.  Honest members
\* answer truthfully; Byzantine ones may claim "unbound" even if they voted.
Drop ==
    /\ ~dropped
    /\ wclock > EXPIRES + MAXSKEW
    /\ HonestVoted = {}
    /\ dropped' = TRUE
    /\ UNCHANGED <<now, clock, wclock, voted, voteClock>>

Next ==
    \/ Tick \/ AdvanceWallet
    \/ \E w \in Honest : AdvanceClock(w) \/ HonestVote(w)
    \/ \E b \in Byz : ByzVote(b)
    \/ Drop

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Clock discipline holds by construction (sanity).
SkewOK == (\A w \in Honest : Within(clock[w])) /\ Within(wclock)

\* Mirror of the witness guard: an honest witness only ever voted t while its
\* clock was at or before the expiry.
NoBindAfterExpiry == \A w \in HonestVoted : voteClock[w] <= EXPIRES

\* The wallet claim: after the pledge is dropped, no honest witness ever binds
\* t, hence t is never sealed (Byzantine votes alone are below quorum).
WalletClaim == dropped => (HonestVoted = {} /\ ~SealedT)
================================================================================
