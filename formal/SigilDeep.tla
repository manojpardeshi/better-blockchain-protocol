------------------------------- MODULE SigilDeep -------------------------------
(* Deep-confirmation soundness (SPEC Section 9).                            *)
(*                                                                         *)
(* Seals stay valid after their charter retires, so retired keys colluding  *)
(* with an owner can forge a valid-looking seal for a sigil really consumed  *)
(* elsewhere.  A deep-confirming holder ignores old seals and instead asks   *)
(* the CURRENT charter's members for STATUS, requiring at least f+1 of them  *)
(* to report the sigil bound to the claimed (gen, tid).                     *)
(*                                                                         *)
(* Premise (SPEC Section 9, and what rotation must preserve): honest current  *)
(* members hold the ONE true binding (gen = G, tid = TrueTid).  At most f    *)
(* current members are faulty and report anything.  TLC checks that no       *)
(* claim for a different tid is ever deep-confirmed, and that the true       *)
(* binding always can be -- and that the threshold f+1 is load-bearing       *)
(* (Threshold = f lets f faulty members forge).                             *)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Honest, Faulty,     \* current charter members
    Gens, Tids,
    TrueGen, TrueTid,   \* the real binding honest members report
    Threshold           \* confirmations required (f+1 is correct)

Members == Honest \cup Faulty
N == Cardinality(Members)
F == (N - 1) \div 3

ASSUME Honest \cap Faulty = {}
ASSUME Cardinality(Faulty) <= F
ASSUME TrueGen \in Gens /\ TrueTid \in Tids
ASSUME Threshold \in Nat

VARIABLE report   \* report[m] = <<gen, tid>> each current member m answers to STATUS

TypeOK == report \in [Members -> Gens \X Tids]

\* Honest members report the true binding; faulty members report anything.
Init == report \in { r \in [Members -> Gens \X Tids] :
                        \A m \in Honest : r[m] = <<TrueGen, TrueTid>> }
\* Faulty members may change their story at any time.
Next == \E m \in Faulty, g \in Gens, t \in Tids :
            /\ report' = [report EXCEPT ![m] = <<g, t>>]
Spec == Init /\ [][Next]_report

Confirmers(g, t) == { m \in Members : report[m] = <<g, t>> }
DeepConfirmed(g, t) == Cardinality(Confirmers(g, t)) >= Threshold

\* Soundness: only the true binding is ever deep-confirmed.
DeepSound == \A g \in Gens, t \in Tids : DeepConfirmed(g, t) => (g = TrueGen /\ t = TrueTid)

\* Non-vacuity: the true binding is always deep-confirmable (honest majority).
TrueConfirmable == DeepConfirmed(TrueGen, TrueTid)
================================================================================
