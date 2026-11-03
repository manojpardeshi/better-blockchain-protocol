"""An automated red-team harness that plays an AI-scale adversary against the
Sigil reference implementation (docs/AI_THREAT_MODEL.md).

It is a *search-based* attacker: it drives the real ``sigil`` code through
randomised + lightly guided sequences of adversarial actions (Byzantine
witnesses up to and beyond ``f``, equivocating owners, malicious
counter-parties, forged/malformed messages, gossip withholding, clock skew,
crash/restart, rotation timing) and, after every step, checks the safety
invariants:

    S1  no sigil is consumed by two different *complete* transitions
    S2  no honest witness is convicted (no equivocation proof vs an honest key)
    S3  an honest wallet never signs two unlocks for one (sigil, gen)
    S4  value is conserved: an honest recipient never accepts more than was
        legitimately transferred to it
    S5  a parcel owned by an honest holder never moves without the owner's
        signature (no theft)

It also runs *resource-exhaustion* probes and reports amplification ratios.

Modules:
    model      -- witness-level schedule explorer (S1, S2)
    conserve   -- payment-level fuzzer over the real Wallet (S3, S4, S5)
    resources  -- CPU / memory / storage amplification probes
    runner     -- ``python -m tests.redteam.runner`` with env-var knobs
    test_redteam -- the unittest entry: fast default run, mutation checks,
                    and the two currently-failing findings (expectedFailure)

Everything here is read-only against the protocol: it only calls the public
reference API. It never weakens or edits ``sigil/``.
"""
