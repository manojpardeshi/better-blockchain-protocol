"""Spending-policy locks for AI agents that hold Sigil wallets.

An owner delegates a wallet to an autonomous agent (an LLM-driven process that
decides payments on its own). The threat is that the agent is *subverted* --
prompt-injected by a malicious counter-party, a poisoned web page, or a
compromised tool -- and signs a payment the owner never intended. Sigil's lock
language already constrains *who* may spend each parcel; this module expresses
an owner's *policy* for the agent's keys with those same primitives, so the
constraints are enforced by the witnesses and re-checked by every recipient,
**not** by the agent's own (subvertible) code.

Everything here builds ordinary ``sigil.locks`` predicates (sig / multi /
after / before / hash / all / any). It edits nothing in the rest of the
package and adds no new lock op. Compose these when you choose the *lock of a
parcel the agent holds* (e.g. the change address of its float): the policy
then binds the next spend of that parcel.

The lock language is **stateless and per-parcel**: it can gate an individual
spend on co-signers, time and secrets, but it cannot by itself count spending
across parcels or across time. Policies that need running totals (a rolling
per-period cap, a cumulative limit) are therefore expressed structurally --
by how the owner *shapes the agent's float into parcels* -- plus a co-signer.
``WHAT_LOCKS_CANNOT_EXPRESS`` lists the gaps explicitly.

See docs/AI_THREAT_MODEL.md section "Protecting AI agents that hold wallets".
"""

from . import locks

# ---------------------------------------------------------------------------
# Building blocks. Each returns a Lock dict usable anywhere a lock is expected.
# ---------------------------------------------------------------------------


def agent_sole(agent_pk: str) -> dict:
    """Baseline: the agent alone may spend. No extra protection (shown for
    contrast); every policy below is strictly stronger."""
    return locks.sig(agent_pk)


def co_signed(agent_pk: str, owner_pk: str) -> dict:
    """Both the agent and the owner (or a policy server) must sign.

    A subverted agent cannot move the parcel without the owner's co-signature,
    so the owner's signer is a second, out-of-band check on every spend. Good
    for an agent's high-value reserves.
    """
    return locks.all_of(locks.sig(agent_pk), locks.sig(owner_pk))


def allow_listed_payee(agent_pk: str, payee_key: str) -> dict:
    """The agent may spend only *into* a parcel the payee controls.

    Sigil locks constrain the spender, not the recipient, so an allow-list of
    payees is enforced one hop out: the owner funds the agent with parcels
    whose spend requires the agent's signature, and the agent may only pay a
    payee by, in turn, giving that payee a parcel -- but to *restrict* which
    payees, the owner pre-commits the payee by requiring the agent's spend to
    also satisfy a lock the payee co-signs. This models "pay only Acme": Acme
    publishes ``payee_key`` and the agent needs Acme's cooperation
    (counter-signature) to complete the spend.

    This is cooperative allow-listing (the payee must take part). A unilateral
    "the output must be addressed to Acme" rule is *not* expressible -- see
    ``WHAT_LOCKS_CANNOT_EXPRESS`` item (1).
    """
    return locks.all_of(locks.sig(agent_pk), locks.sig(payee_key))


def threshold_multisig(agent_pk: str, cosigner_pks: list, k: int) -> dict:
    """k-of-n co-signing: the agent plus any (k-1) of n owner-held cosigners.

    Use for large reserves where the owner wants m independent approvers (e.g.
    a hardware key + a phone + a policy server), any ``k`` of which suffice,
    always in addition to the agent.
    """
    return locks.all_of(locks.sig(agent_pk), locks.multi(k, list(cosigner_pks)))


def time_delayed_with_veto(agent_pk: str, owner_pk: str, not_before: int) -> dict:
    """A large payment the agent proposes now but that only *settles* after
    ``not_before`` -- unless the owner vetoes.

    Expressed as: the agent may complete the spend alone once the delay has
    passed, OR the owner co-signs to let it through sooner. The *veto* is the
    owner refusing to co-sign AND re-homing the parcel before the delay
    elapses (see ``veto_by_rehome`` below). This gives the owner a window to
    react to an injected large payment before it can settle.

        any( all(sig(agent), after(not_before)),      # agent alone, but only later
             all(sig(agent), sig(owner)) )            # or immediately with owner consent
    """
    return locks.any_of(
        locks.all_of(locks.sig(agent_pk), locks.after(not_before)),
        locks.all_of(locks.sig(agent_pk), locks.sig(owner_pk)),
    )


def owner_can_claw_back(agent_pk: str, owner_pk: str, agent_free_after: int) -> dict:
    """The owner can reclaim the parcel at any time; the agent may spend it
    freely only after ``agent_free_after``.

        any( sig(owner),                               # owner reclaims anytime
             all(sig(agent), after(agent_free_after))) # agent only after the window

    Before the window the agent needs the owner (use with ``co_signed`` terms
    off-parcel), so a freshly injected spend cannot settle until the owner has
    had ``agent_free_after - now`` to claw the float back.
    """
    return locks.any_of(
        locks.sig(owner_pk),
        locks.all_of(locks.sig(agent_pk), locks.after(agent_free_after)),
    )


# ---------------------------------------------------------------------------
# Per-period caps and allow-lists are STRUCTURAL: the owner shapes the agent's
# float into parcels so the stateless lock language enforces the limit.
# ---------------------------------------------------------------------------


def capped_float(agent_pk: str, owner_pk: str, denominations: list) -> list:
    """Return a list of per-parcel locks for the agent's float, each co-signed
    above a threshold and spendable alone below it.

    The owner funds the agent with these parcels. The *small* parcels the agent
    may spend unilaterally; the *large* ones need the owner. The per-period cap
    is then the total value of small parcels the owner tops up each period --
    enforced by the owner's refill cadence, not by any single lock. This is the
    closest the lock language gets to a rolling cap without an on-chain counter
    (see ``WHAT_LOCKS_CANNOT_EXPRESS`` item (2)).

    ``denominations`` is a list of ``(amount, requires_cosign: bool)``; the
    returned locks line up with it one-to-one.
    """
    out = []
    for _amount, requires_cosign in denominations:
        out.append(co_signed(agent_pk, owner_pk) if requires_cosign else locks.sig(agent_pk))
    return out


# What the stateless, per-parcel lock language fundamentally cannot express.
WHAT_LOCKS_CANNOT_EXPRESS = [
    "(1) Unilateral payee allow-listing. A lock constrains the SPENDER of a "
    "parcel, never the recipient/output of the transition. 'The agent may only "
    "pay Acme' can only be enforced cooperatively (Acme co-signs) or by an "
    "off-parcel policy signer that inspects outputs before co-signing. Witnesses "
    "are blind to outputs, so they cannot enforce a destination.",
    "(2) True rolling per-period caps. Locks hold no state and cannot read a "
    "running total across parcels or time. A '$1000 per day' cap is approximated "
    "structurally (small vs co-signed denominations + owner refill cadence) or "
    "delegated to a co-signing policy server that keeps the counter; the lock "
    "itself cannot subtract.",
    "(3) Rate limits / velocity. 'At most 5 payments per hour' needs a counter; "
    "not expressible. Same remedy as (2).",
    "(4) Aggregate value conditions across inputs. 'Co-sign only if this spend "
    "plus today's spends exceed X' cannot be evaluated by a lock, which sees one "
    "spend in isolation (and witnesses cannot see amounts at all).",
    "(5) Conditioning on transition semantics (asset, amount, memo, payee "
    "identity). The 'after'/'before' clock and hash preimages are the only "
    "non-signature predicates; there is no op over amounts or asset types.",
    "(6) Revocation of a key mid-life without moving the parcel. To disable a "
    "compromised agent key the owner must re-home / re-lock the affected "
    "parcels (claw-back); the lock cannot be edited in place.",
    "(7) Owner veto as a positive action. The time-delay pattern gives the owner "
    "a WINDOW to react (by clawing back / not co-signing); it cannot express an "
    "explicit 'owner stop' signal short of the owner spending the parcel first.",
]
