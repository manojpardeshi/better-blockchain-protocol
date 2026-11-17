"""The chaos observer must distinguish a released pledge from a later same-tid pledge."""

import unittest
from collections import Counter
from types import SimpleNamespace
from unittest.mock import patch

from sigil import model
from sigil.charter import Registry
from tests.integration.chaos.invariants import Observer, ReleasedPledge, check
from tests.integration.chaos.run import ChaosRun


class PledgeEpochChecks(unittest.TestCase):
    def setUp(self):
        self.obs = Observer()
        self.vote = {"constellation": "home", "version": 1, "witness": "honest",
                     "sigil": "coin", "gen": 0, "tid": "payment", "time": 100,
                     "sig": "verified-in-this-unit-test"}

    def check_s6(self, released):
        uncertain = []
        violations = check(self.obs, Registry(), honest={"honest"}, clocked={"honest"},
                           released=released, final_status={}, uncertain=uncertain)
        return violations, uncertain

    def add_vote(self, time=100):
        with patch("tests.integration.chaos.invariants.verify_vote", return_value=True):
            self.obs.add_vote({**self.vote, "time": time})

    def release(self, order, reauthorised=None, start_clock=100, end_clock=100,
                reauthorise_clock=None):
        return [ReleasedPledge("coin", 0, "payment", 1, order, order + 1,
                               start_clock, end_clock, 3, reauthorised, reauthorise_clock)]

    def test_vote_observed_before_release_is_not_post_release(self):
        self.add_vote()
        release = self.obs.mark()
        violations, uncertain = self.check_s6(self.release(release, start_clock=110, end_clock=110))
        self.assertNotIn("S6-vote-after-pledge-release", {v["kind"] for v in violations})
        self.assertIn("S6-release-despite-prior-vote", {v["kind"] for v in violations})
        self.assertEqual(uncertain, [])

    def test_vote_during_unpledged_interval_is_reported(self):
        release = self.obs.mark()
        self.add_vote(time=110)
        reauthorised = self.obs.mark()
        violations, _ = self.check_s6(self.release(release, reauthorised,
                                                    reauthorise_clock=120))
        self.assertIn("S6-vote-after-pledge-release", {v["kind"] for v in violations})

    def test_later_same_tid_authorisation_permits_later_vote(self):
        release = self.obs.mark()
        reauthorised = self.obs.mark()
        self.add_vote(time=120)
        self.assertEqual(self.check_s6(self.release(release, reauthorised,
                                                    reauthorise_clock=110)), ([], []))

    def test_late_observation_of_old_vote_is_not_post_release(self):
        release = self.obs.mark()
        self.add_vote(time=90)
        violations, uncertain = self.check_s6(self.release(release, start_clock=110, end_clock=110))
        self.assertEqual(violations, [])
        self.assertEqual([x["kind"] for x in uncertain], ["S6-prior-vote-observed-outside-sweep"])

    def test_late_observation_of_gap_vote_still_reports(self):
        release = self.obs.mark()
        reauthorised = self.obs.mark()
        self.add_vote(time=110)
        violations, _ = self.check_s6(self.release(release, reauthorised,
                                                    reauthorise_clock=120))
        self.assertIn("S6-vote-after-pledge-release", {v["kind"] for v in violations})

    def test_ambiguous_delayed_vote_is_diagnostic_not_post_release(self):
        release = self.obs.mark()
        self.add_vote(time=102)  # can have been signed before a release at clock 102
        violations, uncertain = self.check_s6(self.release(release, start_clock=100, end_clock=102))
        self.assertEqual(violations, [])
        self.assertEqual([x["kind"] for x in uncertain], ["S6-vote-order-uncertain"])

    def test_reauthorised_binding_is_not_called_resurrection(self):
        run = object.__new__(ChaosRun)
        run.released = self.release(1, reauthorised=2, reauthorise_clock=110)
        witness = SimpleNamespace(status=lambda _sigil: {"tid": "payment"})
        wallet = SimpleNamespace(holdings={"coin": {"sigil": "coin", "gen": 0,
                                                     "parcel": {"home": "home"}}},
                                 pledged={"coin": (0, "payment", 200)},
                                 network=SimpleNamespace(all_witnesses=lambda _home: [witness]))
        self.assertEqual(run._resurrected(wallet), [])
        run.released = self.release(1)
        wallet.pledged.clear()
        self.assertEqual(run._resurrected(wallet), ["coin"])

    def test_wallet_release_then_same_tid_authorise_closes_episode(self):
        run = object.__new__(ChaosRun)
        run.cfg = SimpleNamespace(client_timeout=0.01, pledge_ttl=4,
                                  max_skew=3, deep_threshold=200)
        run.directory = {}
        run.committees = {}
        run.wallet_locks = {}
        run.released = []
        run.obs = Observer()
        run.faults = Counter()

        def release_pledge(wallet, sigil):
            return wallet.pledged.pop(sigil, None) is not None

        with patch("tests.integration.chaos.run.Wallet.unpledge_if_unbound", release_pledge):
            wallet = run._wallet("alice", "home")
        addr = wallet.address()
        parcel = model.parcel("home", "asset", 1, addr["lock"], addr["salt"])
        sigil = model.sigil_of(parcel)
        ref = model.ref("source", 0)
        wallet.holdings[model.parcel_id(ref)] = {
            "ref": ref, "parcel": parcel, "sigil": sigil, "gen": 0}
        body = model.body([ref], [])
        header = model.header([[sigil, 0]], body)
        tid = model.transition_id(header)

        wallet.authorise(header, body)
        self.assertTrue(wallet.unpledge_if_unbound(sigil))
        self.assertEqual(len(run.released), 1)
        episode = run.released[0]
        self.assertIsNone(episode.reauthorised_order)
        wallet.authorise(header, body)
        self.assertEqual(wallet.pledged[sigil][:2], (0, tid))
        self.assertIsNotNone(episode.reauthorised_order)
        self.assertIsNotNone(episode.reauthorised_clock)
        self.assertGreater(episode.reauthorised_order, episode.released_order)


if __name__ == "__main__":
    unittest.main()
