"""Read-only operator preflight checks against real local witness endpoints."""

import copy
import json
import signal
import tempfile
import unittest
from unittest.mock import patch

from sigil.charter import Registry, charter_body, constellation_id, successor_clause
from sigil.witnessd import load_registry
from testnet.launcher import Testnet
from testnet.preflight import check, main


class TestnetPreflightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="sigil-preflight-")
        cls.tn = Testnet(cls.tmp.name)
        cls.tn.create(constellations=1, witnesses=2)
        cls.tn.start_all()
        cls.registry = load_registry(cls.tn.path("registry.json"))
        with open(cls.tn.path("directory.json")) as stream:
            cls.directory = json.load(stream)
        cls.cid = next(iter(cls.directory["constellations"]))

    @classmethod
    def tearDownClass(cls):
        cls.tn.stop_all(signal.SIGKILL)
        cls.tmp.cleanup()

    def test_live_endpoints_match_registry(self):
        self.assertEqual(check(self.directory, self.registry, allow_http=True), [])
        self.assertEqual(main(["--registry", self.tn.path("registry.json"),
                               "--directory", self.tn.path("directory.json"), "--allow-http"]), 0)

    def test_requires_explicit_http_flag(self):
        errors = check(self.directory, self.registry)
        self.assertTrue(any("must use HTTPS" in error for error in errors), errors)

    def test_reused_url_does_not_count_as_second_member(self):
        directory = copy.deepcopy(self.directory)
        urls = directory["constellations"][self.cid]
        urls[1] = urls[0]
        errors = check(directory, self.registry, allow_http=True)
        self.assertTrue(any("URL reused" in error for error in errors), errors)
        self.assertTrue(any("endpoint keys do not match" in error for error in errors), errors)

    def test_rejects_stale_or_spoofed_endpoint(self):
        class Fake:
            pk = "wrong-key"

            def __init__(self, url, timeout):
                pass

            def _info(self):
                return {"pk": self.pk, "constellation": "wrong-cid", "version": 9, "frozen": True}

            def chain(self, cid):
                return []

        with patch("testnet.preflight.RemoteWitness", Fake):
            errors = check(self.directory, self.registry, allow_http=True)
        self.assertTrue(any("constellation/version" in error for error in errors), errors)
        self.assertTrue(any("public key is not" in error for error in errors), errors)
        self.assertTrue(any("served charter chain differs" in error for error in errors), errors)
        self.assertTrue(any("frozen or fenced" in error for error in errors), errors)

    def test_rejects_missing_committee_and_bad_url(self):
        directory = copy.deepcopy(self.directory)
        directory["constellations"][self.cid][0] = "https://user@node.example/v0/info"
        directory["committees"] = {"unknown": ["https://node.example"]}
        errors = check(directory, self.registry, allow_http=True)
        self.assertTrue(any("credentials, path" in error for error in errors), errors)
        self.assertTrue(any("committee has no constellation" in error for error in errors), errors)

    def test_committee_membership_and_role(self):
        body = charter_body("operator", 0, ["w1", "w2"], None,
                            successor_clause(["s1", "s2"], 60))
        cid = constellation_id(body)
        chain = [{"body": body, "sigs": {}}]
        registry = Registry()
        registry.add_chain(cid, chain)
        directory = {"constellations": {cid: ["https://w1.example", "https://w2.example"]},
                     "committees": {cid: ["https://s1.example", "https://s2.example"]}}

        class Fake:
            def __init__(self, url, timeout):
                self.pk = url.split("//")[1].split(".")[0]
                self.role = "standby" if self.pk.startswith("s") else "witness"

            def _info(self):
                return {"pk": self.pk, "role": self.role, "constellation": cid,
                        "version": 0, "frozen": False}

            def chain(self, asked):
                return chain

        with patch("testnet.preflight.RemoteWitness", Fake), patch("testnet.preflight.RemoteStandby", Fake):
            self.assertEqual(check(directory, registry), [])
            del directory["committees"]
            errors = check(directory, registry)
            self.assertTrue(any("expected 2 URLs, got 0" in error for error in errors), errors)
            directory["committees"] = {cid: ["https://w3.example", "https://w4.example"]}
            errors = check(directory, registry)
            self.assertTrue(any("wrong daemon role" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
