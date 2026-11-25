"""Read-only operator preflight checks against real local witness endpoints."""

import copy
from datetime import datetime
import hashlib
import io
import json
import signal
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest.mock import patch

from sigil.charter import (Registry, charter_body, charter_hash, checkpoint_hash,
                           constellation_id, sign_charter, successor_clause)
from sigil.crypto import KeyPair
from sigil.witnessd import load_registry
from testnet.launcher import Testnet
from testnet.preflight import check, main


class TestnetPreflightArgumentTests(unittest.TestCase):
    def test_timeout_must_be_finite(self):
        for value in ("nan", "inf", "-inf", "1e309", "0", "-1"):
            with self.subTest(value=value), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as raised:
                    main(["--registry", "unused.json", "--directory", "unused.json",
                          "--timeout", value])
                self.assertEqual(raised.exception.code, 2)


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

    def test_down_witness_is_reported_and_recovery_passes(self):
        victim = 1
        url = self.tn.url(victim)
        self.tn.kill(victim, signal.SIGKILL)
        try:
            errors = check(self.directory, self.registry, allow_http=True, timeout=1)
            self.assertTrue(any(url in error and "unreachable or malformed reply" in error
                                for error in errors), errors)
            self.assertTrue(any("endpoint keys do not match current charter" in error
                                for error in errors), errors)
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(main(["--registry", self.tn.path("registry.json"),
                                       "--directory", self.tn.path("directory.json"),
                                       "--allow-http", "--timeout", "1"]), 1)
            self.assertIn(url, output.getvalue())
        finally:
            self.tn.start(victim)
            self.tn.wait_ready(victim)
        self.assertEqual(check(self.directory, self.registry, allow_http=True), [])

    def test_json_report_records_live_success_and_input_hashes(self):
        report_path = self.tn.path("preflight-success.json")
        self.assertEqual(main(["--registry", self.tn.path("registry.json"),
                               "--directory", self.tn.path("directory.json"),
                               "--allow-http", "--report-json", report_path]), 0)
        with open(report_path) as stream:
            report = json.load(stream)
        self.assertEqual(report["schema_version"], 1)
        self.assertTrue(report["success"])
        self.assertEqual(report["errors"], [])
        self.assertIsNotNone(datetime.fromisoformat(report["checked_at_utc"].replace("Z", "+00:00")).tzinfo)
        for name in ("registry", "directory"):
            with open(self.tn.path(f"{name}.json"), "rb") as stream:
                expected_hash = hashlib.sha256(stream.read()).hexdigest()
            self.assertEqual(report[f"{name}_sha256"], expected_hash)

    def test_json_report_redacts_live_outage(self):
        report_path = self.tn.path("preflight-outage.json")
        self.tn.kill(0)
        try:
            self.assertEqual(main(["--registry", self.tn.path("registry.json"),
                                   "--directory", self.tn.path("directory.json"),
                                   "--allow-http", "--timeout", "0.5",
                                   "--report-json", report_path]), 1)
            with open(report_path) as stream:
                contents = stream.read()
            report = json.loads(contents)
            self.assertFalse(report["success"])
            self.assertIn("endpoint_unreachable_or_malformed", report["errors"])
            for url in self.directory["constellations"][self.cid]:
                self.assertNotIn(url, contents)
            for key in self.registry.latest(self.cid)["witnesses"]:
                self.assertNotIn(key, contents)
        finally:
            self.tn.start(0)
            self.tn.wait_ready(0)

    def test_json_report_records_malformed_registry(self):
        registry_path = self.tn.path("invalid-registry.json")
        report_path = self.tn.path("preflight-invalid.json")
        with open(registry_path, "wb") as stream:
            stream.write(b"{invalid")
        self.assertEqual(main(["--registry", registry_path,
                               "--directory", self.tn.path("directory.json"),
                               "--report-json", report_path]), 1)
        with open(report_path) as stream:
            report = json.load(stream)
        self.assertFalse(report["success"])
        self.assertEqual(report["errors"], ["invalid_input"])
        self.assertEqual(report["registry_sha256"], hashlib.sha256(b"{invalid").hexdigest())
        self.assertIsNotNone(report["directory_sha256"])

    def test_json_report_cannot_overwrite_an_input(self):
        registry_path = self.tn.path("registry.json")
        with open(registry_path, "rb") as stream:
            original = stream.read()
        with self.assertRaises(SystemExit) as raised:
            main(["--registry", registry_path, "--directory", self.tn.path("directory.json"),
                  "--report-json", registry_path])
        self.assertEqual(raised.exception.code, 2)
        with open(registry_path, "rb") as stream:
            self.assertEqual(stream.read(), original)

    def test_json_report_marks_unreadable_input_hash_null(self):
        report_path = self.tn.path("preflight-missing.json")
        self.assertEqual(main(["--registry", self.tn.path("missing-registry.json"),
                               "--directory", self.tn.path("directory.json"),
                               "--report-json", report_path]), 1)
        with open(report_path) as stream:
            report = json.load(stream)
        self.assertEqual(report["errors"], ["invalid_input"])
        self.assertIsNone(report["registry_sha256"])
        self.assertIsNotNone(report["directory_sha256"])

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

    def test_checkpointed_charter_requires_checkpoint_feature(self):
        key = KeyPair.generate()
        standby = KeyPair.generate()
        genesis = charter_body("checkpointed", 0, [key.pk], None)
        cid = constellation_id(genesis)
        current = charter_body("checkpointed", 1, [key.pk], charter_hash(genesis),
                               successor_clause([standby.pk], 60),
                               checkpoint=checkpoint_hash([["a" * 64, 0, "b" * 64]]))
        chain = [{"body": genesis, "sigs": {}},
                 {"body": current, "sigs": {key.pk: sign_charter(key, current)}}]
        registry = Registry()
        registry.add_chain(cid, chain)
        directory = {"constellations": {cid: ["https://witness.example"]},
                     "committees": {cid: ["https://standby.example"]}}

        class Fake:
            def __init__(self, url, timeout):
                self.role = "standby" if "standby" in url else "witness"
                self.pk = standby.pk if self.role == "standby" else key.pk
                self.features = Fake.first_features[self.role]

            def _info(self):
                return {"pk": self.pk, "constellation": cid, "version": 1,
                        "role": self.role, "frozen": False, "features": Fake.second_features[self.role]}

            def chain(self, asked):
                return chain

        with patch("testnet.preflight.RemoteWitness", Fake), patch("testnet.preflight.RemoteStandby", Fake):
            # The first INFO is cached by the client constructor; a later INFO
            # must not hide an old daemon's lack of checkpoint support.
            Fake.first_features = {"witness": [], "standby": ["checkpoint"]}
            Fake.second_features = {"witness": ["checkpoint"], "standby": ["checkpoint"]}
            errors = check(directory, registry)
            self.assertTrue(any("witness" in error and "checkpoint" in error for error in errors), errors)
            Fake.first_features = {"witness": ["checkpoint"], "standby": ["checkpoint"]}
            Fake.second_features = {"witness": ["checkpoint"], "standby": []}
            errors = check(directory, registry)
            self.assertTrue(any("standby" in error and "checkpoint" in error for error in errors), errors)
            Fake.second_features["standby"] = ["checkpoint"]
            self.assertEqual(check(directory, registry), [])


if __name__ == "__main__":
    unittest.main()
