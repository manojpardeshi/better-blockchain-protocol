"""Failure paths for the reproducible benchmark runner."""

import os
import subprocess
import tempfile
import unittest
from unittest import mock

from bench import run_all


class BenchmarkRunnerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.output = os.path.join(self.tmp.name, "results.json")

    def test_preflight_rejects_unsupported_host(self):
        with mock.patch.object(run_all.sys, "platform", "darwin"):
            with self.assertRaisesRegex(RuntimeError, "requires Linux"):
                run_all.preflight(1, self.output)

    def test_preflight_rejects_invalid_repetitions_even_in_quick_mode(self):
        with self.assertRaisesRegex(ValueError, "--reps must be at least 1"):
            run_all.preflight(0, self.output)

    def test_preflight_rejects_missing_pinned_cpu(self):
        with (mock.patch.object(run_all.sys, "platform", "linux"),
              mock.patch("builtins.open", mock.mock_open(read_data="model name: test CPU\n")),
              mock.patch.object(run_all.shutil, "which", return_value="/usr/bin/taskset"),
              mock.patch.object(run_all.os, "sched_getaffinity", return_value={1, 2, 3, 4}, create=True)):
            with self.assertRaisesRegex(RuntimeError, "CPUs 0-3 must be available"):
                run_all.preflight(1, self.output)

    def test_preflight_rejects_missing_rust_executable(self):
        with (mock.patch.object(run_all.sys, "platform", "linux"),
              mock.patch("builtins.open", mock.mock_open(read_data="model name: test CPU\n")),
              mock.patch.object(run_all.shutil, "which", return_value="/usr/bin/taskset"),
              mock.patch.object(run_all.os, "sched_getaffinity", return_value={0, 1, 2, 3}, create=True),
              mock.patch.object(run_all.os.path, "isfile", return_value=False)):
            with self.assertRaisesRegex(RuntimeError, "Rust witness executable missing"):
                run_all.preflight(1, self.output)

    def test_preflight_rejects_unusable_taskset(self):
        failed = subprocess.CompletedProcess([], 1, "", "operation not permitted")
        with (mock.patch.object(run_all.sys, "platform", "linux"),
              mock.patch("builtins.open", mock.mock_open(read_data="model name: test CPU\n")),
              mock.patch.object(run_all.shutil, "which", return_value="/usr/bin/taskset"),
              mock.patch.object(run_all.os, "sched_getaffinity", return_value={0, 1, 2, 3}, create=True),
              mock.patch.object(run_all.os.path, "isfile", return_value=True),
              mock.patch.object(run_all.os, "access", return_value=True),
              mock.patch.object(run_all.subprocess, "run", return_value=failed)):
            with self.assertRaisesRegex(RuntimeError, "taskset cannot pin to CPUs 0: operation not permitted"):
                run_all.preflight(1, self.output)

    def test_preflight_rejects_unwritable_output_directory(self):
        succeeded = subprocess.CompletedProcess([], 0, "", "")
        with (mock.patch.object(run_all.sys, "platform", "linux"),
              mock.patch("builtins.open", mock.mock_open(read_data="model name: test CPU\n")),
              mock.patch.object(run_all.shutil, "which", return_value="/usr/bin/taskset"),
              mock.patch.object(run_all.os, "sched_getaffinity", return_value={0, 1, 2, 3}, create=True),
              mock.patch.object(run_all.os.path, "isfile", return_value=True),
              mock.patch.object(run_all.os, "access", return_value=True),
              mock.patch.object(run_all.subprocess, "run", return_value=succeeded),
              mock.patch.object(run_all.tempfile, "mkstemp", side_effect=PermissionError("read only"))):
            with self.assertRaisesRegex(RuntimeError, "cannot create a temporary file in output directory"):
                run_all.preflight(1, self.output)

    def test_atomic_write_preserves_old_result_on_serialization_failure(self):
        with open(self.output, "w") as f:
            f.write("old result")
        with self.assertRaises(TypeError):
            run_all.write_results(self.output, {"partial": object()})
        with open(self.output) as f:
            self.assertEqual(f.read(), "old result")
        self.assertEqual(os.listdir(self.tmp.name), ["results.json"])

    def test_atomic_write_preserves_old_result_on_interrupt(self):
        with open(self.output, "w") as f:
            f.write("old result")
        with mock.patch.object(run_all.json, "dump", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                run_all.write_results(self.output, {"complete": True})
        with open(self.output) as f:
            self.assertEqual(f.read(), "old result")
        self.assertEqual(os.listdir(self.tmp.name), ["results.json"])

    def test_atomic_write_replaces_complete_result(self):
        with open(self.output, "w") as f:
            f.write("old result")
        run_all.write_results(self.output, {"complete": True})
        with open(self.output) as f:
            self.assertEqual(f.read(), '{\n "complete": true\n}\n')
        self.assertEqual(os.listdir(self.tmp.name), ["results.json"])

    def test_measurement_failure_leaves_old_result(self):
        with open(self.output, "w") as f:
            f.write("old result")
        with (mock.patch.object(run_all, "preflight"),
              mock.patch.object(run_all, "machine", return_value={}),
              mock.patch.object(run_all, "rust", side_effect=RuntimeError("measurement failed")),
              mock.patch.object(run_all.sys, "argv", ["run_all.py", "--quick", "--out", self.output])):
            with self.assertRaisesRegex(RuntimeError, "measurement failed"):
                run_all.main()
        with open(self.output) as f:
            self.assertEqual(f.read(), "old result")

    def test_http_run_rejects_partial_success(self):
        result = {"bench": "http_spend", "n": 4, "ok": 3, "errors": 1, "votes_per_s": 100}
        with mock.patch.object(run_all, "sh", return_value=result):
            with self.assertRaisesRegex(RuntimeError, "incomplete HTTP benchmark: requested 4"):
                run_all.rust("http", "--url", "http://localhost:7000", "--n", "4")

    def test_http_run_rejects_missing_or_inconsistent_counts(self):
        for result in (
            {"bench": "http_spend", "n": 4, "ok": 4},
            {"bench": "http_spend", "n": 5, "ok": 4, "errors": 0},
            {"bench": "http_spend", "n": 4, "ok": True, "errors": 0},
        ):
            with self.subTest(result=result), mock.patch.object(run_all, "sh", return_value=result):
                with self.assertRaisesRegex(RuntimeError, "incomplete HTTP benchmark"):
                    run_all.rust("http", "--n", "4")

    def test_http_run_accepts_complete_measurement(self):
        result = {"bench": "http_spend", "n": 4, "ok": 4, "errors": 0, "votes_per_s": 100}
        with mock.patch.object(run_all, "sh", return_value=result):
            self.assertEqual(run_all.rust("http", "--n", "4"), result)


if __name__ == "__main__":
    unittest.main()
