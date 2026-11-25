import unittest

from research.stamp_cost_probe import run, run_http


class StampCostProbeTests(unittest.TestCase):
    def test_phases_exercise_durable_stamp_paths(self):
        result = run(count=2, stamp_bits=1024)
        phases = result["phases"]
        self.assertEqual(phases["sale_sign"]["operations"], 4)
        self.assertEqual(phases["sale_sign"]["log_payload_bytes_delta"], 0)
        self.assertEqual(phases["spend_accepted"]["rows_delta_by_kind"]["stamp"], 2)
        self.assertEqual(phases["spend_accepted"]["rows_delta_by_kind"]["record"], 2)
        self.assertEqual(phases["spend_rejected_valid_stamp"]["rows_delta_by_kind"]["stamp"], 2)
        self.assertEqual(phases["spend_rejected_valid_stamp"]["rows_delta_by_kind"]["record"], 0)
        self.assertEqual(phases["spend_rejected_replay"]["rows_delta_by_kind"]["stamp"], 0)
        self.assertEqual(phases["spend_rejected_replay"]["log_payload_bytes_delta"], 0)
        for phase in phases.values():
            self.assertGreater(phase["wall_seconds"], 0)
            self.assertGreaterEqual(phase["cpu_seconds"], 0)
            self.assertGreaterEqual(phase["db_bytes_delta"], 0)

    def test_invalid_parameters(self):
        for count, bits in ((0, 1024), (-1, 1024), (1, 512)):
            with self.subTest(count=count, bits=bits), self.assertRaises(ValueError):
                run(count=count, stamp_bits=bits)
        for concurrency in (0, -1):
            with self.subTest(concurrency=concurrency), self.assertRaises(ValueError):
                run_http(count=1, stamp_bits=1024, concurrency=concurrency)

    def test_http_paths_and_concurrent_durable_outcomes(self):
        result = run_http(count=2, stamp_bits=1024, concurrency=2)
        self.assertEqual(result["transport"], "loopback_http")
        self.assertEqual(result["concurrency"], 2)
        self.assertEqual(result["outcomes"], {
            "sale_signed": 4, "spend_accepted": 2,
            "spend_rejected_valid_stamp": 2, "spend_rejected_replay": 2})
        phases = result["phases"]
        self.assertEqual(phases["sale_sign"]["operations"], 4)
        self.assertEqual(phases["spend_accepted"]["rows_delta_by_kind"]["record"], 2)
        self.assertEqual(phases["spend_accepted"]["rows_delta_by_kind"]["stamp"], 2)
        self.assertEqual(phases["spend_rejected_valid_stamp"]["rows_delta_by_kind"]["record"], 0)
        self.assertEqual(phases["spend_rejected_valid_stamp"]["rows_delta_by_kind"]["stamp"], 2)
        self.assertEqual(phases["spend_rejected_replay"]["rows_delta_by_kind"]["stamp"], 0)


if __name__ == "__main__":
    unittest.main()
