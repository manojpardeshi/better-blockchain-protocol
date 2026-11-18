"""Graceful shutdown with HTTP handlers waiting for the witness lock."""

import threading
import unittest
import urllib.error
import urllib.request

from sigil import Network
from sigil.server import StandbyServer, WitnessServer


class ServerShutdownTests(unittest.TestCase):
    def test_queued_handlers_are_rejected_after_stop(self):
        sim = Network()
        cid = sim.create_constellation("shutdown", successor={"n": 1, "dead_man": 60})
        for server_type, witness in ((WitnessServer, sim.all_witnesses(cid)[0]),
                                     (StandbyServer, sim.committee(cid)[0])):
            with self.subTest(server=server_type.__name__):
                self.assert_queued_handlers_rejected(server_type, witness)

    def assert_queued_handlers_rejected(self, server_type, witness):
        original_status = witness.status
        active = threading.Event()
        release = threading.Event()
        calls = []

        def blocked_status(sigil):
            calls.append(sigil)
            active.set()
            if not release.wait(10):
                raise TimeoutError("test did not release the active handler")
            return original_status(sigil)

        witness.status = blocked_status
        server = server_type(witness).start()
        self.addCleanup(server.stop)
        self.addCleanup(release.set)

        entered = 0
        entered_lock = threading.Lock()
        all_queued = threading.Event()
        dispatch = server.dispatch

        def counted_dispatch(method, body):
            nonlocal entered
            with entered_lock:
                entered += 1
                if entered == 10:
                    all_queued.set()
            return dispatch(method, body)

        server.dispatch = counted_dispatch
        results = []

        def client():
            request = urllib.request.Request(
                server.url + "/v0/status", data=b'{"sigil":"' + b"ab" * 32 + b'"}',
                headers={"Content-Type": "application/json"})
            try:
                with urllib.request.urlopen(request, timeout=10) as response:
                    results.append(response.status)
            except urllib.error.HTTPError as error:
                with error:
                    results.append(error.code)

        threads = [threading.Thread(target=client, daemon=True) for _ in range(10)]
        threads[0].start()
        self.assertTrue(active.wait(10), "first handler did not enter the witness")
        for thread in threads[1:]:
            thread.start()
        self.assertTrue(all_queued.wait(10), "handlers did not queue behind the witness lock")

        server.stop()  # SIGTERM closes admission while the first call is still active.
        release.set()
        for thread in threads:
            thread.join(10)
            self.assertFalse(thread.is_alive(), "handler did not finish after shutdown")
        self.assertEqual(sorted(results), [200] + [403] * 9)
        self.assertEqual(len(calls), 1, "a queued handler reached the witness after shutdown")


if __name__ == "__main__":
    unittest.main()
