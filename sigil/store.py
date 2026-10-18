"""Durable witness state: an append-only log in SQLite.

A witness that forgets a vote after a crash could vote again for a
different transition at the same ``(sigil, gen)``, which is equivocation.
The store makes every state change durable before the witness answers.

The log is a single table of ``(seq, kind, key, value)`` rows that is only
ever appended to; the current state is the last value per ``(kind, key)``.
Kinds:

* ``pk``      -- the witness key this store belongs to (guards against mix-ups)
* ``member``  -- ``[cid, version]`` the witness has joined
* ``frozen``  -- ``true`` once the witness froze for rotation
* ``record``  -- key = sigil, value = the full ``Record`` as a dict
* ``stamp``   -- key = a redeemed stamp serial

Each ``append`` is one transaction committed in WAL mode with
``synchronous=FULL``, so once it returns the rows survive a crash or power
loss, and a batch is applied entirely or not at all. Compaction is left
out: logs only grow, which is fine for a prototype.
"""

import json
import sqlite3

from .encoding import canonical


class WitnessStore:
    def __init__(self, path: str):
        self.db = sqlite3.connect(path, isolation_level=None)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS log ("
            "seq INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT NOT NULL, key TEXT NOT NULL, value TEXT NOT NULL)"
        )

    def append(self, entries: list[tuple[str, str, object]]) -> None:
        """Durably append ``(kind, key, value)`` entries as one atomic batch."""
        rows = [(kind, key, canonical(value).decode()) for kind, key, value in entries]
        self.db.execute("BEGIN IMMEDIATE")
        try:
            self.db.executemany("INSERT INTO log (kind, key, value) VALUES (?, ?, ?)", rows)
        except BaseException:
            self.db.execute("ROLLBACK")
            raise
        self.db.execute("COMMIT")

    def load(self) -> dict:
        """Replay the log into ``{pk, member, frozen, records, stamps}``."""
        state = {"pk": None, "member": None, "frozen": False, "records": {}, "stamps": set()}
        for kind, key, value in self.db.execute("SELECT kind, key, value FROM log ORDER BY seq"):
            v = json.loads(value)
            if kind == "record":
                state["records"][key] = v
            elif kind == "stamp":
                state["stamps"].add(key)
            elif kind in ("pk", "member", "frozen"):
                state[kind] = v
        return state

    def close(self) -> None:
        self.db.close()
