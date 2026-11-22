"""Transactional SQLite persistence for the version 1 coordination state API.

This module authenticates no caller and controls no filesystem/tool access. Its
hashes detect inconsistent stored data; they are not signatures against a writer
who can replace the database and recompute every hash.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import sqlite3
from typing import Callable


SCHEMA_VERSION = 1
PROTOCOL_VERSION = "iut-agent-tree/2026-10-13-v1"
_CHAIN_ORIGIN = "0" * 64
_SCHEMA = {
    "store_metadata": """CREATE TABLE store_metadata (
        singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL,
        protocol_version TEXT NOT NULL
    )""",
    "state_snapshot": """CREATE TABLE state_snapshot (
        singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
        revision INTEGER NOT NULL CHECK (revision > 0),
        snapshot_json TEXT NOT NULL,
        snapshot_sha256 TEXT NOT NULL
    )""",
    "state_events": """CREATE TABLE state_events (
        revision INTEGER PRIMARY KEY CHECK (revision > 0),
        request_id TEXT NOT NULL UNIQUE,
        request_json TEXT NOT NULL,
        request_sha256 TEXT NOT NULL,
        event_json TEXT NOT NULL,
        snapshot_json TEXT NOT NULL,
        snapshot_sha256 TEXT NOT NULL,
        response_json TEXT NOT NULL,
        previous_event_sha256 TEXT NOT NULL,
        event_sha256 TEXT NOT NULL
    )""",
    "state_events_no_update": """CREATE TRIGGER state_events_no_update
        BEFORE UPDATE ON state_events BEGIN
        SELECT RAISE(ABORT, 'state events are append-only'); END""",
    "state_events_no_delete": """CREATE TRIGGER state_events_no_delete
        BEFORE DELETE ON state_events BEGIN
        SELECT RAISE(ABORT, 'state events are append-only'); END""",
}


class StoreError(Exception):
    """A safe, structured storage or semantic rejection."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


def _require_json(value: object) -> None:
    if value is None or type(value) in (str, bool, int):
        return
    if type(value) is float and math.isfinite(value):
        return
    if type(value) is list:
        for element in value:
            _require_json(element)
        return
    if type(value) is dict and all(type(key) is str for key in value):
        for element in value.values():
            _require_json(element)
        return
    raise ValueError("Only finite JSON values with string object keys are supported.")


def _canonical(value: object, code: str = "INVALID_REQUEST") -> str:
    try:
        _require_json(value)
        return json.dumps(value, sort_keys=True, separators=(",", ":"),
                          ensure_ascii=True, allow_nan=False)
    except (ValueError, TypeError, RecursionError) as error:
        raise StoreError(code, "The value is not valid finite JSON.") from error


def _digest(encoded: str) -> str:
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _object_from_storage(encoded: str) -> dict:
    try:
        decoded = json.loads(encoded)
    except (ValueError, TypeError, RecursionError) as error:
        raise StoreError("STORE_CORRUPT", "Stored JSON is invalid.") from error
    if type(decoded) is not dict or _canonical(decoded, "STORE_CORRUPT") != encoded:
        raise StoreError("STORE_CORRUPT", "Stored JSON is not a canonical object.")
    return decoded


def _validate_request(request: dict) -> str:
    if type(request) is not dict:
        raise StoreError("INVALID_REQUEST", "The request must be a JSON object.")
    request_id = request.get("request_id")
    expected_revision = request.get("expected_revision")
    if type(request_id) is not str or not request_id.strip():
        raise StoreError("INVALID_REQUEST", "request_id must be a nonempty string.")
    if type(expected_revision) is not int or expected_revision < 0:
        raise StoreError("INVALID_REQUEST", "expected_revision must be a nonnegative integer.")
    return _canonical(request)


def _check_snapshot_protocol(snapshot: dict) -> None:
    if "protocol_version" in snapshot and snapshot["protocol_version"] != PROTOCOL_VERSION:
        raise StoreError("PROTOCOL_MISMATCH", "The snapshot protocol version is unsupported.")


def _connect(db_path: str | Path, *, writable: bool, initialize: bool = False) -> sqlite3.Connection:
    path = Path(db_path).absolute()
    if not initialize and not path.is_file():
        raise StoreError("STORE_MISSING", "The state database does not exist.")
    mode = "rwc" if initialize else "rw" if writable else "ro"
    connection = sqlite3.connect(path.as_uri() + "?mode=" + mode,
                                 uri=True, timeout=30, isolation_level=None)
    connection.row_factory = sqlite3.Row
    try:
        if writable:
            connection.execute("PRAGMA synchronous = FULL")
    except sqlite3.Error:
        connection.close()
        raise
    return connection


def _translate_sqlite(error: sqlite3.Error) -> StoreError:
    code = getattr(error, "sqlite_errorcode", 0)
    base_code = code & 255 if type(code) is int else 0
    if base_code in (sqlite3.SQLITE_BUSY, sqlite3.SQLITE_LOCKED):
        return StoreError("STORE_BUSY", "The state database is busy; retry the request.")
    if base_code in (sqlite3.SQLITE_CANTOPEN, sqlite3.SQLITE_IOERR,
                     sqlite3.SQLITE_FULL, sqlite3.SQLITE_READONLY, sqlite3.SQLITE_PERM):
        return StoreError("STORE_IO", "The state database could not be accessed durably.")
    return StoreError("STORE_CORRUPT", "The state database is invalid or inconsistent.")


def _schema_entries(connection: sqlite3.Connection) -> dict:
    return {row["name"]: row for row in connection.execute(
        "SELECT name, type, sql FROM sqlite_master WHERE substr(name, 1, 7) != 'sqlite_'")}


def _validate_store(connection: sqlite3.Connection) -> tuple[int, dict, list[sqlite3.Row]]:
    entries = _schema_entries(connection)
    if set(entries) != set(_SCHEMA):
        raise StoreError("SCHEMA_MISMATCH", "The state database schema is unsupported.")
    for name, definition in _SCHEMA.items():
        expected_type = "trigger" if name.startswith("state_events_no_") else "table"
        actual_definition = entries[name]["sql"]
        if (entries[name]["type"] != expected_type or type(actual_definition) is not str
                or " ".join(actual_definition.split()) != " ".join(definition.split())):
            raise StoreError("SCHEMA_MISMATCH", "The state database schema has changed.")
    metadata = connection.execute("SELECT * FROM store_metadata").fetchall()
    if len(metadata) != 1 or metadata[0]["singleton"] != 1:
        raise StoreError("STORE_CORRUPT", "The state database metadata is missing or inconsistent.")
    if metadata[0]["schema_version"] != SCHEMA_VERSION:
        raise StoreError("SCHEMA_MISMATCH", "The state database schema version is unsupported.")
    if metadata[0]["protocol_version"] != PROTOCOL_VERSION:
        raise StoreError("PROTOCOL_MISMATCH", "The stored protocol version is unsupported.")
    snapshots = connection.execute("SELECT * FROM state_snapshot").fetchall()
    if len(snapshots) != 1 or snapshots[0]["singleton"] != 1:
        raise StoreError("STORE_CORRUPT", "The current state snapshot is missing or inconsistent.")
    current = snapshots[0]
    revision = current["revision"]
    if type(revision) is not int or revision < 1:
        raise StoreError("STORE_CORRUPT", "The stored revision is invalid.")
    snapshot = _object_from_storage(current["snapshot_json"])
    _check_snapshot_protocol(snapshot)
    if _digest(current["snapshot_json"]) != current["snapshot_sha256"]:
        raise StoreError("STORE_CORRUPT", "The current snapshot hash does not match.")
    events = connection.execute("SELECT * FROM state_events ORDER BY revision").fetchall()
    if len(events) != revision:
        raise StoreError("STORE_CORRUPT", "The event history does not match the current revision.")
    previous_hash = _CHAIN_ORIGIN
    for expected_revision, record in enumerate(events, start=1):
        if record["revision"] != expected_revision:
            raise StoreError("STORE_CORRUPT", "The event history contains a revision gap.")
        request = _object_from_storage(record["request_json"])
        if (type(request.get("request_id")) is not str or not request["request_id"].strip()
                or request["request_id"] != record["request_id"]
                or type(request.get("expected_revision")) is not int
                or request["expected_revision"] != expected_revision - 1
                or _digest(record["request_json"]) != record["request_sha256"]):
            raise StoreError("STORE_CORRUPT", "A stored request is inconsistent.")
        _object_from_storage(record["event_json"])
        event_snapshot = _object_from_storage(record["snapshot_json"])
        _check_snapshot_protocol(event_snapshot)
        response = _object_from_storage(record["response_json"])
        if (set(response) != {"ok", "revision", "result", "replayed"}
                or response["ok"] is not True or response["replayed"] is not False
                or type(response["revision"]) is not int
                or response["revision"] != expected_revision
                or type(response["result"]) is not dict):
            raise StoreError("STORE_CORRUPT", "A stored response is inconsistent.")
        if (_digest(record["snapshot_json"]) != record["snapshot_sha256"]
                or record["previous_event_sha256"] != previous_hash
                or _event_digest(dict(record)) != record["event_sha256"]):
            raise StoreError("STORE_CORRUPT", "An event hash does not match the stored history.")
        previous_hash = record["event_sha256"]
    latest = events[-1]
    if (latest["snapshot_json"] != current["snapshot_json"]
            or latest["snapshot_sha256"] != current["snapshot_sha256"]):
        raise StoreError("STORE_CORRUPT", "The latest event and current snapshot disagree.")
    return revision, snapshot, events


def _event_digest(record: dict) -> str:
    hashed_record = {key: value for key, value in record.items() if key != "event_sha256"}
    return _digest(_canonical(hashed_record, "STORE_CORRUPT"))


def read_state(db_path: str | Path) -> tuple[int, dict]:
    """Read one consistent, validated snapshot without creating a database."""
    connection = None
    try:
        connection = _connect(db_path, writable=False)
        connection.execute("BEGIN")
        revision, snapshot, _ = _validate_store(connection)
        connection.commit()
        return revision, snapshot
    except sqlite3.Error as error:
        raise _translate_sqlite(error) from error
    finally:
        if connection is not None:
            connection.close()


def history(db_path: str | Path, after_revision: int = 0) -> list[dict]:
    """Return public event envelopes, excluding requests and private snapshots."""
    if type(after_revision) is not int or after_revision < 0:
        raise StoreError("INVALID_REQUEST", "after_revision must be a nonnegative integer.")
    connection = None
    try:
        connection = _connect(db_path, writable=False)
        connection.execute("BEGIN")
        _, _, events = _validate_store(connection)
        records = [{"revision": record["revision"], "request_id": record["request_id"],
                    "event": _object_from_storage(record["event_json"])}
                   for record in events if record["revision"] > after_revision]
        connection.commit()
        return records
    except sqlite3.Error as error:
        raise _translate_sqlite(error) from error
    finally:
        if connection is not None:
            connection.close()


def transact(
    db_path: str | Path,
    request: dict,
    mutate: Callable[[dict | None, int], tuple[dict, dict, dict]],
    *,
    initialize: bool = False,
) -> dict:
    """Commit a snapshot, event, request fingerprint, and original response together."""
    request_json = _validate_request(request)
    connection = None
    try:
        connection = _connect(db_path, writable=True, initialize=initialize)
        connection.execute("BEGIN IMMEDIATE")
        entries = _schema_entries(connection)
        if not entries and initialize:
            revision, snapshot, events = 0, None, []
        else:
            revision, snapshot, events = _validate_store(connection)
        if revision:
            previous = connection.execute(
                "SELECT request_json, response_json FROM state_events WHERE request_id = ?",
                (request["request_id"],),
            ).fetchone()
            if previous is not None:
                if previous["request_json"] != request_json:
                    raise StoreError("REQUEST_CONFLICT", "request_id was used for a different request.")
                response = _object_from_storage(previous["response_json"])
                response["replayed"] = True
                connection.commit()
                return response
        if request["expected_revision"] != revision:
            raise StoreError("REVISION_CONFLICT", "expected_revision does not match the current revision.")
        if initialize and revision:
            raise StoreError("ALREADY_INITIALIZED", "The state database is already initialized.")
        new_snapshot, result, public_event = mutate(snapshot, revision)
        if any(type(value) is not dict for value in (new_snapshot, result, public_event)):
            raise StoreError("INVALID_MUTATION", "The mutation must return three JSON objects.")
        _check_snapshot_protocol(new_snapshot)
        new_revision = revision + 1
        snapshot_json = _canonical(new_snapshot, "INVALID_MUTATION")
        response = {"ok": True, "revision": new_revision, "result": result, "replayed": False}
        record = {
            "revision": new_revision,
            "request_id": request["request_id"],
            "request_json": request_json,
            "request_sha256": _digest(request_json),
            "event_json": _canonical(public_event, "INVALID_MUTATION"),
            "snapshot_json": snapshot_json,
            "snapshot_sha256": _digest(snapshot_json),
            "response_json": _canonical(response, "INVALID_MUTATION"),
            "previous_event_sha256": events[-1]["event_sha256"] if events else _CHAIN_ORIGIN,
        }
        record["event_sha256"] = _event_digest(record)
        if not revision:
            for definition in _SCHEMA.values():
                connection.execute(definition)
            connection.execute("INSERT INTO store_metadata VALUES (1, ?, ?)",
                               (SCHEMA_VERSION, PROTOCOL_VERSION))
            connection.execute("INSERT INTO state_snapshot VALUES (1, ?, ?, ?)",
                               (new_revision, snapshot_json, record["snapshot_sha256"]))
        else:
            connection.execute(
                "UPDATE state_snapshot SET revision = ?, snapshot_json = ?, snapshot_sha256 = ? WHERE singleton = 1",
                (new_revision, snapshot_json, record["snapshot_sha256"]),
            )
        connection.execute(
            "INSERT INTO state_events (revision, request_id, request_json, request_sha256, event_json, "
            "snapshot_json, snapshot_sha256, response_json, previous_event_sha256, event_sha256) "
            "VALUES (:revision, :request_id, :request_json, :request_sha256, :event_json, "
            ":snapshot_json, :snapshot_sha256, :response_json, :previous_event_sha256, :event_sha256)",
            record,
        )
        connection.commit()
        return response
    except sqlite3.Error as error:
        raise _translate_sqlite(error) from error
    finally:
        if connection is not None:
            connection.close()
