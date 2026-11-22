"""Independent black-box checks of the frozen agent-bootstrap/v1 CLI contract.

Only the two explicitly registered SQLite paths are fixtures.  The state service
creates and accesses them; this test never opens SQLite or implementation source.
Preparation refuses existing databases.  Results are an append-only JSONL record.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time
import uuid


BASE = Path(r"D:\lean")
STATE_CLI = BASE / "tools" / "agent_state.py"
BOOTSTRAP_CLI = BASE / "tools" / "agent_bootstrap.py"
HAPPY_DB = BASE / "logs" / "coordination" / "bootstrap-checker-happy-20261014.sqlite"
REJECTION_DB = BASE / "logs" / "coordination" / "bootstrap-checker-rejection-20261014.sqlite"
RESULTS_PATH = BASE / "logs" / "coordination" / "bootstrap-checker-results-20261014.json"
PROTOCOL = "iut-agent-tree/2026-10-13-v1"
PRIVATE_SECRET = "private-checkpoint-canary-20261014-7fc8"
RESULTS_LOCK = threading.Lock()
ROOT_ID = "fixture_parent"
HAPPY_CHILDREN = [
    "mutation_worker", "concurrent_child", "timeout_child", "interrupted_child",
    "private_child", "batch_first", "batch_second", "ready_child",
] + [f"cas_child_{index:02d}" for index in range(12)]
REJECTION_CHILDREN = [
    "wrong_parent_child", "wrong_context_child", "wrong_generation_child",
    "finished_child", "feedback_child", "unknown_child", "pending_child",
    "blocked_parent", "invalid_batch_first", "invalid_batch_last",
]


def ascii_json(value):
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def append_result(event, **fields):
    record = {"event": event, "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), **fields}
    with RESULTS_LOCK:
        with RESULTS_PATH.open("a", encoding="ascii", newline="\n") as stream:
            stream.write(ascii_json(record) + "\n")
    print(ascii_json(record), flush=True)


def invoke_state(database, payload):
    completed = subprocess.run(
        [sys.executable, "-X", "utf8", "-B", str(STATE_CLI), "--db", str(database)],
        input=ascii_json(payload) + "\n", capture_output=True, text=True,
        encoding="utf-8", timeout=20,
    )
    try:
        result = json.loads(completed.stdout)
    except ValueError as error:
        raise AssertionError(f"state service returned non-JSON; exit={completed.returncode}") from error
    return result


def require_success(result, operation):
    if not result.get("ok"):
        failure = result.get("error", {})
        code = failure.get("code", failure) if isinstance(failure, dict) else failure
        raise AssertionError(f"state {operation} failed: {code}")
    return result


class Fixture:
    def __init__(self, database):
        self.database = database
        self.run_id = "blackbox-happy-20261014" if database == HAPPY_DB else "blackbox-rejection-20261014"

    def inspect(self, agent_id, actor_id=ROOT_ID, generation=2):
        return require_success(invoke_state(self.database, {
            "op": "inspect", "actor_id": actor_id, "generation": generation,
            "agent_id": agent_id,
        }), "inspect")

    def agent(self, agent_id):
        return self.inspect(agent_id)["result"]["agent"]

    def context(self, agent_id):
        return {
            "run_id": self.run_id, "protocol_version": PROTOCOL,
            "contract_digest": self.agent(agent_id)["contract_digest"],
        }

    def mutate(self, operation, agent_id, actor_id=None, generation=2, context=None, **extras):
        actor_id = actor_id or agent_id
        for attempt in range(20):
            snapshot = self.inspect(actor_id, actor_id=actor_id, generation=generation) if actor_id != "@user" else self.inspect(agent_id, "@user", 0)
            target_context = context or self.context(agent_id)
            payload = {
                "op": operation, "request_id": "blackbox-" + uuid.uuid4().hex,
                "expected_revision": snapshot["revision"], "actor_id": actor_id,
                "generation": generation, "agent_id": agent_id,
                "context": target_context, **extras,
            }
            result = invoke_state(self.database, payload)
            if result.get("ok"):
                return result
            failure = result.get("error", {})
            code = failure.get("code", failure) if isinstance(failure, dict) else failure
            if code != "REVISION_CONFLICT":
                return require_success(result, operation)
        raise AssertionError("fixture could not settle after 20 explicit CAS conflicts")

    def activate_child(self, agent_id):
        current = self.agent(agent_id)
        if current["state"] == "NOT_READY":
            self.mutate("begin_recovery", agent_id, generation=1)
            current = self.agent(agent_id)
        if current["state"] == "RECOVERING":
            self.mutate("resume", agent_id, actor_id=ROOT_ID, recovery_generation=current["generation"])
            current = self.agent(agent_id)
        if current["state"] == "READY":
            self.mutate("start", agent_id, generation=current["generation"])
        return self.agent(agent_id)

    def child_input(self, agent_id, timeout=4, retries=8, continuation=None, from_generation=1):
        return {
            "schema": "agent-bootstrap/v1", "mode": "child",
            "ticket": "blackbox-" + agent_id,
            "actor_id": agent_id, "parent_id": ROOT_ID,
            "from_generation": from_generation, "recovery_generation": from_generation + 1,
            "context": self.context(agent_id),
            "limits": {"timeout_seconds": timeout, "max_cas_retries": retries},
            "continuation": continuation,
        }

    def parent_input(self, agent_ids, timeout=12, retries=8):
        return {
            "schema": "agent-bootstrap/v1", "mode": "parent",
            "ticket": "blackbox-parent-" + agent_ids[0],
            "actor_id": ROOT_ID, "generation": 2, "context": self.context(ROOT_ID),
            "children": [{"agent_id": agent_id, "context": self.context(agent_id), "recovery_generation": 2} for agent_id in agent_ids],
            "limits": {"timeout_seconds": timeout, "max_cas_retries": retries},
            "continuation": None,
        }

    def history(self):
        return require_success(invoke_state(self.database, {
            "op": "history", "actor_id": ROOT_ID, "generation": 2, "after_revision": 0,
        }), "history")


def helper_process(database):
    return subprocess.Popen(
        [sys.executable, "-X", "utf8", "-B", str(BOOTSTRAP_CLI), "--db", str(database)],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", bufsize=1,
    )


def parse_helper(completed_code, stdout, stderr):
    assert PRIVATE_SECRET not in stdout + stderr, "private checkpoint leaked from helper"
    assert stdout.isascii(), "helper stdout is not ASCII transport"
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    assert rows, "helper emitted no public receipt"
    for row in rows:
        assert row.get("schema") == "agent-bootstrap/v1", "wrong event schema"
        assert isinstance(row.get("observations"), list), "missing compact observations"
        assert "checkpoint" not in ascii_json(row), "private checkpoint field leaked"
    return {"exit_code": completed_code, "rows": rows, "final": rows[-1]}


def invoke_helper(database, payload):
    process = helper_process(database)
    stdout, stderr = process.communicate(ascii_json(payload) + "\n", timeout=payload["limits"]["timeout_seconds"] + 20)
    result = parse_helper(process.returncode, stdout, stderr)
    retry_events = sum(row.get("status") == "retrying" and row.get("code") == "REVISION_CONFLICT" for row in result["rows"])
    append_result("helper_receipt", database=str(database), ticket=payload.get("ticket"), receipt=result["final"], exit_code=result["exit_code"], explicit_retry_events=retry_events)
    return result


def latest_saved_receipts():
    latest = {}
    with RESULTS_PATH.open("r", encoding="ascii") as stream:
        for line in stream:
            if not line.strip():
                continue
            record = json.loads(line)
            if record.get("event") == "helper_receipt":
                latest[record["ticket"]] = record["receipt"]
    return latest


def assert_receipt(result, status, exit_code):
    assert result["exit_code"] == exit_code, f"exit {result['exit_code']} expected {exit_code}; status={result['final'].get('status')} code={result['final'].get('code')}"
    assert result["final"].get("status") == status, f"status={result['final'].get('status')} code={result['final'].get('code')}"


def prepare_fixture(database, child_ids, rejection=False):
    assert not database.exists(), f"refusing to reset existing database: {database}"
    for suffix in ("-journal", "-wal", "-shm"):
        assert not Path(str(database) + suffix).exists(), f"unexpected fixture sidecar: {suffix}"
    fixture = Fixture(database)
    def registration(agent_id, parent_id):
        target = "Verify exact lifecycle transitions; Unicode hypothesis: \u91cf\u8bcd\u4e0e\u5047\u8bbe \u2200 x \u03b1" if agent_id == "concurrent_child" else "Verify " + agent_id
        return {
            "agent_id": agent_id, "parent_id": parent_id, "role": "blackbox_fixture",
            "provider": "offline", "model": "no-model-execution", "files": [],
            "contract": {"version": "bootstrap-blackbox-fixture-v1", "target": target,
                "variables": [], "quantifiers": [], "assumptions": [],
                "conclusion": "Only observed lifecycle behavior is accepted", "dependencies": []},
        }
    agents = [registration(ROOT_ID, None)] + [registration(agent_id, ROOT_ID) for agent_id in child_ids]
    if rejection:
        agents.append(registration("blocked_parent_child", "blocked_parent"))
    initialized = require_success(invoke_state(database, {
        "op": "init", "request_id": "blackbox-fixture-init-20261014", "expected_revision": 0,
        "run_id": fixture.run_id, "protocol_version": PROTOCOL, "agents": agents,
    }), "init")
    root = fixture.inspect(ROOT_ID, "@user", 0)["result"]["agent"]
    context = {"run_id": fixture.run_id, "protocol_version": PROTOCOL, "contract_digest": root["contract_digest"]}
    fixture.mutate("begin_recovery", ROOT_ID, generation=1, context=context)
    fixture.mutate("resume", ROOT_ID, actor_id="@user", generation=0, context=context, recovery_generation=2)
    fixture.mutate("start", ROOT_ID, context=context)
    fixture.mutate("checkpoint", ROOT_ID, checkpoint={"secret": PRIVATE_SECRET}, summary="Public fixture parent")
    append_result("fixture_prepared", database=str(database), registered_nodes=len(agents), initialized_revision=initialized["revision"])
    return fixture


def prepare():
    for database in (HAPPY_DB, REJECTION_DB):
        assert not database.exists(), "prepare requires both registered databases to be absent"
    happy = prepare_fixture(HAPPY_DB, HAPPY_CHILDREN)
    happy.activate_child("mutation_worker")
    happy.activate_child("private_child")
    happy.mutate("checkpoint", "private_child", checkpoint={"secret": PRIVATE_SECRET}, summary="Public child summary")
    rejection = prepare_fixture(REJECTION_DB, REJECTION_CHILDREN, rejection=True)
    for agent_id in ("finished_child", "feedback_child", "unknown_child", "pending_child", "blocked_parent"):
        rejection.activate_child(agent_id)
    rejection.mutate("finish", "finished_child")
    rejection.mutate("wait", "feedback_child", feedback_id="feedback-blackbox-v1", message="Frozen public question")
    rejection.mutate("begin_operation", "pending_child", operation_id="pending-operation-v1", description="Blackbox unresolved operation")
    rejection.mutate("begin_operation", "unknown_child", operation_id="unknown-operation-v1", description="Blackbox uncertain operation")
    rejection.mutate("begin_recovery", "unknown_child")
    rejection.mutate("wait", "blocked_parent", feedback_id="blocked-parent-feedback-v1", message="Frozen parent question")
    append_result("fixture_states_seeded", happy_nodes=len(HAPPY_CHILDREN) + 1, rejection_nodes=len(REJECTION_CHILDREN) + 2)


def concurrent_handshake():
    fixture = Fixture(HAPPY_DB)
    child_input = fixture.child_input("concurrent_child", timeout=15)
    parent_input = fixture.parent_input(["concurrent_child"], timeout=15)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        child_future = executor.submit(invoke_helper, HAPPY_DB, child_input)
        parent_future = executor.submit(invoke_helper, HAPPY_DB, parent_input)
        child_result, parent_result = child_future.result(), parent_future.result()
    assert_receipt(child_result, "ready", 0)
    assert_receipt(parent_result, "ready", 0)
    agent = fixture.agent("concurrent_child")
    assert (agent["generation"], agent["state"]) == (2, "RUNNING")
    assert any(row.get("status") == "waiting" and row.get("code") == "WAITING_PARENT" for row in child_result["rows"]), "child did not publish WAITING_PARENT"
    return {"generation": agent["generation"], "child_events": len(child_result["rows"]), "parent_events": len(parent_result["rows"]), "unicode_contract": True}


def timeout_reentry():
    fixture = Fixture(HAPPY_DB)
    agent_id = "ready_child"
    payload = fixture.child_input(agent_id, timeout=3)
    first = invoke_helper(HAPPY_DB, payload)
    assert_receipt(first, "timeout", 2)
    assert fixture.agent(agent_id)["generation"] == 2
    payload["continuation"] = first["final"]["continuation"]
    second = invoke_helper(HAPPY_DB, payload)
    assert_receipt(second, "timeout", 2)
    assert fixture.agent(agent_id)["generation"] == 2
    assert_receipt(invoke_helper(HAPPY_DB, fixture.parent_input([agent_id])), "ready", 0)
    payload["continuation"] = second["final"]["continuation"]
    payload["limits"]["timeout_seconds"] = 6
    third = invoke_helper(HAPPY_DB, payload)
    assert_receipt(third, "ready", 0)
    before = fixture.inspect(agent_id)["revision"]
    payload["continuation"] = third["final"]["continuation"]
    fourth = invoke_helper(HAPPY_DB, payload)
    assert_receipt(fourth, "ready", 0)
    after = fixture.inspect(agent_id)["revision"]
    assert before == after, "RUNNING reentry performed an extra mutation"
    assert fixture.agent(agent_id)["generation"] == 2
    return {"timeout_receipts": 2, "reentry_generation": 2, "running_reentry_revision_unchanged": True}


def interrupted_pending_reentry():
    fixture = Fixture(HAPPY_DB)
    payload = fixture.child_input("interrupted_child", timeout=5)
    process = helper_process(HAPPY_DB)
    process.stdin.write(ascii_json(payload) + "\n")
    process.stdin.close()
    process.stdin = None
    rows = []
    pending = None
    deadline = time.monotonic() + 12
    while time.monotonic() < deadline:
        line = process.stdout.readline()
        if not line:
            break
        row = json.loads(line)
        rows.append(row)
        if row.get("status") == "pending":
            pending = row
            process.kill()
            break
    process.communicate(timeout=10)
    assert pending is not None, "no flushed pending event before mutation"
    assert pending.get("continuation", {}).get("pending"), "pending event lacks recoverable request"
    assert PRIVATE_SECRET not in ascii_json(rows)
    payload["continuation"] = pending["continuation"]
    payload["limits"]["timeout_seconds"] = 3
    resumed = invoke_helper(HAPPY_DB, payload)
    assert_receipt(resumed, "timeout", 2)
    assert fixture.agent("interrupted_child")["generation"] == 2
    assert_receipt(invoke_helper(HAPPY_DB, fixture.parent_input(["interrupted_child"])), "ready", 0)
    payload["continuation"] = resumed["final"]["continuation"]
    payload["limits"]["timeout_seconds"] = 6
    complete = invoke_helper(HAPPY_DB, payload)
    assert_receipt(complete, "ready", 0)
    assert fixture.agent("interrupted_child")["generation"] == 2
    return {"interruption_boundary": "flushed pending event", "pending_continuation_reentered": True, "final_generation": 2, "limitation": "exact service commit timing is deliberately unknown"}


def batch_progress_retained():
    fixture = Fixture(HAPPY_DB)
    fixture.mutate("begin_recovery", "batch_first", generation=1)
    payload = fixture.parent_input(["batch_first", "batch_second"], timeout=3)
    first = invoke_helper(HAPPY_DB, payload)
    assert_receipt(first, "timeout", 2)
    assert fixture.agent("batch_first")["state"] == "READY"
    assert fixture.agent("batch_second")["state"] == "NOT_READY"
    payload["continuation"] = first["final"]["continuation"]
    payload["limits"]["timeout_seconds"] = 10
    child_payload = fixture.child_input("batch_second", timeout=10)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        parent_future = executor.submit(invoke_helper, HAPPY_DB, payload)
        child_future = executor.submit(invoke_helper, HAPPY_DB, child_payload)
        parent_result, child_result = parent_future.result(), child_future.result()
    assert_receipt(parent_result, "ready", 0)
    assert_receipt(child_result, "ready", 0)
    assert_receipt(invoke_helper(HAPPY_DB, fixture.child_input("batch_first")), "ready", 0)
    assert all(fixture.agent(agent_id)["generation"] == 2 for agent_id in ("batch_first", "batch_second"))
    return {"earlier_resume_retained_at_timeout": True, "resumed_batch_complete": True}


def private_checkpoint_absence():
    fixture = Fixture(HAPPY_DB)
    child = invoke_helper(HAPPY_DB, fixture.child_input("private_child"))
    parent = invoke_helper(HAPPY_DB, fixture.parent_input(["private_child"]))
    assert_receipt(child, "ready", 0)
    assert_receipt(parent, "ready", 0)
    return {"private_canaries": 2, "tested_modes": ["child", "parent"]}


def refusal_cases():
    fixture = Fixture(REJECTION_DB)
    outcomes = []
    for agent_id, field, replacement in [
        ("wrong_parent_child", "parent_id", "unrelated_parent"),
        ("wrong_context_child", "context", {"run_id": fixture.run_id, "protocol_version": PROTOCOL, "contract_digest": "0" * 64}),
        ("wrong_generation_child", "from_generation", 7),
    ]:
        payload = fixture.child_input(agent_id)
        payload[field] = replacement
        if field == "from_generation":
            payload["recovery_generation"] = 8
        before = fixture.inspect(agent_id)["revision"]
        result = invoke_helper(REJECTION_DB, payload)
        assert_receipt(result, "blocked", 2)
        assert fixture.inspect(agent_id)["revision"] == before, "invalid request changed state"
        outcomes.append({"case": field, "code": result["final"].get("code")})
    for agent_id, from_generation in [("finished_child", 1), ("feedback_child", 1), ("unknown_child", 2), ("pending_child", 1)]:
        before = fixture.inspect(agent_id)["revision"]
        result = invoke_helper(REJECTION_DB, fixture.child_input(agent_id, from_generation=from_generation))
        assert_receipt(result, "blocked", 2)
        assert fixture.inspect(agent_id)["revision"] == before, "blocked lifecycle changed state"
        outcomes.append({"case": agent_id, "code": result["final"].get("code")})
    return {"refusals": outcomes, "unchanged_state_count": len(outcomes)}


def schema_rejections():
    fixture = Fixture(REJECTION_DB)
    base = fixture.child_input("wrong_context_child")
    invalid_payloads = []
    extra = dict(base, undocumented=True)
    invalid_payloads.append(extra)
    invalid_payloads.append(dict(base, limits={"timeout_seconds": 0, "max_cas_retries": 8}))
    invalid_payloads.append(dict(base, limits={"timeout_seconds": 2, "max_cas_retries": 9}))
    invalid_payloads.append(dict(base, ticket="\u975eASCII"))
    parent = fixture.parent_input(["invalid_batch_first"])
    parent["children"].append(dict(parent["children"][0]))
    invalid_payloads.append(parent)
    before = fixture.inspect(ROOT_ID)["revision"]
    for payload in invalid_payloads:
        result = invoke_helper(REJECTION_DB, payload)
        assert_receipt(result, "rejected", 1)
    assert fixture.inspect(ROOT_ID)["revision"] == before
    return {"malformed_requests_rejected": len(invalid_payloads)}


def parent_validates_entire_batch():
    fixture = Fixture(REJECTION_DB)
    if fixture.agent("invalid_batch_first")["state"] == "NOT_READY":
        fixture.mutate("begin_recovery", "invalid_batch_first", generation=1)
    assert fixture.agent("invalid_batch_first")["state"] == "RECOVERING"
    payload = fixture.parent_input(["invalid_batch_first", "invalid_batch_last"])
    payload["children"][1]["context"]["contract_digest"] = "0" * 64
    before = fixture.inspect(ROOT_ID)["revision"]
    result = invoke_helper(REJECTION_DB, payload)
    assert_receipt(result, "blocked", 2)
    assert fixture.inspect(ROOT_ID)["revision"] == before, "batch resumed first child before validating last child"
    assert fixture.agent("invalid_batch_first")["state"] == "RECOVERING"
    return {"invalid_last_child_prevented_first_resume": True, "code": result["final"].get("code")}


def blocked_parent_refusal():
    fixture = Fixture(REJECTION_DB)
    snapshot = fixture.inspect("blocked_parent_child", actor_id="blocked_parent", generation=2)
    target = snapshot["result"]["agent"]
    payload = {
        "schema": "agent-bootstrap/v1", "mode": "parent", "ticket": "blackbox-blocked-parent",
        "actor_id": "blocked_parent", "generation": 2, "context": fixture.context("blocked_parent"),
        "children": [{"agent_id": "blocked_parent_child", "context": {"run_id": fixture.run_id, "protocol_version": PROTOCOL, "contract_digest": target["contract_digest"]}, "recovery_generation": 2}],
        "limits": {"timeout_seconds": 4, "max_cas_retries": 8}, "continuation": None,
    }
    before = fixture.inspect(ROOT_ID)["revision"]
    result = invoke_helper(REJECTION_DB, payload)
    assert_receipt(result, "blocked", 2)
    assert fixture.inspect(ROOT_ID)["revision"] == before
    return {"blocked_parent_cannot_resume": True, "code": result["final"].get("code")}


def explicit_cas_contention():
    fixture = Fixture(HAPPY_DB)
    children = [f"cas_child_{index:02d}" for index in range(12)]
    saved = latest_saved_receipts()
    payloads = [fixture.child_input(agent_id, timeout=15, retries=8, continuation=saved.get("blackbox-" + agent_id, {}).get("continuation")) for agent_id in children]
    stopped = threading.Event()
    mutation_counts = []
    def concurrent_checkpoints():
        completed = 0
        while not stopped.is_set() and completed < 35:
            fixture.mutate("checkpoint", "mutation_worker", checkpoint={"counter": completed}, summary="Harmless CAS contention")
            completed += 1
        mutation_counts.append(completed)
    with concurrent.futures.ThreadPoolExecutor(max_workers=13) as executor:
        mutation_future = executor.submit(concurrent_checkpoints)
        futures = [executor.submit(invoke_helper, HAPPY_DB, payload) for payload in payloads]
        results = [future.result() for future in futures]
        stopped.set()
        mutation_future.result()
    conflict_events = sum(sum(row.get("status") == "retrying" and row.get("code") == "REVISION_CONFLICT" for row in result["rows"]) for result in results)
    conflict_counts = [result["final"].get("cas_conflicts", 0) for result in results]
    assert all(isinstance(count, int) and 0 <= count <= 9 for count in conflict_counts), "conflict retries not bounded by configured budget"
    assert all(result["final"].get("status") in ("timeout", "blocked", "unknown") for result in results)
    for result in results:
        if result["final"]["status"] == "unknown":
            assert result["exit_code"] == 3 and result["final"]["continuation"]["pending"], "uncertain mutation must preserve its pending continuation"
    assert all(fixture.agent(agent_id)["generation"] in (1, 2) for agent_id in children)
    if conflict_events == 0:
        return {"gap": "no explicit helper CAS conflict observed in concurrent actual CLI runs", "concurrent_children": 12, "checkpoint_mutations": sum(mutation_counts)}
    assert sum(conflict_counts) >= conflict_events, "retry events exceed reported conflict counts"
    return {"explicit_retry_events": conflict_events, "reported_cumulative_conflicts": conflict_counts, "checkpoint_mutations": sum(mutation_counts), "configured_retry_budget": 8, "budget_exhausted_receipts": sum(result["final"].get("status") == "blocked" and result["final"].get("code") == "REVISION_CONFLICT" for result in results)}


def uncertain_receipt_reentry():
    fixture = Fixture(HAPPY_DB)
    uncertain = {}
    with RESULTS_PATH.open("r", encoding="ascii") as stream:
        for line in stream:
            if not line.strip():
                continue
            record = json.loads(line)
            ticket = record.get("ticket", "")
            receipt = record.get("receipt", {})
            if record.get("event") == "helper_receipt" and ticket.startswith("blackbox-cas_child_") and receipt.get("status") == "unknown":
                uncertain[ticket] = receipt
    assert uncertain, "no actual uncertain receipt available for this follow-up"
    recovered = []
    for ticket, receipt in uncertain.items():
        agent_id = ticket.removeprefix("blackbox-")
        continuation = receipt["continuation"]
        payload = fixture.child_input(agent_id, timeout=3, continuation=continuation)
        result = invoke_helper(HAPPY_DB, payload)
        assert_receipt(result, "timeout", 2)
        pending_events = [row for row in result["rows"] if row.get("status") == "pending"]
        assert pending_events and pending_events[0]["continuation"]["pending"] == continuation["pending"], "first replay did not preserve the uncertain request identity"
        assert result["final"]["continuation"]["pending"] is None
        assert fixture.agent(agent_id)["generation"] == 2
        recovered.append(agent_id)
    return {"actual_unknown_receipts_recovered": len(recovered), "first_pending_identity_preserved": True, "final_generation": 2}


def mixed_blocked_siblings():
    fixture = Fixture(REJECTION_DB)
    expected_blockers = {
        "finished_child": "FINISHED", "feedback_child": "PENDING_FEEDBACK",
        "pending_child": "PENDING_OPERATION", "unknown_child": "UNKNOWN_OPERATION",
    }
    agent_ids = ["invalid_batch_first", *expected_blockers]
    before = {agent_id: fixture.agent(agent_id) for agent_id in agent_ids}
    assert before["invalid_batch_first"]["state"] == "RECOVERING"
    payload = fixture.parent_input(agent_ids)
    for child in payload["children"]:
        if child["agent_id"] == "unknown_child":
            child["recovery_generation"] = 3
    result = invoke_helper(REJECTION_DB, payload)
    assert_receipt(result, "blocked", 2)
    assert result["final"].get("code") == "CHILDREN_BLOCKED"
    actual_blockers = {child["agent_id"]: child["code"] for child in result["final"].get("blocked_children", [])}
    assert actual_blockers == expected_blockers, "blocked sibling list did not match actual lifecycle barriers"
    assert fixture.agent("invalid_batch_first")["state"] == "READY"
    for agent_id in expected_blockers:
        after = fixture.agent(agent_id)
        assert (after["generation"], after["state"]) == (before[agent_id]["generation"], before[agent_id]["state"])
    return {"eligible_sibling_resumed": True, "blocked_siblings_preserved": len(expected_blockers), "final_code": "CHILDREN_BLOCKED", "whole_batch_success_claimed": False}


CASES = {
    "concurrent_handshake": concurrent_handshake,
    "timeout_reentry": timeout_reentry,
    "interrupted_pending_reentry": interrupted_pending_reentry,
    "batch_progress_retained": batch_progress_retained,
    "private_checkpoint_absence": private_checkpoint_absence,
    "refusal_cases": refusal_cases,
    "schema_rejections": schema_rejections,
    "parent_validates_entire_batch": parent_validates_entire_batch,
    "blocked_parent_refusal": blocked_parent_refusal,
    "explicit_cas_contention": explicit_cas_contention,
    "uncertain_receipt_reentry": uncertain_receipt_reentry,
    "mixed_blocked_siblings": mixed_blocked_siblings,
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--case", choices=list(CASES), action="append")
    options = parser.parse_args()
    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    append_result("invocation", source_sha256=source_hash, prepare=options.prepare, cases=options.case)
    if options.prepare:
        prepare()
    failures = []
    if options.run or options.case:
        for name in options.case or CASES:
            started = time.monotonic()
            try:
                evidence = CASES[name]()
                append_result("case_result", case=name, status="gap" if "gap" in evidence else "passed", elapsed_seconds=round(time.monotonic() - started, 3), evidence=evidence, source_sha256=source_hash)
            except Exception as error:
                failures.append(name)
                append_result("case_result", case=name, status="failed", error_type=type(error).__name__, error=str(error), elapsed_seconds=round(time.monotonic() - started, 3), source_sha256=source_hash)
        append_result("suite_result", failed_cases=failures, selected_cases=options.case or list(CASES), source_sha256=source_hash)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
