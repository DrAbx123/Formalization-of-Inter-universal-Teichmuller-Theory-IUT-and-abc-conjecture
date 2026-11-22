"""Blackbox scenarios for the frozen durable coordination CLI v1.

This harness owns only this file and the literal SQLite paths below.  It never
imports or inspects the implementation, and never relays raw child diagnostics.
"""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


DATABASE = Path(r"D:\lean\tmp\agent-state-tests-20261013.sqlite")
DATABASE_FILES = (
    DATABASE,
    Path(str(DATABASE) + "-journal"),
    Path(str(DATABASE) + "-wal"),
    Path(str(DATABASE) + "-shm"),
)
IMPLEMENTATION = r"D:\lean\tools\agent_state.py"
PROTOCOL = "iut-agent-tree/2026-10-13-v1"
RUN_ID = "coordination-state-scenarios-20261013"
AGENT_IDS = ("test_root", "test_domain", "test_module", "test_file", "test_worker", "test_peer")
PARENTS = dict(zip(AGENT_IDS, (None, "test_root", "test_domain", "test_module", "test_file", "test_root")))


class ScenarioFailure(Exception):
    """A sanitized failure, safe to print without implementation diagnostics."""


def require(condition: bool, label: str) -> None:
    if not condition:
        raise ScenarioFailure(label)


def invoke(request: dict) -> dict:
    try:
        process = subprocess.run(
            [sys.executable, "-B", IMPLEMENTATION, "--db", str(DATABASE)],
            input=json.dumps(request, ensure_ascii=False),
            text=True,
            encoding="utf-8",
            capture_output=True,
            timeout=20,
            check=False,
        )
    except subprocess.TimeoutExpired:
        raise ScenarioFailure("CLI process exceeded 20 seconds") from None
    except OSError as error:
        raise ScenarioFailure("CLI process could not start: " + type(error).__name__) from None
    try:
        response = json.loads(process.stdout)
    except (ValueError, TypeError):
        fingerprint = hashlib.sha256(process.stdout.encode("utf-8")).hexdigest()[:12]
        raise ScenarioFailure(
            "CLI did not emit one JSON document; exit=" + str(process.returncode)
            + ", stdout_bytes=" + str(len(process.stdout.encode("utf-8")))
            + ", stdout_sha256=" + fingerprint
        ) from None
    require(isinstance(response, dict), "CLI response must be an object")
    require(isinstance(response.get("ok"), bool), "CLI response must include boolean ok")
    require(process.returncode == (0 if response["ok"] else 1), "CLI exit status disagrees with ok")
    require(not process.stderr.strip(), "CLI emitted unexpected stderr (suppressed)")
    if response["ok"]:
        require(isinstance(response.get("revision"), int), "Success response lacks revision")
        require("result" in response, "Success response lacks result")
    else:
        require(isinstance(response.get("error"), dict), "Error response lacks error object")
        require(isinstance(response["error"].get("code"), str), "Error response lacks code")
        require(isinstance(response["error"].get("message"), str), "Error response lacks message")
    return response


def reset_database() -> None:
    for path in DATABASE_FILES:
        require(path.parent == Path(r"D:\lean\tmp"), "Refusing cleanup outside assigned directory")
        if path.exists():
            path.unlink()


def contract_for(agent_id: str) -> dict:
    return {
        "version": "scenario-contract-v1",
        "target": "Exercise durable state for " + agent_id,
        "variables": ["logical identity"],
        "quantifiers": ["each registered generation"],
        "assumptions": ["registered direct parent"],
        "conclusion": "State transitions preserve the frozen test contract",
        "dependencies": [],
    }


def init_request() -> dict:
    return {
        "op": "init",
        "request_id": "scenario-init",
        "expected_revision": 0,
        "run_id": RUN_ID,
        "protocol_version": PROTOCOL,
        "agents": [
            {
                "agent_id": agent_id,
                "parent_id": PARENTS[agent_id],
                "role": "scenario " + agent_id,
                "provider": "local-test",
                "model": "blackbox-harness",
                "files": [{"path": "D:\\lean\\tmp\\scenario-" + agent_id + ".txt", "mode": "append" if agent_id == "test_root" else "read_write"}],
                "contract": contract_for(agent_id),
            }
            for agent_id in AGENT_IDS
        ],
    }


def reversed_keys(value):
    if isinstance(value, dict):
        return {key: reversed_keys(item) for key, item in reversed(list(value.items()))}
    if isinstance(value, list):
        return [reversed_keys(item) for item in value]
    return value


def serialized_contains(value, needle: str) -> bool:
    return needle in json.dumps(value, ensure_ascii=False, sort_keys=True)


class Harness:
    def __init__(self):
        self.revision = 0
        self.counter = 0
        self.generations = {agent_id: 1 for agent_id in AGENT_IDS}
        self.digests = {}
        self.passed = []

    def mark(self, label: str) -> None:
        self.passed.append(label)

    def request(self, op: str, agent_id: str, actor_id=None, **extras) -> dict:
        self.counter += 1
        actor_id = agent_id if actor_id is None else actor_id
        request = {
            "op": op,
            "request_id": "scenario-request-" + str(self.counter),
            "expected_revision": self.revision,
            "actor_id": actor_id,
            "generation": 0 if actor_id == "@user" else self.generations[actor_id],
            "agent_id": agent_id,
            "context": {
                "run_id": RUN_ID,
                "protocol_version": PROTOCOL,
                "contract_digest": self.digests[agent_id],
            },
        }
        request.update(extras)
        if op == "reply" and "target_generation" not in request:
            request["target_generation"] = self.generations[agent_id]
        return request

    def accept(self, request: dict, expected_state=None) -> dict:
        response = invoke(request)
        require(response["ok"], "Expected success for " + request["op"] + "; code=" + response.get("error", {}).get("code", "missing"))
        require(response["revision"] == self.revision + 1, "Successful mutation must increment revision exactly once")
        require(response.get("replayed") is False, "Fresh mutation must set replayed=false")
        self.revision = response["revision"]
        if expected_state is not None:
            require(response["result"]["agent"]["state"] == expected_state, "Unexpected state after " + request["op"])
        return response

    def inspect(self, agent_id: str, actor_id=None, generation=None) -> dict:
        actor_id = agent_id if actor_id is None else actor_id
        return invoke({
            "op": "inspect",
            "actor_id": actor_id,
            "generation": self.generations[actor_id] if generation is None else generation,
            "agent_id": agent_id,
        })

    def current_revision(self) -> int:
        response = self.inspect("test_root")
        require(response["ok"], "Root self inspect failed")
        return response["revision"]

    def reject(self, request: dict, label: str, code=None) -> dict:
        before_revision = self.current_revision()
        response = invoke(request)
        require(not response["ok"], "Expected rejection: " + label)
        if code is not None:
            require(response["error"]["code"] == code, "Unexpected error code: " + label)
        require(self.current_revision() == before_revision == self.revision, "Rejected request changed revision: " + label)
        self.mark(label)
        return response

    def history(self, agent_id: str, after_revision=0) -> dict:
        response = invoke({
            "op": "history",
            "actor_id": agent_id,
            "generation": self.generations[agent_id],
            "after_revision": after_revision,
        })
        require(response["ok"], "History request failed")
        require(response["revision"] == self.revision, "Read changed or lost revision")
        return response

    def recover_and_resume(self, agent_id: str) -> None:
        self.accept(self.request("begin_recovery", agent_id), "RECOVERING")
        self.generations[agent_id] += 1
        self.accept(self.request(
            "resume", agent_id, actor_id=PARENTS[agent_id] or "@user",
            recovery_generation=self.generations[agent_id],
        ), "READY")

    def initialize(self) -> dict:
        request = init_request()
        response = self.accept(request)
        require(response["result"]["run_id"] == RUN_ID, "Init run ID mismatch")
        summaries = response["result"]["agents"]
        require({item["agent_id"] for item in summaries} == set(AGENT_IDS), "Init summaries must cover registered agents")
        for item in summaries:
            require(item["generation"] == 1 and item["state"] == "NOT_READY", "Initial generation/state mismatch")
            self.digests[item["agent_id"]] = item["contract_digest"]
        self.mark("six agents registered across five hierarchy levels")
        return response

    def invalid_initializations(self) -> None:
        mutations = []
        missing_parent = init_request()
        missing_parent["agents"][1]["parent_id"] = "unregistered-parent"
        mutations.append(("invalid parent rejected atomically", missing_parent))
        cyclic = init_request()
        cyclic["agents"][1]["parent_id"] = "test_module"
        mutations.append(("disconnected parent cycle rejected atomically", cyclic))
        multiroot = init_request()
        multiroot["agents"][-1]["parent_id"] = None
        mutations.append(("multiple roots rejected atomically", multiroot))
        readonly_duplicate = init_request()
        readonly_duplicate["agents"][0]["files"] = [{"path": r"D:\lean\tmp\shared-scenario.txt", "mode": "read"}]
        readonly_duplicate["agents"][1]["files"] = [{"path": r"d:/LEAN/tmp/shared-scenario.txt", "mode": "read"}]
        mutations.append(("duplicate read ownership rejected after Windows normalization", readonly_duplicate))
        append_collision = init_request()
        append_collision["agents"][0]["files"] = [{"path": r"D:\lean\tmp\shared-append-scenario.txt", "mode": "append"}]
        append_collision["agents"][1]["files"] = [{"path": r"d:/LEAN/tmp/shared-append-scenario.txt", "mode": "read"}]
        mutations.append(("append/read ownership collision rejected atomically", append_collision))
        extra_field = init_request()
        extra_field["undeclared"] = True
        mutations.append(("extra init field rejected atomically", extra_field))
        missing_conclusion = init_request()
        del missing_conclusion["agents"][0]["contract"]["conclusion"]
        mutations.append(("incomplete frozen contract rejected atomically", missing_conclusion))
        empty_target = init_request()
        empty_target["agents"][0]["contract"]["target"] = ""
        mutations.append(("empty frozen target rejected atomically", empty_target))
        missing_evidence = init_request()
        missing_evidence["agents"][0]["contract"]["dependencies"] = [{"dependency_id": "local-proof", "version": "v1"}]
        mutations.append(("dependency without evidence rejected atomically", missing_evidence))
        unknown_contract_field = init_request()
        unknown_contract_field["agents"][0]["contract"]["undeclared"] = True
        mutations.append(("extra frozen contract field rejected atomically", unknown_contract_field))
        for label, request in mutations:
            reset_database()
            response = invoke(request)
            require(not response["ok"], label)
            if label.startswith("extra"):
                require(response["error"]["code"] == "INVALID_REQUEST", "Extra init field must be INVALID_REQUEST")
            valid = invoke(init_request())
            require(valid["ok"] and valid["revision"] == 1, "Rejected init left durable state: " + label)
            self.mark(label)
        reset_database()

    def run(self) -> None:
        self.invalid_initializations()
        initial = self.initialize()
        self.mark("append mode accepted for an exclusively assigned file")
        replay = invoke(reversed_keys(init_request()))
        expected_replay = copy.deepcopy(initial)
        expected_replay["replayed"] = True
        require(replay == expected_replay, "Canonical replay must preserve original durable response")
        self.mark("init response replays identically across fresh processes and JSON key order")
        conflicting_init = init_request()
        conflicting_init["run_id"] = "different-run-id"
        self.reject(conflicting_init, "changed complete request cannot reuse request ID", "REQUEST_CONFLICT")

        for agent_id in AGENT_IDS:
            self.recover_and_resume(agent_id)
            self.accept(self.request("start", agent_id), "RUNNING")
        self.mark("five hierarchy levels recover via direct parent and enter RUNNING")
        self.reject(self.request("finish", "test_file"), "supervisor cannot finish with unfinished direct child", "UNFINISHED_CHILDREN")
        user_view = invoke({"op": "inspect", "actor_id": "@user", "generation": 0, "agent_id": "test_root"})
        require(user_view["ok"], "User must be able to inspect root public summary")
        self.reject({"op": "inspect", "actor_id": "@user", "generation": 0, "agent_id": "test_domain"}, "user inspect restricted to unique root")
        self.mark("user may inspect unique root public summary")

        worker = "test_worker"
        stale_generation = self.request("checkpoint", worker, checkpoint={}, summary="stale generation")
        stale_generation["generation"] -= 1
        self.reject(stale_generation, "stale execution generation rejected")
        for context_key, bad_value in (
            ("run_id", "wrong-run"),
            ("protocol_version", "wrong-protocol"),
            ("contract_digest", "wrong-contract"),
        ):
            wrong_context = self.request("checkpoint", worker, checkpoint={}, summary="wrong context")
            wrong_context["context"][context_key] = bad_value
            self.reject(wrong_context, "mismatched " + context_key + " rejected")

        checkpoint_secret = "private-checkpoint-sentinel-8ab5eb5b"
        checkpoint_request = self.request("checkpoint", worker, checkpoint={"secret": checkpoint_secret}, summary="worker checkpoint persisted")
        checkpoint_response = self.accept(checkpoint_request, "RUNNING")
        require(not serialized_contains(checkpoint_response, checkpoint_secret), "Mutation result disclosed private checkpoint")
        self_view = self.inspect(worker)
        require(self_view["ok"] and serialized_contains(self_view["result"], checkpoint_secret), "Self inspect did not recover persisted private checkpoint")
        parent_view = self.inspect(worker, actor_id="test_file")
        require(parent_view["ok"] and not serialized_contains(parent_view, checkpoint_secret), "Parent inspect disclosed private checkpoint")
        require(not serialized_contains(self.history(worker), checkpoint_secret), "Self history disclosed private checkpoint")
        require(not serialized_contains(self.history("test_file"), checkpoint_secret), "Parent history disclosed private checkpoint")
        self.mark("checkpoint persists after process exit and remains private from results/parent/history")

        self.reject({"op": "inspect", "actor_id": "test_root", "generation": self.generations["test_root"], "agent_id": worker}, "ancestor cannot inspect beyond direct child")
        self.reject({"op": "inspect", "actor_id": "test_peer", "generation": self.generations["test_peer"], "agent_id": worker}, "unrelated peer cannot inspect worker")
        extra_checkpoint = self.request("checkpoint", worker, checkpoint={}, summary="strict fields", undeclared=True)
        self.reject(extra_checkpoint, "extra mutation field rejected", "INVALID_REQUEST")
        stale_revision = self.request("checkpoint", worker, checkpoint={}, summary="stale revision")
        stale_revision["expected_revision"] -= 1
        self.reject(stale_revision, "stale expected revision rejected", "REVISION_CONFLICT")
        replayed_checkpoint = invoke(checkpoint_request)
        expected_checkpoint = copy.deepcopy(checkpoint_response)
        expected_checkpoint["replayed"] = True
        require(replayed_checkpoint == expected_checkpoint, "Checkpoint replay did not return original response")
        require(self.current_revision() == self.revision, "Replay changed durable revision")
        self.mark("durable mutation replay precedes stale expected_revision check")

        self.accept(self.request("pause", worker), "PAUSED")
        self.accept(self.request("checkpoint", worker, checkpoint={"secret": checkpoint_secret}, summary="paused checkpoint"), "PAUSED")
        self.mark("PAUSED permits checkpoint and preserves state")

        feedback_secret = "private-feedback-sentinel-41b2fa32"
        self.accept(self.request("wait", worker, feedback_id="worker-feedback-v1", message=feedback_secret), "WAITING_FEEDBACK")
        for forbidden_op, extras in (
            ("start", {}),
            ("pause", {}),
            ("finish", {}),
            ("checkpoint", {"checkpoint": {}, "summary": "must remain blocked"}),
        ):
            self.reject(self.request(forbidden_op, worker, **extras), "waiting rejects self " + forbidden_op)
        self.reject(self.request("reply", worker, actor_id="test_peer", feedback_id="worker-feedback-v1", response={"ready": True}), "wrong parent cannot reply")
        self.reject(self.request("reply", worker, actor_id="test_file", feedback_id="other-feedback", response={"ready": True}), "wrong feedback identity rejected")
        mismatched_reply = self.request("reply", worker, actor_id="test_file", feedback_id="worker-feedback-v1", response={"ready": True})
        mismatched_reply["context"]["contract_digest"] = "another-contract"
        self.reject(mismatched_reply, "reply context must match pending request")
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        stale_reply = self.request("reply", worker, actor_id="test_file", feedback_id="worker-feedback-v1", response={"ready": True})
        stale_reply["target_generation"] -= 1
        self.reject(stale_reply, "reply to previous target generation rejected")
        invalid_epoch = self.request("resume", worker, actor_id="test_file", recovery_generation=self.generations[worker] - 1)
        self.reject(invalid_epoch, "old recovery epoch cannot resume")
        wrong_parent = self.request("resume", worker, actor_id="test_peer", recovery_generation=self.generations[worker])
        self.reject(wrong_parent, "wrong parent cannot resume")
        self.accept(self.request("resume", worker, actor_id="test_file", recovery_generation=self.generations[worker]), "WAITING_FEEDBACK")
        self.reject(self.request("start", worker), "recovery does not erase unresolved feedback")
        self.mark("recovery preserves pending feedback and enforces fresh epoch/direct parent")

        reply_secret = "private-reply-sentinel-d273b50c"
        reply_response = self.accept(self.request("reply", worker, actor_id="test_file", feedback_id="worker-feedback-v1", response={"secret": reply_secret}), "READY")
        require(not serialized_contains(reply_response, reply_secret), "Reply result disclosed private response")
        for actor_id in (worker, "test_file"):
            history = self.history(actor_id)
            require(not serialized_contains(history, feedback_secret), "History disclosed feedback message")
            require(not serialized_contains(history, reply_secret), "History disclosed private reply")
        parent_after_reply = self.inspect(worker, actor_id="test_file")
        require(not serialized_contains(parent_after_reply, reply_secret), "Parent inspect disclosed private reply")
        self.mark("matching parent reply releases wait and private feedback data stays out of public views")
        self.accept(self.request("start", worker), "RUNNING")
        self.reject(self.request("wait", worker, feedback_id="worker-feedback-v1", message="reused feedback identity"), "completed feedback identity cannot be reused")

        self.accept(self.request("wait", worker, feedback_id="worker-feedback-during-recovery", message="recovery reply path"), "WAITING_FEEDBACK")
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        self.accept(self.request("reply", worker, actor_id="test_file", feedback_id="worker-feedback-during-recovery", response={"ready": True}), "RECOVERING")
        self.reject(self.request("start", worker), "reply during recovery still requires parent resume")
        self.accept(self.request("resume", worker, actor_id="test_file", recovery_generation=self.generations[worker]), "READY")
        self.accept(self.request("start", worker), "RUNNING")
        self.mark("reply during RECOVERING preserves mandatory parent resume")

        supervisor = "test_file"
        self.accept(self.request("wait", supervisor, feedback_id="supervisor-feedback-v1", message="supervisor awaits its parent"), "WAITING_FEEDBACK")
        waiting_supervisor = self.inspect(supervisor)["result"]["agent"]
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        self.accept(self.request("resume", worker, actor_id=supervisor, recovery_generation=self.generations[worker]), "READY")
        after_child_resume = self.inspect(supervisor)["result"]["agent"]
        for preserved_key in ("state", "generation", "pending_feedback", "checkpoint"):
            require(after_child_resume[preserved_key] == waiting_supervisor[preserved_key], "Child resume changed waiting supervisor's " + preserved_key)
        self.reject(self.request("checkpoint", supervisor, checkpoint={}, summary="blocked supervisor"), "waiting supervisor remains blocked from substantive checkpoint work")
        self.accept(self.request("start", worker), "RUNNING")
        self.accept(self.request("begin_recovery", supervisor), "RECOVERING")
        self.generations[supervisor] += 1
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        self.reject(self.request("resume", worker, actor_id=supervisor, recovery_generation=self.generations[worker]), "recovering parent cannot resume its child")
        self.accept(self.request("resume", supervisor, actor_id="test_module", recovery_generation=self.generations[supervisor]), "WAITING_FEEDBACK")
        self.accept(self.request("resume", worker, actor_id=supervisor, recovery_generation=self.generations[worker]), "READY")
        self.accept(self.request("reply", supervisor, actor_id="test_module", feedback_id="supervisor-feedback-v1", response={"ready": True}), "READY")
        self.accept(self.request("start", supervisor), "RUNNING")
        self.accept(self.request("start", worker), "RUNNING")
        self.mark("waiting parent resumes recovering child while retaining its own blocked state and pending feedback")

        operation_generation = self.generations[worker]
        operation_id = "worker-operation-v1"
        operation_secret = "private-operation-description-c901f2a7"
        operation_result = self.accept(self.request("begin_operation", worker, operation_id=operation_id, description=operation_secret), "RUNNING")
        require(not serialized_contains(operation_result, operation_secret), "Operation result disclosed private operation description")
        pending_view = self.inspect(worker)
        require(serialized_contains(pending_view["result"], operation_id), "Self inspect must retain pending operation identity")
        require(serialized_contains(pending_view["result"], "PENDING"), "Operation must initially be PENDING")
        self.reject(self.request("finish", worker), "pending operation blocks finish")
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        unknown_view = self.inspect(worker)
        require(serialized_contains(unknown_view["result"], operation_id), "Recovery lost operation identity")
        require(serialized_contains(unknown_view["result"], "UNKNOWN"), "Recovery must mark unresolved operation UNKNOWN")
        require(not serialized_contains(self.inspect(worker, actor_id="test_file"), operation_secret), "Parent inspect disclosed private operation details")
        self.accept(self.request("begin_recovery", worker), "RECOVERING")
        self.generations[worker] += 1
        repeated_recovery_view = self.inspect(worker)
        require(serialized_contains(repeated_recovery_view["result"], operation_id), "Repeated recovery lost operation identity")
        require(serialized_contains(repeated_recovery_view["result"], "UNKNOWN"), "Repeated recovery lost UNKNOWN status")
        self.mark("repeated recovery fences generation again while preserving UNKNOWN operations")
        self.accept(self.request("resume", worker, actor_id="test_file", recovery_generation=self.generations[worker]), "READY")
        self.accept(self.request("start", worker), "RUNNING")
        self.reject(self.request("finish", worker), "unknown operation blocks finish after recovery")
        self.reject(self.request("resolve_operation", worker, operation_id=operation_id, operation_generation=self.generations[worker], outcome="SUCCEEDED", evidence="scenario evidence"), "resolution must match operation's original generation")
        self.reject(self.request("resolve_operation", worker, operation_id=operation_id, operation_generation=operation_generation, outcome="SUCCEEDED", evidence=""), "operation resolution requires nonempty evidence")
        self.accept(self.request("resolve_operation", worker, operation_id=operation_id, operation_generation=operation_generation, outcome="SUCCEEDED", evidence="scenario evidence supplied by caller"), "RUNNING")
        resolved_view = self.inspect(worker)
        require(operation_id not in resolved_view["result"]["agent"]["pending_operations"], "Resolved operation remains pending")
        require(serialized_contains(resolved_view["result"]["agent"]["operation_resolutions"], "scenario evidence supplied by caller"), "Resolution evidence was not retained privately")
        require(not serialized_contains(self.history(worker), operation_secret), "History disclosed private operation details")
        self.mark("pending operation becomes UNKNOWN on recovery and requires original epoch plus caller evidence to resolve")

        contenders = [
            self.request("checkpoint", worker, checkpoint={"contender": contender}, summary="concurrent contender " + str(contender))
            for contender in (1, 2)
        ]
        before_race = self.revision
        with ThreadPoolExecutor(max_workers=2) as executor:
            responses = list(executor.map(invoke, contenders))
        winners = [response for response in responses if response["ok"]]
        losers = [response for response in responses if not response["ok"]]
        require(len(winners) == len(losers) == 1, "Concurrent writers must have exactly one winner")
        require(winners[0]["revision"] == before_race + 1, "Concurrent winner revision incorrect")
        require(losers[0]["error"]["code"] == "REVISION_CONFLICT", "Concurrent loser must report revision conflict")
        self.revision = before_race + 1
        require(self.current_revision() == self.revision, "Concurrent mutation did not commit exactly once")
        self.mark("concurrent independent processes serialize one winner and one revision conflict")

        self.accept(self.request("finish", worker), "FINISHED")
        self.reject(self.request("start", worker), "finished node cannot restart directly")
        self.mark("finish commits only from RUNNING and is durable across process reopen")
        for finishing_agent in ("test_file", "test_module", "test_domain", "test_peer", "test_root"):
            self.accept(self.request("finish", finishing_agent), "FINISHED")
        self.mark("all supervisors finish successfully after direct children finish bottom-up")
        root_history = self.history("test_root")
        require(not serialized_contains(root_history["result"], checkpoint_secret), "Root history disclosed checkpoint")
        require(not serialized_contains(root_history["result"], reply_secret), "Root history disclosed private reply")
        allowed_scopes = {
            "test_root": {"test_root", "test_domain", "test_peer"},
            "test_file": {"test_file", "test_worker"},
            "test_worker": {"test_worker"},
        }
        for actor_id, visible_agents in allowed_scopes.items():
            scoped_history = self.history(actor_id)
            events = scoped_history["result"]["events"]
            revisions = [entry["revision"] for entry in events]
            require(revisions == sorted(set(revisions)), "History must be ordered without duplicate revisions")
            for entry in events:
                require(set(entry) == {"revision", "request_id", "event"}, "Unexpected history envelope fields")
                require(entry["event"]["agent_id"] in visible_agents, "History disclosed events outside direct scope")
                operation = entry["event"]["op"]
                permitted_extras = {
                    "wait": {"feedback_id"},
                    "reply": {"feedback_id"},
                    "begin_operation": {"operation_id", "status"},
                    "resolve_operation": {"operation_id", "outcome"},
                }.get(operation, set())
                require(set(entry["event"]) == {"op", "agent_id", "actor_id", "state", "generation", "summary"} | permitted_extras, "Public history event has unexpected fields for " + operation)
                if operation == "begin_operation":
                    require(entry["event"]["status"] == "PENDING", "Begin-operation event must record PENDING")
            if revisions:
                watermark = revisions[len(revisions) // 2]
                later = self.history(actor_id, after_revision=watermark)["result"]["events"]
                require(later == [entry for entry in events if entry["revision"] > watermark], "History watermark filter mismatch")
        user_history = invoke({"op": "history", "actor_id": "@user", "generation": 0, "after_revision": 0})
        require(user_history["ok"], "User history failed")
        require(all(entry["event"]["agent_id"] == "test_root" for entry in user_history["result"]["events"]), "User history must be restricted to root events")
        self.mark("history is ordered, filtered by revision, limited to self/direct children, and exposes only public event fields")
        empty_history = self.history("test_root", after_revision=self.revision)
        require(not serialized_contains(empty_history["result"], '"op"'), "History after current revision should contain no events")
        self.mark("history watermark returns no new events at current revision")


def main() -> int:
    if sys.argv[1:] == ["--fixture"]:
        print(json.dumps(init_request(), ensure_ascii=False))
        return 0
    if sys.argv[1:]:
        print(json.dumps({"ok": False, "error": "Only --fixture or no arguments are supported"}))
        return 2
    harness = Harness()
    try:
        harness.run()
    except Exception as error:
        message = str(error) if isinstance(error, ScenarioFailure) else "Harness or response shape failure: " + type(error).__name__
        print(json.dumps({"ok": False, "passed_count": len(harness.passed), "passed": harness.passed, "failure": message, "revision": harness.revision}, ensure_ascii=False))
        return 1
    print(json.dumps({"ok": True, "passed_count": len(harness.passed), "passed": harness.passed, "revision": harness.revision, "database": str(DATABASE)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
