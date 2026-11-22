"""Bounded, role-preserving recovery handshakes over the existing state CLI."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time


SCHEMA = "agent-bootstrap/v1"
PROTOCOL = "iut-agent-tree/2026-10-13-v1"
IDENTIFIER = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:/-]{0,127}\Z")
CONTEXT_FIELDS = {"run_id", "protocol_version", "contract_digest"}
EXIT_CODES = {"ready": 0, "rejected": 1, "blocked": 2, "timeout": 2, "unknown": 3}


class StopBootstrap(Exception):
    def __init__(self, status: str, code: str):
        self.status, self.code = status, code


class UncertainService(Exception):
    pass


def require(condition: bool, code: str = "INVALID_REQUEST") -> None:
    if not condition:
        raise StopBootstrap("rejected", code)


def exact(value: object, names: set[str]) -> None:
    require(isinstance(value, dict) and set(value) == names)


def valid_id(value: object, *, maximum: int = 128) -> bool:
    return isinstance(value, str) and len(value) <= maximum and bool(IDENTIFIER.fullmatch(value))


def valid_integer(value: object, low: int, high: int | None = None) -> bool:
    return type(value) is int and value >= low and (high is None or value <= high)


def canonical(value: object) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"), allow_nan=False)


def parse_input(raw: bytes) -> dict:
    def unique_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result)
            result[key] = value
        return result

    def reject_constant(value):
        raise StopBootstrap("rejected", "INVALID_REQUEST")

    try:
        require(len(raw) <= 1024 * 1024, "INPUT_TOO_LARGE")
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_pairs, parse_constant=reject_constant)
        require(isinstance(value, dict))
        return value
    except (UnicodeError, ValueError, RecursionError):
        raise StopBootstrap("rejected", "INVALID_JSON") from None


def validate_context(context: dict) -> None:
    exact(context, CONTEXT_FIELDS)
    require(valid_id(context["run_id"]))
    require(context["protocol_version"] == PROTOCOL, "PROTOCOL_MISMATCH")
    digest = context["contract_digest"]
    require(isinstance(digest, str) and bool(re.fullmatch("[0-9a-f]{64}", digest)))


def validate_request(packet: dict) -> tuple[str, list[str]]:
    common = {"schema", "mode", "ticket", "actor_id", "context", "limits", "continuation"}
    require(packet.get("mode") in {"child", "parent"})
    mode = packet["mode"]
    extra = {"parent_id", "from_generation", "recovery_generation"} if mode == "child" else {"generation", "children"}
    exact(packet, common | extra)
    require(packet["schema"] == SCHEMA, "SCHEMA_MISMATCH")
    require(valid_id(packet["ticket"], maximum=64))
    require(valid_id(packet["actor_id"]))
    validate_context(packet["context"])
    exact(packet["limits"], {"timeout_seconds", "max_cas_retries"})
    require(valid_integer(packet["limits"]["timeout_seconds"], 1, 60))
    require(valid_integer(packet["limits"]["max_cas_retries"], 0, 8))
    if mode == "child":
        require(packet["parent_id"] == "@user" or valid_id(packet["parent_id"]))
        require(valid_integer(packet["from_generation"], 1))
        require(valid_integer(packet["recovery_generation"], 2))
        require(packet["recovery_generation"] == packet["from_generation"] + 1)
        steps = ["recover", "start"]
    else:
        require(valid_integer(packet["generation"], 1))
        children = packet["children"]
        require(isinstance(children, list) and 1 <= len(children) <= 64)
        child_ids = set()
        for child in children:
            exact(child, {"agent_id", "context", "recovery_generation"})
            require(valid_id(child["agent_id"]) and child["agent_id"] != packet["actor_id"])
            require(child["agent_id"] not in child_ids)
            child_ids.add(child["agent_id"])
            validate_context(child["context"])
            require(child["context"]["run_id"] == packet["context"]["run_id"], "CONTEXT_MISMATCH")
            require(valid_integer(child["recovery_generation"], 2))
        steps = [f"resume:{index}" for index in range(len(children))]
    intent = {key: value for key, value in packet.items() if key not in {"limits", "continuation"}}
    digest = hashlib.sha256(canonical(intent).encode("ascii")).hexdigest()
    handle = packet["continuation"]
    if handle is not None:
        exact(handle, {"intent_digest", "attempts", "pending"})
        require(handle["intent_digest"] == digest, "CONTINUATION_MISMATCH")
        require(isinstance(handle["attempts"], dict) and set(handle["attempts"]) == set(steps))
        require(all(valid_integer(value, 0, 9) for value in handle["attempts"].values()))
        pending = handle["pending"]
        if pending is not None:
            exact(pending, {"step", "expected_revision", "attempt"})
            require(isinstance(pending["step"], str) and pending["step"] in steps)
            require(valid_integer(pending["expected_revision"], 1))
            require(valid_integer(pending["attempt"], 0, 8))
            require(pending["attempt"] == handle["attempts"][pending["step"]])
    return digest, steps


class Bootstrap:
    def __init__(self, database: str, packet: dict, digest: str, steps: list[str]):
        self.database, self.packet = database, packet
        self.deadline = time.monotonic() + packet["limits"]["timeout_seconds"]
        self.handle = copy.deepcopy(packet["continuation"]) if packet["continuation"] is not None else {
            "intent_digest": digest, "attempts": {step: 0 for step in steps}, "pending": None,
        }
        self.observations: dict[str, dict] = {}
        self.blocked_children: list[dict] = []
        self.last_wait = None
        self.service = str(Path(__file__).with_name("agent_state.py"))

    def emit(self, status: str, code: str | None = None) -> None:
        result = {
            "schema": SCHEMA, "status": status, "mode": self.packet["mode"],
            "ticket": self.packet["ticket"], "observations": list(self.observations.values()),
            "continuation": copy.deepcopy(self.handle),
            "cas_conflicts": sum(self.handle["attempts"].values()),
            "blocked_children": list(self.blocked_children),
        }
        if code is not None:
            result["code"] = code
        print(canonical(result), flush=True)

    def remaining(self) -> float:
        return self.deadline - time.monotonic()

    def service_call(self, request: dict) -> dict:
        remaining = self.remaining()
        if remaining <= 0:
            raise UncertainService()
        try:
            completed = subprocess.run(
                [sys.executable, "-B", "-X", "utf8", self.service, "--db", self.database],
                input=canonical(request).encode("ascii"), stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=min(5.0, remaining), check=False,
            )
            response = json.loads(completed.stdout.decode("utf-8"))
            if not isinstance(response, dict) or type(response.get("ok")) is not bool:
                raise UncertainService()
            if response["ok"]:
                if completed.returncode != 0 or not valid_integer(response.get("revision"), 1):
                    raise UncertainService()
                if not isinstance(response.get("result"), dict):
                    raise UncertainService()
            elif not isinstance(response.get("error"), dict) or not isinstance(response["error"].get("code"), str):
                raise UncertainService()
            return response
        except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError):
            raise UncertainService() from None

    def inspect(self, actor_generation: int, target: str) -> dict:
        if self.remaining() <= 0:
            raise StopBootstrap("timeout", "DEADLINE")
        try:
            response = self.service_call({
                "op": "inspect", "actor_id": self.packet["actor_id"],
                "generation": actor_generation, "agent_id": target,
            })
        except UncertainService:
            if self.remaining() <= 0 and self.handle["pending"] is None:
                raise StopBootstrap("timeout", "DEADLINE") from None
            raise StopBootstrap("unknown", "SERVICE_RECEIPT_UNAVAILABLE") from None
        return response

    def require_ok(self, response: dict) -> dict:
        if not response["ok"]:
            raise StopBootstrap("blocked", response["error"]["code"])
        return response

    def observe(self, response: dict, expected_context: dict, target: str, parent: str | None = None) -> dict:
        self.require_ok(response)
        result = response["result"]
        agent = result.get("agent")
        if not isinstance(agent, dict):
            raise StopBootstrap("unknown", "INVALID_SERVICE_RECEIPT")
        if (result.get("run_id") != expected_context["run_id"]
                or result.get("protocol_version") != expected_context["protocol_version"]
                or agent.get("contract_digest") != expected_context["contract_digest"]
                or agent.get("agent_id") != target):
            raise StopBootstrap("blocked", "CONTEXT_MISMATCH")
        if parent is not None and agent.get("parent_id") != (None if parent == "@user" else parent):
            raise StopBootstrap("blocked", "WRONG_PARENT")
        self.observations[target] = {
            "agent_id": target, "parent_id": agent.get("parent_id"),
            "generation": agent.get("generation"), "state": agent.get("state"),
            "revision": response["revision"], "contract_digest": agent.get("contract_digest"),
        }
        return agent

    @staticmethod
    def require_clean(agent: dict) -> None:
        state = agent.get("state")
        if state == "FINISHED":
            raise StopBootstrap("blocked", "FINISHED")
        if agent.get("pending_feedback"):
            raise StopBootstrap("blocked", "PENDING_FEEDBACK")
        if state == "WAITING_FEEDBACK":
            raise StopBootstrap("blocked", "WAITING_FEEDBACK")
        operations = agent.get("pending_operations")
        if operations:
            entries = operations.values() if isinstance(operations, dict) else operations
            code = "UNKNOWN_OPERATION" if any(item.get("status") == "UNKNOWN" for item in entries) else "PENDING_OPERATION"
            raise StopBootstrap("blocked", code)

    def request_for(self, pending: dict) -> dict:
        step = pending["step"]
        request = {
            "request_id": f"{self.packet['ticket']}:{step}:{pending['attempt']}",
            "expected_revision": pending["expected_revision"],
            "actor_id": self.packet["actor_id"],
        }
        if self.packet["mode"] == "child":
            request.update({
                "op": "begin_recovery" if step == "recover" else "start",
                "generation": self.packet["from_generation"] if step == "recover" else self.packet["recovery_generation"],
                "agent_id": self.packet["actor_id"], "context": self.packet["context"],
            })
        else:
            child = self.packet["children"][int(step.split(":")[1])]
            request.update({
                "op": "resume", "generation": self.packet["generation"],
                "agent_id": child["agent_id"], "context": child["context"],
                "recovery_generation": child["recovery_generation"],
            })
        return request

    def reconcile_pending(self) -> dict | None:
        pending = self.handle["pending"]
        if pending is None:
            return None
        request = self.request_for(pending)
        # Reconcile only this exact state request, including its original revision.
        response = None
        for _ in range(2):
            try:
                response = self.service_call(request)
                if not response["ok"] and response["error"]["code"] in {"INTERNAL_ERROR", "STORE_IO", "STORE_BUSY"}:
                    response = None
                    raise UncertainService()
                break
            except UncertainService:
                if self.remaining() <= 0:
                    break
        if response is None:
            raise StopBootstrap("unknown", "MUTATION_RECEIPT_UNAVAILABLE")
        if response["ok"]:
            self.handle["pending"] = None
            return response
        code = response["error"]["code"]
        self.handle["pending"] = None
        if code == "REVISION_CONFLICT":
            step = pending["step"]
            self.handle["attempts"][step] += 1
            self.emit("retrying", code)
            if self.handle["attempts"][step] > self.packet["limits"]["max_cas_retries"]:
                raise StopBootstrap("blocked", "REVISION_CONFLICT")
            return None
        raise StopBootstrap("blocked", code)

    def guard_continuation(self) -> None:
        """An opaque handle is not authority to skip fresh state validation."""
        pending = self.handle["pending"]
        if pending is None:
            return
        packet = self.packet
        request = self.request_for(pending)
        response = self.inspect(request["generation"], packet["actor_id"])
        if (packet["mode"] == "child" and pending["step"] == "recover"
                and not response["ok"] and response["error"]["code"] == "STALE_GENERATION"):
            response = self.inspect(packet["recovery_generation"], packet["actor_id"])
        self.require_ok(response)
        # A past revision can only replay a cached receipt or conflict. It cannot
        # authorize a new mutation, even if the current task is now blocked.
        if response["revision"] > pending["expected_revision"]:
            return
        if response["revision"] < pending["expected_revision"]:
            raise StopBootstrap("rejected", "CONTINUATION_MISMATCH")
        own = self.observe(response, packet["context"], packet["actor_id"],
                           packet["parent_id"] if packet["mode"] == "child" else None)
        self.require_clean(own)
        if packet["mode"] == "child":
            allowed = {"NOT_READY", "PAUSED"} if pending["step"] == "recover" else {"READY"}
            if own["state"] not in allowed or own["generation"] != request["generation"]:
                raise StopBootstrap("blocked", "INVALID_STATE")
        else:
            if own["state"] not in {"READY", "RUNNING", "PAUSED"}:
                raise StopBootstrap("blocked", "PARENT_NOT_READY")
            target_index = int(pending["step"].split(":")[1])
            for index, child in enumerate(packet["children"]):
                child_response = self.inspect(packet["generation"], child["agent_id"])
                agent = self.observe(child_response, child["context"], child["agent_id"], packet["actor_id"])
                expected = child["recovery_generation"]
                if agent["generation"] not in {expected - 1, expected}:
                    raise StopBootstrap("blocked", "STALE_GENERATION")
                try:
                    self.require_clean(agent)
                except StopBootstrap as blocked:
                    if index == target_index:
                        raise
                    self.blocked_children.append({"agent_id": child["agent_id"], "code": blocked.code})
                    continue
                valid = (agent["generation"] == expected - 1 and agent["state"] in {"NOT_READY", "PAUSED"}
                         or agent["generation"] == expected and agent["state"] in {"RECOVERING", "READY", "RUNNING"})
                if not valid:
                    raise StopBootstrap("blocked", "STALE_GENERATION")
                if index == target_index and (agent["generation"] != expected or agent["state"] != "RECOVERING"):
                    raise StopBootstrap("blocked", "INVALID_STATE")

    def mutate(self, step: str, revision: int) -> dict | None:
        if self.remaining() <= 0:
            raise StopBootstrap("timeout", "DEADLINE")
        attempt = self.handle["attempts"][step]
        if attempt > self.packet["limits"]["max_cas_retries"]:
            raise StopBootstrap("blocked", "REVISION_CONFLICT")
        self.handle["pending"] = {"step": step, "expected_revision": revision, "attempt": attempt}
        # The caller can retain this public receipt even if this process is killed.
        self.emit("pending")
        return self.reconcile_pending()

    def wait(self, code: str) -> None:
        signature = (code, tuple((key, value["generation"], value["state"]) for key, value in self.observations.items()))
        if signature != self.last_wait:
            self.emit("waiting", code)
            self.last_wait = signature
        remaining = self.remaining()
        if remaining <= 0:
            raise StopBootstrap("timeout", code)
        time.sleep(min(0.1, remaining))

    def run_child(self) -> None:
        packet = self.packet
        while True:
            response = self.inspect(packet["from_generation"], packet["actor_id"])
            if not response["ok"] and response["error"]["code"] == "STALE_GENERATION":
                response = self.inspect(packet["recovery_generation"], packet["actor_id"])
            agent = self.observe(response, packet["context"], packet["actor_id"], packet["parent_id"])
            self.require_clean(agent)
            generation, state = agent["generation"], agent["state"]
            if generation == packet["from_generation"]:
                if state not in {"NOT_READY", "PAUSED"}:
                    raise StopBootstrap("blocked", "GENERATION_NOT_RECOVERED")
                changed = self.mutate("recover", response["revision"])
                if changed is not None:
                    self.observe(changed, packet["context"], packet["actor_id"], packet["parent_id"])
                continue
            if generation != packet["recovery_generation"]:
                raise StopBootstrap("blocked", "STALE_GENERATION")
            if state == "RUNNING":
                return
            if state == "READY":
                changed = self.mutate("start", response["revision"])
                if changed is not None:
                    current = self.observe(changed, packet["context"], packet["actor_id"], packet["parent_id"])
                    if current["state"] == "RUNNING":
                        return
                continue
            if state != "RECOVERING":
                raise StopBootstrap("blocked", "INVALID_STATE")
            self.wait("WAITING_PARENT")

    def run_parent(self) -> None:
        packet = self.packet
        while True:
            own_response = self.inspect(packet["generation"], packet["actor_id"])
            own = self.observe(own_response, packet["context"], packet["actor_id"])
            self.require_clean(own)
            if own["state"] not in {"READY", "RUNNING", "PAUSED"}:
                raise StopBootstrap("blocked", "PARENT_NOT_READY")
            eligible = []
            complete = True
            self.blocked_children = []
            # Validate the whole requested batch before issuing any new RESUME.
            for index, child in enumerate(packet["children"]):
                response = self.inspect(packet["generation"], child["agent_id"])
                agent = self.observe(response, child["context"], child["agent_id"], packet["actor_id"])
                generation, expected = agent["generation"], child["recovery_generation"]
                state = agent["state"]
                if generation not in {expected - 1, expected}:
                    raise StopBootstrap("blocked", "STALE_GENERATION")
                try:
                    self.require_clean(agent)
                except StopBootstrap as blocked:
                    self.blocked_children.append({"agent_id": child["agent_id"], "code": blocked.code})
                    continue
                if generation == expected - 1:
                    if state not in {"NOT_READY", "PAUSED"}:
                        raise StopBootstrap("blocked", "GENERATION_NOT_RECOVERED")
                    complete = False
                elif generation == expected:
                    if state == "RECOVERING":
                        eligible.append(index)
                        complete = False
                    elif state not in {"READY", "RUNNING"}:
                        raise StopBootstrap("blocked", "INVALID_STATE")
                else:
                    raise StopBootstrap("blocked", "STALE_GENERATION")
            if complete:
                if self.blocked_children:
                    raise StopBootstrap("blocked", "CHILDREN_BLOCKED")
                return
            if eligible:
                # Use the earliest validated snapshot: intervening parent/child
                # changes must cause CAS conflict, not bypass a clean-state check.
                index = eligible[0]
                changed = self.mutate(f"resume:{index}", own_response["revision"])
                if changed is not None:
                    child = packet["children"][index]
                    self.observe(changed, child["context"], child["agent_id"], packet["actor_id"])
                continue
            self.wait("WAITING_CHILDREN")

    def run(self) -> int:
        try:
            self.guard_continuation()
            if self.handle["pending"] is not None:
                self.emit("pending")
            self.reconcile_pending()
            if self.packet["mode"] == "child":
                self.run_child()
            else:
                self.run_parent()
            self.emit("ready")
            return 0
        except StopBootstrap as stop:
            self.emit(stop.status, stop.code)
            return EXIT_CODES[stop.status]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", required=True)
    arguments = parser.parse_args()
    runner = None
    try:
        packet = parse_input(sys.stdin.buffer.read(1024 * 1024 + 1))
        digest, steps = validate_request(packet)
        runner = Bootstrap(arguments.db, packet, digest, steps)
        return runner.run()
    except StopBootstrap as stop:
        if runner is not None:
            runner.emit(stop.status, stop.code)
        else:
            print(canonical({"schema": SCHEMA, "status": stop.status, "code": stop.code,
                             "mode": None, "ticket": None, "observations": [],
                             "continuation": None, "cas_conflicts": 0, "blocked_children": []}), flush=True)
        return EXIT_CODES[stop.status]
    except Exception:
        # No tracebacks, raw service output, private checkpoints or reply bodies.
        if runner is not None:
            runner.emit("unknown", "INTERNAL_ERROR")
        else:
            print(canonical({"schema": SCHEMA, "status": "rejected", "code": "INVALID_REQUEST",
                             "mode": None, "ticket": None, "observations": [],
                             "continuation": None, "cas_conflicts": 0, "blocked_children": []}), flush=True)
        return 3 if runner is not None else 1


if __name__ == "__main__":
    raise SystemExit(main())
