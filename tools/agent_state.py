"""Durable coordination metadata, without authentication or a file-access gateway."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import ntpath
import os
import re
import sys
from typing import Any

from agent_state_store import StoreError, history, read_state, transact


PROTOCOL_VERSION = "iut-agent-tree/2026-10-13-v1"
SCHEMA_VERSION = 1
STATES = {"NOT_READY", "RECOVERING", "READY", "RUNNING", "PAUSED", "WAITING_FEEDBACK", "FINISHED"}
ACTIVE_PARENT_STATES = {"READY", "RUNNING", "PAUSED"}
IDENTIFIER = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:/-]{0,127}\Z")
MANIFEST_FIELDS = {"agent_id", "parent_id", "role", "provider", "model", "files", "contract"}
CONTRACT_FIELDS = {"version", "target", "variables", "quantifiers", "assumptions", "conclusion", "dependencies"}
CONTEXT_FIELDS = {"run_id", "protocol_version", "contract_digest"}
COMMON_MUTATION_FIELDS = {"op", "request_id", "expected_revision", "actor_id", "generation", "agent_id", "context"}
OPERATION_FIELDS = {
    "begin_recovery": set(),
    "resume": {"recovery_generation"},
    "start": set(),
    "pause": set(),
    "finish": set(),
    "checkpoint": {"checkpoint", "summary"},
    "wait": {"feedback_id", "message"},
    "reply": {"feedback_id", "response", "target_generation"},
    "begin_operation": {"operation_id", "description"},
    "resolve_operation": {"operation_id", "operation_generation", "outcome", "evidence"},
}
NODE_FIELDS = MANIFEST_FIELDS | {
    "contract_digest", "generation", "state", "checkpoint", "summary", "pending_feedback",
    "feedback_response", "used_feedback_ids", "pending_operations", "operation_resolutions",
}


def reject(code: str, message: str) -> None:
    raise StoreError(code, message)


def exact_fields(value: Any, fields: set[str], label: str) -> None:
    if not isinstance(value, dict) or set(value) != fields:
        reject("INVALID_REQUEST", f"{label} must contain exactly: {', '.join(sorted(fields))}")


def nonempty_string(value: Any, label: str) -> None:
    if not isinstance(value, str) or not value.strip():
        reject("INVALID_REQUEST", f"{label} must be a nonempty string")


def identifier(value: Any, label: str) -> None:
    if not isinstance(value, str) or not IDENTIFIER.fullmatch(value):
        reject("INVALID_REQUEST", f"{label} must be a stable identifier of at most 128 characters")


def integer(value: Any, label: str, minimum: int = 0) -> None:
    if type(value) is not int or value < minimum:
        reject("INVALID_REQUEST", f"{label} must be an integer >= {minimum}")


def canonical_json(value: Any) -> str:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)
    except (TypeError, ValueError):
        reject("INVALID_REQUEST", "Values must be finite JSON data")


def contract_digest(contract: dict[str, Any]) -> str:
    return hashlib.sha256(canonical_json(contract).encode("utf-8")).hexdigest()


def validate_contract(contract: Any) -> None:
    exact_fields(contract, CONTRACT_FIELDS, "contract")
    for field in ("version", "target", "conclusion"):
        nonempty_string(contract[field], f"contract.{field}")
    for field in ("variables", "quantifiers", "assumptions"):
        if not isinstance(contract[field], list):
            reject("INVALID_REQUEST", f"contract.{field} must be an explicit list")
        for item in contract[field]:
            nonempty_string(item, f"contract.{field} entry")
    if not isinstance(contract["dependencies"], list):
        reject("INVALID_REQUEST", "contract.dependencies must be an explicit list")
    dependency_ids: set[str] = set()
    for dependency in contract["dependencies"]:
        exact_fields(dependency, {"dependency_id", "version", "evidence"}, "dependency")
        identifier(dependency["dependency_id"], "dependency_id")
        nonempty_string(dependency["version"], "dependency.version")
        nonempty_string(dependency["evidence"], "dependency.evidence")
        if dependency["dependency_id"] in dependency_ids:
            reject("INVALID_REQUEST", "Dependency identifiers must be unique within a contract")
        dependency_ids.add(dependency["dependency_id"])


def canonical_file(path: Any) -> tuple[str, tuple[int, int] | None]:
    nonempty_string(path, "file.path")
    if len(path) > 4096 or any(character in path for character in '*?%~\x00'):
        reject("INVALID_PATH", "File paths must be exact and cannot contain wildcard, environment, or short-name syntax")
    normalized = path.replace("/", "\\")
    drive, tail = ntpath.splitdrive(normalized)
    if not re.fullmatch(r"[A-Za-z]:", drive) or not tail.startswith("\\") or tail.endswith("\\"):
        reject("INVALID_PATH", "File paths must name an absolute drive-qualified Windows file")
    components = tail[1:].split("\\")
    reserved = re.compile(r"(?:CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(?:\..*)?\Z", re.IGNORECASE)
    if any(not component or component in {".", ".."} or component[-1] in " ." or
           ":" in component or reserved.fullmatch(component) for component in components):
        reject("INVALID_PATH", "Ambiguous, device, stream, and relative path components are not allowed")
    resolved = os.path.realpath(normalized)
    if os.path.isdir(resolved):
        reject("INVALID_PATH", "Ownership entries must name files, not existing directories")
    canonical = ntpath.normcase(ntpath.normpath(resolved))
    identity = None
    try:
        metadata = os.stat(resolved)
        if metadata.st_ino:
            identity = (metadata.st_dev, metadata.st_ino)
    except FileNotFoundError:
        pass
    except OSError:
        reject("INVALID_PATH", "File identity could not be resolved")
    return canonical, identity


def validate_tree(agents: dict[str, Any], *, normalize_paths: bool) -> None:
    if not isinstance(agents, dict) or not agents or len(agents) > 4096:
        reject("INVALID_TREE", "A tree must contain between 1 and 4096 agents")
    roots: list[str] = []
    ownership: set[str] = set()
    existing_identities: set[tuple[int, int]] = set()
    for agent_id, agent in agents.items():
        identifier(agent_id, "agent_id")
        if agent.get("agent_id") != agent_id:
            reject("INVALID_TREE", "Agent keys and stable identifiers must match")
        parent_id = agent["parent_id"]
        if parent_id is None:
            roots.append(agent_id)
        elif not isinstance(parent_id, str) or parent_id not in agents or parent_id == agent_id:
            reject("INVALID_TREE", "Each non-root agent requires a distinct existing parent")
        for field in ("role", "provider", "model"):
            nonempty_string(agent[field], field)
        validate_contract(agent["contract"])
        files = agent["files"]
        if not isinstance(files, list) or len(files) > 32:
            reject("INVALID_REQUEST", "Each allowlist must be an explicit list of at most 32 exact files")
        for entry in files:
            exact_fields(entry, {"path", "mode"}, "file")
            if entry["mode"] not in {"read", "write", "read_write", "append"}:
                reject("INVALID_REQUEST", "file.mode must be read, write, read_write, or append")
            canonical, identity = canonical_file(entry["path"])
            if canonical in ownership or identity is not None and identity in existing_identities:
                reject("OWNERSHIP_CONFLICT", "A file may be assigned only once, including read-only ownership")
            ownership.add(canonical)
            if identity is not None:
                existing_identities.add(identity)
            if normalize_paths:
                entry["path"] = canonical
            elif canonical != entry["path"]:
                reject("STATE_INCONSISTENT", "A stored file ownership path no longer resolves to its registered canonical path")
    if len(roots) != 1:
        reject("INVALID_TREE", "Exactly one root with parent_id null is required")
    root_id = roots[0]
    for agent_id in agents:
        ancestors: set[str] = set()
        cursor = agent_id
        while cursor != root_id:
            if cursor in ancestors:
                reject("INVALID_TREE", "The parent relation must be acyclic and connected")
            ancestors.add(cursor)
            parent_id = agents[cursor]["parent_id"]
            if parent_id is None:
                reject("INVALID_TREE", "Every agent must descend from the unique root")
            cursor = parent_id


def current_context(snapshot: dict[str, Any], agent: dict[str, Any]) -> dict[str, str]:
    return {"run_id": snapshot["run_id"], "protocol_version": snapshot["protocol_version"], "contract_digest": agent["contract_digest"]}


def validate_snapshot(snapshot: Any) -> None:
    exact_fields(snapshot, {"schema_version", "protocol_version", "run_id", "agents"}, "snapshot")
    if snapshot["schema_version"] != SCHEMA_VERSION or type(snapshot["schema_version"]) is not int:
        reject("SCHEMA_MISMATCH", "Unsupported coordination schema version")
    if snapshot["protocol_version"] != PROTOCOL_VERSION:
        reject("PROTOCOL_MISMATCH", "The stored protocol version does not match this executable")
    identifier(snapshot["run_id"], "run_id")
    if not isinstance(snapshot["agents"], dict):
        reject("STATE_INCONSISTENT", "Stored agents must be a mapping")
    for agent in snapshot["agents"].values():
        exact_fields(agent, NODE_FIELDS, "stored agent")
    validate_tree(snapshot["agents"], normalize_paths=False)
    for agent in snapshot["agents"].values():
        if agent["contract_digest"] != contract_digest(agent["contract"]):
            reject("STATE_INCONSISTENT", "The frozen task contract digest does not match")
        integer(agent["generation"], "stored generation", 1)
        if agent["state"] not in STATES:
            reject("STATE_INCONSISTENT", "Unknown stored agent state")
        if not isinstance(agent["checkpoint"], dict) or not isinstance(agent["summary"], str):
            reject("STATE_INCONSISTENT", "Checkpoint and public summary types are invalid")
        pending = agent["pending_feedback"]
        used_feedback_ids = agent["used_feedback_ids"]
        if not isinstance(used_feedback_ids, list) or any(not isinstance(value, str) for value in used_feedback_ids) or len(set(used_feedback_ids)) != len(used_feedback_ids):
            reject("STATE_INCONSISTENT", "Feedback identifiers must have an explicit unique history")
        for feedback_id in used_feedback_ids:
            identifier(feedback_id, "used feedback_id")
        if pending is not None:
            exact_fields(pending, {"feedback_id", "message", "context", "issued_generation"}, "pending feedback")
            identifier(pending["feedback_id"], "feedback_id")
            if pending["feedback_id"] not in used_feedback_ids:
                reject("STATE_INCONSISTENT", "Pending feedback is missing its durable identity history")
            nonempty_string(pending["message"], "feedback.message")
            integer(pending["issued_generation"], "feedback.issued_generation", 1)
            if pending["context"] != current_context(snapshot, agent) or pending["issued_generation"] > agent["generation"]:
                reject("STATE_INCONSISTENT", "Pending feedback has inconsistent task or instance context")
            if agent["state"] not in {"WAITING_FEEDBACK", "RECOVERING"}:
                reject("STATE_INCONSISTENT", "An unanswered request must retain a blocking state")
        elif agent["state"] == "WAITING_FEEDBACK":
            reject("STATE_INCONSISTENT", "WAITING_FEEDBACK requires a pending request")
        response = agent["feedback_response"]
        if response is not None:
            exact_fields(response, {"feedback_id", "response", "context", "received_generation"}, "feedback response")
            identifier(response["feedback_id"], "feedback_id")
            if response["feedback_id"] not in used_feedback_ids:
                reject("STATE_INCONSISTENT", "A feedback response requires a registered feedback identifier")
            integer(response["received_generation"], "feedback.received_generation", 1)
            if not isinstance(response["response"], dict) or response["context"] != current_context(snapshot, agent) or response["received_generation"] > agent["generation"]:
                reject("STATE_INCONSISTENT", "Stored feedback response context is invalid")
        if not isinstance(agent["pending_operations"], dict) or not isinstance(agent["operation_resolutions"], dict):
            reject("STATE_INCONSISTENT", "Operation state must be an explicit mapping")
        if set(agent["pending_operations"]) & set(agent["operation_resolutions"]):
            reject("STATE_INCONSISTENT", "An operation cannot be both pending and resolved")
        for operation_id, operation in agent["pending_operations"].items():
            exact_fields(operation, {"operation_id", "status", "generation", "context", "description"}, "pending operation")
            identifier(operation_id, "operation_id")
            nonempty_string(operation["description"], "operation.description")
            integer(operation["generation"], "operation.generation", 1)
            if operation["operation_id"] != operation_id or operation["status"] not in {"PENDING", "UNKNOWN"} or operation["context"] != current_context(snapshot, agent) or operation["generation"] > agent["generation"]:
                reject("STATE_INCONSISTENT", "Pending operation identity, context, or status is invalid")
            if operation["generation"] < agent["generation"] and operation["status"] != "UNKNOWN":
                reject("STATE_INCONSISTENT", "An operation from an earlier instance must remain UNKNOWN")
        for operation_id, resolution in agent["operation_resolutions"].items():
            exact_fields(resolution, {"operation_id", "operation_generation", "resolved_generation", "outcome", "evidence", "context"}, "operation resolution")
            identifier(operation_id, "operation_id")
            nonempty_string(resolution["evidence"], "resolution.evidence")
            integer(resolution["operation_generation"], "operation_generation", 1)
            integer(resolution["resolved_generation"], "resolved_generation", 1)
            if resolution["operation_id"] != operation_id or resolution["outcome"] not in {"SUCCEEDED", "FAILED", "CANCELLED"} or resolution["context"] != current_context(snapshot, agent) or not resolution["operation_generation"] <= resolution["resolved_generation"] <= agent["generation"]:
                reject("STATE_INCONSISTENT", "Stored operation resolution context is invalid")
        if agent["state"] == "FINISHED" and (pending is not None or agent["pending_operations"]):
            reject("STATE_INCONSISTENT", "Finished agents cannot have unresolved work")
        if agent["state"] == "FINISHED" and any(child["parent_id"] == agent["agent_id"] and child["state"] != "FINISHED" for child in snapshot["agents"].values()):
            reject("STATE_INCONSISTENT", "A finished supervisor cannot retain an unfinished child")
    canonical_json(snapshot)


def public_agent(agent: dict[str, Any]) -> dict[str, Any]:
    return {
        "agent_id": agent["agent_id"], "parent_id": agent["parent_id"], "role": agent["role"],
        "provider": agent["provider"], "model": agent["model"], "files": copy.deepcopy(agent["files"]),
        "contract_version": agent["contract"]["version"], "target": agent["contract"]["target"],
        "contract_digest": agent["contract_digest"], "generation": agent["generation"],
        "state": agent["state"], "summary": agent["summary"],
        "pending_feedback": copy.deepcopy(agent["pending_feedback"]),
        "pending_operations": [{"operation_id": operation["operation_id"], "status": operation["status"], "generation": operation["generation"]} for operation in agent["pending_operations"].values()],
    }


def root_identifier(snapshot: dict[str, Any]) -> str:
    return next(agent_id for agent_id, agent in snapshot["agents"].items() if agent["parent_id"] is None)


def get_agent(snapshot: dict[str, Any], agent_id: Any) -> dict[str, Any]:
    identifier(agent_id, "agent_id")
    if agent_id not in snapshot["agents"]:
        reject("UNKNOWN_AGENT", "The requested stable agent identifier is not registered")
    return snapshot["agents"][agent_id]


def validate_actor(snapshot: dict[str, Any], actor_id: Any, generation: Any) -> dict[str, Any] | None:
    integer(generation, "generation")
    if actor_id == "@user":
        if generation != 0:
            reject("STALE_GENERATION", "The trusted local operator uses generation zero")
        return None
    actor = get_agent(snapshot, actor_id)
    if actor["generation"] != generation:
        reject("STALE_GENERATION", "The execution instance has been fenced by a newer generation")
    return actor


def require_self(actor: dict[str, Any] | None, target: dict[str, Any]) -> None:
    if actor is None or actor["agent_id"] != target["agent_id"]:
        reject("WRONG_ACTOR", "Only the target agent may perform this transition")


def require_parent(actor: dict[str, Any] | None, target: dict[str, Any], *, recovery_control: bool = False) -> None:
    if target["parent_id"] is None:
        if actor is not None:
            reject("WRONG_PARENT", "Only @user is the registered parent of the root")
    elif actor is None or actor["agent_id"] != target["parent_id"]:
        reject("WRONG_PARENT", "Only the unique direct parent may perform this transition")
    elif actor["state"] not in ACTIVE_PARENT_STATES | ({"WAITING_FEEDBACK"} if recovery_control else set()):
        reject("PARENT_NOT_READY", "The direct parent has not reached an allowed restored state")


def require_state(target: dict[str, Any], allowed: set[str]) -> None:
    if target["state"] not in allowed:
        reject("INVALID_STATE", "This transition is not allowed from the persisted state")


def initialize_snapshot(request: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    exact_fields(request, {"op", "request_id", "expected_revision", "run_id", "protocol_version", "agents"}, "init request")
    if request["protocol_version"] != PROTOCOL_VERSION:
        reject("PROTOCOL_MISMATCH", "Initialization requires the supported explicit protocol version")
    identifier(request["run_id"], "run_id")
    if request["expected_revision"] != 0:
        reject("REVISION_CONFLICT", "Initialization requires expected_revision zero")
    if not isinstance(request["agents"], list):
        reject("INVALID_REQUEST", "agents must be an explicit list containing the entire tree")
    agents: dict[str, Any] = {}
    for supplied in request["agents"]:
        exact_fields(supplied, MANIFEST_FIELDS, "manifest agent")
        identifier(supplied["agent_id"], "agent_id")
        if supplied["agent_id"] in agents:
            reject("INVALID_TREE", "Stable agent identifiers must be unique")
        agent = copy.deepcopy(supplied)
        agent.update({
            "contract_digest": contract_digest(supplied["contract"]), "generation": 1,
            "state": "NOT_READY", "checkpoint": {}, "summary": "", "pending_feedback": None,
            "feedback_response": None, "used_feedback_ids": [], "pending_operations": {}, "operation_resolutions": {},
        })
        agents[agent["agent_id"]] = agent
    validate_tree(agents, normalize_paths=True)
    snapshot = {"schema_version": SCHEMA_VERSION, "protocol_version": PROTOCOL_VERSION, "run_id": request["run_id"], "agents": agents}
    validate_snapshot(snapshot)
    result = {"run_id": snapshot["run_id"], "protocol_version": PROTOCOL_VERSION, "agents": [public_agent(agent) for agent in agents.values()]}
    event = {"op": "init", "agent_id": root_identifier(snapshot), "actor_id": "@user", "state": "NOT_READY", "generation": 1, "summary": "Complete role tree initialized"}
    return snapshot, result, event


def mutate_snapshot(snapshot: dict[str, Any], request: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_snapshot(snapshot)
    operation_name = request["op"]
    exact_fields(request, COMMON_MUTATION_FIELDS | OPERATION_FIELDS[operation_name], f"{operation_name} request")
    actor = validate_actor(snapshot, request["actor_id"], request["generation"])
    target = get_agent(snapshot, request["agent_id"])
    exact_fields(request["context"], CONTEXT_FIELDS, "context")
    if request["context"] != current_context(snapshot, target):
        reject("CONTEXT_MISMATCH", "The run, protocol, or complete frozen task contract version does not match")
    event_extra: dict[str, Any] = {}
    if operation_name in {"resume", "reply"}:
        require_parent(actor, target, recovery_control=operation_name == "resume")
    else:
        require_self(actor, target)

    if operation_name == "begin_recovery":
        require_state(target, STATES - {"FINISHED"})
        target["generation"] += 1
        target["state"] = "RECOVERING"
        for operation in target["pending_operations"].values():
            operation["status"] = "UNKNOWN"
    elif operation_name == "resume":
        integer(request["recovery_generation"], "recovery_generation", 1)
        if request["recovery_generation"] != target["generation"]:
            reject("STALE_GENERATION", "RESUME must confirm the exact current recovery generation")
        require_state(target, {"RECOVERING"})
        target["state"] = "WAITING_FEEDBACK" if target["pending_feedback"] else "READY"
    elif operation_name == "start":
        require_state(target, {"READY"})
        target["state"] = "RUNNING"
    elif operation_name == "pause":
        require_state(target, {"RUNNING"})
        target["state"] = "PAUSED"
    elif operation_name == "finish":
        require_state(target, {"RUNNING"})
        if target["pending_feedback"] or target["pending_operations"]:
            reject("UNRESOLVED_WORK", "Pending feedback or uncertain operations must be explicitly resolved before finish")
        if any(agent["parent_id"] == target["agent_id"] and agent["state"] != "FINISHED" for agent in snapshot["agents"].values()):
            reject("UNFINISHED_CHILDREN", "A supervisor must retain its lifecycle until every direct child is FINISHED")
        target["state"] = "FINISHED"
    elif operation_name == "checkpoint":
        require_state(target, {"RUNNING", "PAUSED"})
        if not isinstance(request["checkpoint"], dict) or not isinstance(request["summary"], str):
            reject("INVALID_REQUEST", "checkpoint must be an object and summary must be a public string")
        canonical_json(request["checkpoint"])
        target["checkpoint"] = copy.deepcopy(request["checkpoint"])
        target["summary"] = request["summary"]
    elif operation_name == "wait":
        require_state(target, {"RUNNING", "PAUSED"})
        identifier(request["feedback_id"], "feedback_id")
        nonempty_string(request["message"], "message")
        if request["feedback_id"] in target["used_feedback_ids"]:
            reject("FEEDBACK_CONFLICT", "Feedback identifiers are never reused within an agent contract")
        target["used_feedback_ids"].append(request["feedback_id"])
        target["pending_feedback"] = {"feedback_id": request["feedback_id"], "message": request["message"], "context": copy.deepcopy(request["context"]), "issued_generation": target["generation"]}
        target["state"] = "WAITING_FEEDBACK"
        event_extra["feedback_id"] = request["feedback_id"]
    elif operation_name == "reply":
        integer(request["target_generation"], "target_generation", 1)
        if request["target_generation"] != target["generation"]:
            reject("STALE_GENERATION", "Feedback must address the current target generation")
        require_state(target, {"WAITING_FEEDBACK", "RECOVERING"})
        pending = target["pending_feedback"]
        if pending is None or request["feedback_id"] != pending["feedback_id"] or request["context"] != pending["context"]:
            reject("FEEDBACK_MISMATCH", "The reply must match the exact pending feedback ID and context")
        if not isinstance(request["response"], dict):
            reject("INVALID_REQUEST", "response must be an explicit object")
        canonical_json(request["response"])
        target["feedback_response"] = {"feedback_id": pending["feedback_id"], "response": copy.deepcopy(request["response"]), "context": copy.deepcopy(request["context"]), "received_generation": target["generation"]}
        target["pending_feedback"] = None
        if target["state"] == "WAITING_FEEDBACK":
            target["state"] = "READY"
        event_extra["feedback_id"] = request["feedback_id"]
    elif operation_name == "begin_operation":
        require_state(target, {"RUNNING"})
        identifier(request["operation_id"], "operation_id")
        nonempty_string(request["description"], "description")
        if request["operation_id"] in target["pending_operations"] or request["operation_id"] in target["operation_resolutions"]:
            reject("OPERATION_CONFLICT", "Operation identifiers are never reused within an agent contract")
        target["pending_operations"][request["operation_id"]] = {"operation_id": request["operation_id"], "description": request["description"], "status": "PENDING", "generation": target["generation"], "context": copy.deepcopy(request["context"])}
        event_extra.update({"operation_id": request["operation_id"], "status": "PENDING"})
    elif operation_name == "resolve_operation":
        require_state(target, {"RUNNING", "PAUSED"})
        identifier(request["operation_id"], "operation_id")
        integer(request["operation_generation"], "operation_generation", 1)
        nonempty_string(request["evidence"], "evidence")
        if request["outcome"] not in {"SUCCEEDED", "FAILED", "CANCELLED"}:
            reject("INVALID_REQUEST", "outcome must be SUCCEEDED, FAILED, or CANCELLED")
        operation = target["pending_operations"].get(request["operation_id"])
        if operation is None:
            reject("OPERATION_MISMATCH", "There is no pending operation with this identifier")
        if request["operation_generation"] != operation["generation"] or request["context"] != operation["context"]:
            reject("OPERATION_MISMATCH", "Resolution must match the original operation generation and contract")
        target["operation_resolutions"][request["operation_id"]] = {"operation_id": request["operation_id"], "operation_generation": operation["generation"], "resolved_generation": target["generation"], "outcome": request["outcome"], "evidence": request["evidence"], "context": copy.deepcopy(request["context"])}
        del target["pending_operations"][request["operation_id"]]
        event_extra.update({"operation_id": request["operation_id"], "outcome": request["outcome"]})
    validate_snapshot(snapshot)
    result = {"run_id": snapshot["run_id"], "protocol_version": snapshot["protocol_version"], "agent": public_agent(target)}
    event = {"op": operation_name, "agent_id": target["agent_id"], "actor_id": request["actor_id"], "state": target["state"], "generation": target["generation"], "summary": target["summary"], **event_extra}
    return snapshot, result, event


def read_request(database_path: str, request: dict[str, Any]) -> dict[str, Any]:
    operation_name = request["op"]
    fields = {"op", "actor_id", "generation", "agent_id"} if operation_name == "inspect" else {"op", "actor_id", "generation", "after_revision"}
    exact_fields(request, fields, f"{operation_name} request")
    revision, snapshot = read_state(database_path)
    validate_snapshot(snapshot)
    actor = validate_actor(snapshot, request["actor_id"], request["generation"])
    root_id = root_identifier(snapshot)
    if operation_name == "inspect":
        target = get_agent(snapshot, request["agent_id"])
        if actor is None:
            if target["agent_id"] != root_id:
                reject("SCOPE_DENIED", "The local operator recovery view is limited to the root public summary")
            visible = public_agent(target)
        elif actor["agent_id"] == target["agent_id"]:
            visible = copy.deepcopy(target)
        elif target["parent_id"] == actor["agent_id"]:
            visible = public_agent(target)
        else:
            reject("SCOPE_DENIED", "Agents may inspect only themselves or direct children's public summaries")
        result = {"run_id": snapshot["run_id"], "protocol_version": snapshot["protocol_version"], "agent": visible}
    else:
        integer(request["after_revision"], "after_revision")
        visible_ids = {root_id} if actor is None else {actor["agent_id"]} | {agent_id for agent_id, agent in snapshot["agents"].items() if agent["parent_id"] == actor["agent_id"]}
        records = history(database_path, request["after_revision"])
        # The bound preserves one read revision even if another process appends between these reads.
        result = {"run_id": snapshot["run_id"], "protocol_version": snapshot["protocol_version"], "events": [record for record in records if record["revision"] <= revision and record["event"].get("agent_id") in visible_ids]}
    return {"ok": True, "revision": revision, "result": result, "replayed": False}


def dispatch(database_path: str, request: Any) -> dict[str, Any]:
    if not isinstance(request, dict) or not isinstance(request.get("op"), str):
        reject("INVALID_REQUEST", "A single JSON object with an explicit op is required")
    canonical_json(request)
    operation_name = request["op"]
    if operation_name in {"inspect", "history"}:
        return read_request(database_path, request)
    if operation_name not in {"init"} | set(OPERATION_FIELDS):
        reject("INVALID_REQUEST", "Unknown operation")
    identifier(request.get("request_id"), "request_id")
    integer(request.get("expected_revision"), "expected_revision")
    if operation_name == "init":
        # Validate the complete manifest before the storage module can create a database.
        initial, result, event = initialize_snapshot(request)
        return transact(database_path, request, lambda existing, revision: (copy.deepcopy(initial), copy.deepcopy(result), copy.deepcopy(event)), initialize=True)
    exact_fields(request, COMMON_MUTATION_FIELDS | OPERATION_FIELDS[operation_name], f"{operation_name} request")
    return transact(database_path, request, lambda existing, revision: mutate_snapshot(existing, request))


def parse_json_object(raw: str) -> Any:
    def unique_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                reject("INVALID_REQUEST", "Duplicate JSON object keys are not allowed")
            result[key] = value
        return result

    def reject_constant(value: str) -> Any:
        reject("INVALID_REQUEST", "Non-finite JSON numbers are not allowed")

    try:
        return json.loads(raw, object_pairs_hook=unique_keys, parse_constant=reject_constant)
    except (json.JSONDecodeError, RecursionError):
        reject("INVALID_REQUEST", "Input must be one valid JSON object")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", required=True, help="Exact path of the coordination SQLite state database")
    arguments = parser.parse_args()
    try:
        raw = sys.stdin.read(4 * 1024 * 1024 + 1)
        if len(raw) > 4 * 1024 * 1024:
            reject("INVALID_REQUEST", "Request exceeds the four MiB input limit")
        response = dispatch(arguments.db, parse_json_object(raw))
        exit_code = 0
    except StoreError as error:
        response = {"ok": False, "error": {"code": error.code, "message": error.message}}
        exit_code = 1
    except Exception:
        # Never expose private snapshots or another file owner's source in a raw traceback.
        response = {"ok": False, "error": {"code": "INTERNAL_ERROR", "message": "The request failed closed; no successful transition is claimed"}}
        exit_code = 1
    print(json.dumps(response, ensure_ascii=True, sort_keys=True, allow_nan=False))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
