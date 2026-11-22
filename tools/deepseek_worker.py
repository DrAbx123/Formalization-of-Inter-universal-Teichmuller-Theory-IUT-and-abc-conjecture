"""Bounded, state-bound DeepSeek candidate worker; Python standard library only."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import socket
import subprocess
import sys
import threading
import tomllib
import urllib.error
import urllib.parse
import urllib.request


SCHEMA = "deepseek-worker/v1"
PROTOCOL = "iut-agent-tree/2026-10-13-v1"
MAX_INPUT_BYTES = 32768
MAX_RESPONSE_BYTES = 65536
_dispatch_lock = threading.Lock()
_network_in_flight = threading.Event()


class WorkerError(Exception):
    def __init__(self, code: str, status: str = "rejected"):
        self.code = code
        self.status = status
        super().__init__(code)


def _strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise WorkerError("DUPLICATE_JSON_KEY")
        result[key] = value
    return result


def _parse_json(value):
    try:
        return json.loads(value, object_pairs_hook=_strict_object,
                          parse_constant=lambda _: (_ for _ in ()).throw(
                              WorkerError("INVALID_JSON")))
    except (ValueError, UnicodeError, RecursionError):
        raise WorkerError("INVALID_JSON") from None


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def task_packet_digest(packet):
    """Public canonical digest convention used by the registered contract."""
    return hashlib.sha256(_canonical({name: packet[name] for name in
                                     ("selection", "task", "budget")})).hexdigest()


def _keys(value, required, optional=()):
    if not isinstance(value, dict) or set(value) - set(required) - set(optional):
        raise WorkerError("INVALID_FIELDS")
    if not set(required).issubset(value):
        raise WorkerError("MISSING_FIELDS")


def _text(value, limit=256, identifier=False):
    if not isinstance(value, str) or not value.strip() or len(value) > limit:
        raise WorkerError("INVALID_TEXT")
    if any(ord(char) < 32 and char not in "\n\t" for char in value):
        raise WorkerError("INVALID_TEXT")
    if identifier and not re.fullmatch(r"[A-Za-z0-9_.:@/-]+", value):
        raise WorkerError("INVALID_IDENTIFIER")
    return value


def _prose(value, limit):
    _text(value, limit)
    if re.search(r"```|(?m:^\s*(?:import|from|def|class|theorem|lemma|axiom|namespace|#include)\s)|(?:file|https?)://", value):
        raise WorkerError("SOURCE_PAYLOAD_NOT_ALLOWED")
    return value


def _number(value, low, high):
    if isinstance(value, bool) or not isinstance(value, int) or not low <= value <= high:
        raise WorkerError("INVALID_BUDGET")
    return value


def _absolute(value):
    _text(value, 2048)
    if not Path(value).is_absolute():
        raise WorkerError("ABSOLUTE_PATH_REQUIRED")
    return value


def _endpoint(base_url):
    _text(base_url, 2048)
    try:
        parsed = urllib.parse.urlsplit(base_url)
        if (parsed.scheme != "https" or not parsed.hostname or parsed.username
                or parsed.password or parsed.query or parsed.fragment
                or parsed.port not in (None, 443)):
            raise WorkerError("INVALID_ENDPOINT")
    except ValueError:
        raise WorkerError("INVALID_ENDPOINT") from None
    return base_url.rstrip("/")


def _environment_name(value):
    _text(value, 128)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise WorkerError("INVALID_AUTH_SOURCE")
    return value


def _load_selection(selection, credentials):
    if not isinstance(selection, dict):
        raise WorkerError("INVALID_SELECTION")
    mode = selection.get("mode")
    headers = {}
    secret_values = []
    secret_env_names = []
    auth_fields = []
    if mode == "direct":
        _keys(selection, ("mode", "provider", "base_url", "model", "wire_api", "api_key_env"))
        if selection["provider"] != "deepseek":
            raise WorkerError("UNSUPPORTED_PROVIDER", "needs_feedback")
        if selection["base_url"].rstrip("/") not in (
                "https://api.deepseek.com", "https://api.deepseek.com/v1"):
            raise WorkerError("UNSUPPORTED_DIRECT_ENDPOINT", "needs_feedback")
        provider_data = {"base_url": selection["base_url"],
                         "wire_api": selection["wire_api"],
                         "env_key": selection["api_key_env"]}
    elif mode == "config":
        _keys(selection, ("mode", "config", "provider", "model"), ("profile",))
        _absolute(selection["config"])
        try:
            with open(selection["config"], "rb") as stream:
                config = tomllib.load(stream)
        except (OSError, ValueError):
            raise WorkerError("CONFIG_UNAVAILABLE", "needs_feedback") from None
        provider_data = config.get("model_providers", {}).get(selection["provider"])
        if not isinstance(provider_data, dict):
            raise WorkerError("PROVIDER_UNAVAILABLE", "needs_feedback")
        if "profile" in selection:
            profile = config.get("profiles", {}).get(selection["profile"])
            if not isinstance(profile, dict):
                raise WorkerError("PROFILE_UNAVAILABLE", "needs_feedback")
            if profile.get("model_provider") != selection["provider"] or profile.get("model") != selection["model"]:
                raise WorkerError("PROFILE_SELECTION_MISMATCH", "needs_feedback")
        # Recognized query configuration cannot silently disappear from a request.
        if provider_data.get("query_params"):
            raise WorkerError("QUERY_PARAMS_UNSUPPORTED", "needs_feedback")
    else:
        raise WorkerError("INVALID_SELECTION")
    provider = _text(selection["provider"], 128, True)
    model = _text(selection["model"], 128, True)
    if "deepseek" not in model.lower():
        raise WorkerError("DEEPSEEK_MODEL_REQUIRED", "needs_feedback")
    base_url = _endpoint(provider_data.get("base_url"))
    wire_api = provider_data.get("wire_api")
    if wire_api == "chat":
        wire_api = "chat_completions"
    if wire_api not in ("chat_completions", "responses"):
        raise WorkerError("WIRE_API_UNSUPPORTED", "needs_feedback")
    if wire_api == "responses":
        raise WorkerError("RESPONSES_UNSUPPORTED", "needs_feedback")
    for field in ("env_key", "experimental_bearer_token", "http_headers", "env_http_headers", "requires_openai_auth"):
        if field in provider_data:
            auth_fields.append(field)

    def add_header(name, value):
        if not isinstance(name, str) or not re.fullmatch(r"[!#$%&'*+.^_`|~0-9A-Za-z-]+", name):
            raise WorkerError("INVALID_AUTH_HEADER")
        if name.lower() in ("host", "content-length", "transfer-encoding", "connection", "content-type"):
            raise WorkerError("RESERVED_HEADER")
        if not isinstance(value, str) or not value or "\r" in value or "\n" in value:
            raise WorkerError("INVALID_AUTH_HEADER")
        if name.lower() in {existing.lower() for existing in headers}:
            raise WorkerError("DUPLICATE_AUTH_HEADER")
        headers[name] = value
        secret_values.append(value)
        if value.lower().startswith("bearer "):
            secret_values.append(value[7:])

    def get_env(name):
        name = _environment_name(name)
        secret_env_names.append(name)
        if not credentials:
            return "inspection-placeholder"
        value = os.environ.get(name)
        if not value:
            raise WorkerError("AUTH_ENV_MISSING", "needs_feedback")
        return value

    if provider_data.get("env_key") is not None:
        add_header("Authorization", "Bearer " + get_env(provider_data["env_key"]))
    if provider_data.get("experimental_bearer_token") is not None:
        bearer = provider_data["experimental_bearer_token"]
        if not isinstance(bearer, str):
            raise WorkerError("INVALID_AUTH_SOURCE")
        add_header("Authorization", "Bearer " + bearer)
    for field in ("http_headers", "env_http_headers"):
        configured = provider_data.get(field, {})
        if not isinstance(configured, dict):
            raise WorkerError("INVALID_AUTH_SOURCE")
        for name, value in configured.items():
            add_header(name, get_env(value) if field == "env_http_headers" else value)
    if not headers:
        raise WorkerError("AUTH_SOURCE_REQUIRED", "needs_feedback")
    return {"provider": provider, "model": model, "base_url": base_url,
            "wire_api": wire_api, "auth_fields": auth_fields, "headers": headers,
            "secret_values": secret_values, "secret_env_names": secret_env_names}


def inspect_config(selection):
    """Return sanitized metadata without reading credential environment values."""
    try:
        selected = _load_selection(selection, False)
        return {"schema": SCHEMA, "status": "candidate", "selection": {
            key: selected[key] for key in ("provider", "model", "base_url", "wire_api", "auth_fields")}}
    except WorkerError as error:
        return {"schema": SCHEMA, "status": error.status, "code": error.code}
    except Exception:
        return {"schema": SCHEMA, "status": "rejected", "code": "CONFIG_INVALID"}


def _validate_packet(packet):
    _keys(packet, ("schema", "request_id", "state", "selection", "task", "budget"))
    if packet["schema"] != SCHEMA or len(_canonical(packet)) > MAX_INPUT_BYTES:
        raise WorkerError("INVALID_PACKET")
    _text(packet["request_id"], 64, True)
    state = packet["state"]
    _keys(state, ("db", "agent_id", "generation", "expected_revision", "run_id", "protocol_version", "contract_digest"))
    _absolute(state["db"])
    for field in ("agent_id", "run_id"):
        _text(state[field], 128, True)
    _number(state["generation"], 1, 2**53)
    _number(state["expected_revision"], 0, 2**53)
    if state["protocol_version"] != PROTOCOL or not re.fullmatch(r"[a-f0-9]{64}", str(state["contract_digest"])):
        raise WorkerError("INVALID_STATE_CONTEXT")
    budget = packet["budget"]
    _keys(budget, ("max_output_tokens", "timeout_seconds"))
    _number(budget["max_output_tokens"], 1, 1024)
    _number(budget["timeout_seconds"], 1, 60)
    task = packet["task"]
    _keys(task, ("kind", "question", "dependencies", "required_dependencies"))
    if task["kind"] not in ("dependency_graph", "bounded_text"):
        raise WorkerError("UNSUPPORTED_TASK")
    _prose(task["question"], 2000)
    if not isinstance(task["dependencies"], list) or len(task["dependencies"]) > 32:
        raise WorkerError("INVALID_DEPENDENCIES")
    names = set()
    for dependency in task["dependencies"]:
        _keys(dependency, ("name", "statement", "status", "version"))
        name = _text(dependency["name"], 64, True)
        if name in names or dependency["status"] not in ("established", "missing"):
            raise WorkerError("INVALID_DEPENDENCIES")
        names.add(name)
        _text(dependency["version"], 64, True)
        _prose(dependency["statement"], 2000)
    required = task["required_dependencies"]
    if not isinstance(required, list) or len(required) > 32:
        raise WorkerError("INVALID_DEPENDENCIES")
    for name in required:
        _text(name, 64, True)
    if len(set(required)) != len(required):
        raise WorkerError("INVALID_DEPENDENCIES")


class StateBridge:
    def __init__(self, packet, secret_env_names):
        self.packet = packet
        self.state = packet["state"]
        self.revision = self.state["expected_revision"]
        self.generation = self.state["generation"]
        self.secret_env_names = secret_env_names

    def call(self, operation, **extras):
        state = self.state
        command = {"op": operation, "actor_id": state["agent_id"],
                   "agent_id": state["agent_id"], "generation": self.generation}
        if operation != "inspect":
            command.update(request_id=self.packet["request_id"] + ":" + operation,
                           expected_revision=self.revision,
                           context={name: state[name] for name in
                                    ("run_id", "protocol_version", "contract_digest")})
        command.update(extras)
        child_env = os.environ.copy()
        for name in self.secret_env_names:
            child_env.pop(name, None)
        try:
            completed = subprocess.run(
                [sys.executable, "-B", str(Path(__file__).with_name("agent_state.py")),
                 "--db", state["db"]], input=_canonical(command),
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15,
                env=child_env, check=False)
            response = _parse_json(completed.stdout)
        except Exception:
            raise WorkerError("STATE_UNAVAILABLE", "needs_feedback") from None
        if not isinstance(response, dict) or response.get("ok") is not True:
            code = response.get("error", {}).get("code") if isinstance(response, dict) else None
            allowed = {"REVISION_CONFLICT", "REQUEST_CONFLICT", "STALE_GENERATION",
                       "GENERATION_MISMATCH", "CONTEXT_MISMATCH"}
            raise WorkerError("STATE_" + code if code in allowed else "STATE_REJECTED", "needs_feedback")
        if not isinstance(response.get("revision"), int):
            raise WorkerError("STATE_INVALID", "needs_feedback")
        self.revision = response["revision"]
        return response

    def verify(self, selected):
        expected_revision = self.revision
        response = self.call("inspect")
        if self.revision != expected_revision:
            raise WorkerError("STATE_REVISION_CONFLICT", "needs_feedback")
        result = response.get("result", {})
        agent = result.get("agent", {})
        if (result.get("run_id") != self.state["run_id"] or
                result.get("protocol_version") != PROTOCOL or
                agent.get("generation") != self.generation or agent.get("state") != "RUNNING" or
                agent.get("contract_digest") != self.state["contract_digest"]):
            raise WorkerError("STATE_CONTEXT_MISMATCH", "needs_feedback")
        if agent.get("provider") != selected["provider"] or agent.get("model") != selected["model"]:
            raise WorkerError("STATE_SELECTION_MISMATCH", "needs_feedback")
        assumptions = agent.get("contract", {}).get("assumptions", [])
        hashes = [entry for entry in assumptions if isinstance(entry, str)
                  and entry.startswith("task_packet_sha256=")]
        if hashes != ["task_packet_sha256=" + task_packet_digest(self.packet)]:
            raise WorkerError("TASK_CONTRACT_MISMATCH", "needs_feedback")
        if agent.get("pending_operations"):
            raise WorkerError("PENDING_OPERATION", "needs_feedback")
        if self.packet["request_id"] in agent.get("operation_resolutions", {}):
            raise WorkerError("ALREADY_EXECUTED", "needs_feedback")

    def receipt(self, receipt, succeeded):
        self.call("checkpoint", checkpoint={"worker_schema": SCHEMA,
                  "request_id": self.packet["request_id"], "receipt": receipt},
                  summary="Bounded worker response receipt recorded before resolution.")
        self.call("resolve_operation", operation_id=self.packet["request_id"],
                  operation_generation=self.generation,
                  outcome="SUCCEEDED" if succeeded else "FAILED",
                  evidence="Receipt stored in checkpoint for " + self.packet["request_id"])

    def unknown(self):
        try:
            self.call("begin_recovery")
            self.generation += 1
        except WorkerError:
            pass  # Unresolved PENDING also blocks redispatch if durable recovery failed.

    def snapshot(self):
        return {"revision": self.revision, "generation": self.generation}


class _RefuseRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, file_pointer, code, message, headers, new_url):
        return None


def _open_request(request, timeout):
    """Transport seam for independent fabricated-response tests."""
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), _RefuseRedirect())
    return opener.open(request, timeout=timeout)


def _candidate_payload(envelope, task, secret_values):
    if not isinstance(envelope, dict) or not isinstance(envelope.get("choices"), list) or len(envelope["choices"]) != 1:
        raise WorkerError("INVALID_REMOTE_RESPONSE")
    choice = envelope["choices"][0]
    if not isinstance(choice, dict) or choice.get("finish_reason") != "stop":
        raise WorkerError("INCOMPLETE_REMOTE_RESPONSE")
    message = choice.get("message")
    if not isinstance(message, dict) or message.get("role") != "assistant" or "tool_calls" in message or "function_call" in message:
        raise WorkerError("REMOTE_TOOL_CALL_REJECTED")
    content = message.get("content")
    if not isinstance(content, str):
        raise WorkerError("INVALID_REMOTE_RESPONSE")
    if any(secret and secret in content for secret in secret_values):
        raise WorkerError("REMOTE_SECRET_REFLECTION")
    result = _parse_json(content)
    if not isinstance(result, dict):
        raise WorkerError("INVALID_REMOTE_PAYLOAD")
    status = result.get("status")
    if status == "candidate":
        _keys(result, ("status", "answer", "used_dependencies"))
        _prose(result["answer"], 8000)
        names = result["used_dependencies"]
        established = {dependency["name"] for dependency in task["dependencies"]
                       if dependency["status"] == "established"}
        if not isinstance(names, list) or any(not isinstance(name, str) or name not in established for name in names) or len(set(names)) != len(names):
            raise WorkerError("UNREGISTERED_REMOTE_DEPENDENCY")
        return {"status": "candidate", "candidate": {"answer": result["answer"], "used_dependencies": names}}
    if status == "needs_feedback":
        _keys(result, ("status", "reason", "missing_dependencies"))
        _prose(result["reason"], 2000)
        names = result["missing_dependencies"]
        if not isinstance(names, list) or len(names) > 32:
            raise WorkerError("INVALID_REMOTE_PAYLOAD")
        for name in names:
            _text(name, 64, True)
        return {"status": "needs_feedback", "code": "REMOTE_NEEDS_FEEDBACK",
                "feedback": {"reason": result["reason"], "missing_dependencies": names}}
    raise WorkerError("INVALID_REMOTE_PAYLOAD")


def _dispatch(packet, selected):
    task = packet["task"]
    body = {"model": selected["model"], "messages": [
        {"role": "system", "content": (
            "Answer only the exact registered bounded text question using its supplied dependencies. "
            "Established means a caller assumption, "
            "not a Lean proof. Do not invent missing premises. Return one JSON object only: "
            '{"status":"candidate","answer":"plain prose","used_dependencies":["registered name"]} '
            "or "
            '{"status":"needs_feedback","reason":"plain prose","missing_dependencies":["name"]}. '
            "No tools, source code, markdown fences, or unregistered dependency claims.")},
        {"role": "user", "content": _canonical(task).decode("utf-8")}],
        "max_tokens": packet["budget"]["max_output_tokens"], "stream": False,
        "response_format": {"type": "json_object"}}
    if selected["provider"] == "deepseek":
        body["thinking"] = {"type": "disabled"}
    request = urllib.request.Request(selected["base_url"] + "/chat/completions",
                                     data=_canonical(body), method="POST",
                                     headers={"Content-Type": "application/json", **selected["headers"]})
    with _open_request(request, packet["budget"]["timeout_seconds"]) as response:
        if response.status != 200:
            raise WorkerError("HTTP_RESPONSE_REJECTED")
        if "application/json" not in response.headers.get("Content-Type", "").lower():
            raise WorkerError("REMOTE_CONTENT_TYPE_REJECTED")
        raw = response.read(MAX_RESPONSE_BYTES + 1)
    if len(raw) > MAX_RESPONSE_BYTES:
        raise WorkerError("REMOTE_RESPONSE_TOO_LARGE")
    return _candidate_payload(_parse_json(raw), task, selected["secret_values"])


def _dispatch_with_deadline(packet, selected):
    """Bound caller network wait, including slow reads, by one total deadline.

    A timed-out daemon can still be finishing an HTTP operation. Its outcome is
    UNKNOWN; another in-process request is refused until that thread exits.
    The one-shot CLI exits after recording UNKNOWN, terminating daemon activity.
    """
    result_queue = queue.Queue(maxsize=1)
    _network_in_flight.set()

    def run_request():
        try:
            result_queue.put((True, _dispatch(packet, selected)))
        except Exception as error:
            result_queue.put((False, error))
        finally:
            _network_in_flight.clear()

    threading.Thread(target=run_request, daemon=True, name="deepseek-bounded-request").start()
    try:
        succeeded, value = result_queue.get(timeout=packet["budget"]["timeout_seconds"])
    except queue.Empty:
        raise TimeoutError from None
    if not succeeded:
        raise value
    return value


def execute(packet):
    """Validate and dispatch at most one state-bound request; never retry."""
    request_id = packet.get("request_id") if isinstance(packet, dict) else None
    if not isinstance(request_id, str) or not re.fullmatch(r"[A-Za-z0-9_.:@/-]{1,64}", request_id):
        request_id = None
    output = {"schema": SCHEMA, "request_id": request_id}
    bridge = None
    began = False
    if not _dispatch_lock.acquire(blocking=False):
        return {**output, "status": "needs_feedback", "code": "WORKER_BUSY"}
    try:
        if _network_in_flight.is_set():
            raise WorkerError("WORKER_BUSY", "needs_feedback")
        _validate_packet(packet)
        selected = _load_selection(packet["selection"], True)
        bridge = StateBridge(packet, selected["secret_env_names"])
        bridge.verify(selected)
        established = {dependency["name"] for dependency in packet["task"]["dependencies"]
                       if dependency["status"] == "established"}
        missing = [name for name in packet["task"]["required_dependencies"] if name not in established]
        if missing:
            return {**output, "status": "needs_feedback", "code": "MISSING_DEPENDENCY",
                    "missing_dependencies": missing, "state": bridge.snapshot()}
        bridge.call("begin_operation", operation_id=request_id,
                    description="One bounded DeepSeek dependency review; no automatic retries.")
        began = True
        try:
            result = _dispatch_with_deadline(packet, selected)
        except urllib.error.HTTPError as error:
            error.close()
            result = {"status": "rejected", "code": "HTTP_RESPONSE_REJECTED"}
        except WorkerError as error:
            result = {"status": "rejected", "code": error.code}
        except (TimeoutError, socket.timeout, urllib.error.URLError, OSError):
            bridge.unknown()
            return {**output, "status": "unknown", "code": "NETWORK_OUTCOME_UNKNOWN",
                    "state": bridge.snapshot()}
        bridge.receipt(result, result["status"] in ("candidate", "needs_feedback"))
        began = False
        return {**output, **result, "state": bridge.snapshot()}
    except WorkerError as error:
        if began and bridge is not None:
            bridge.unknown()
            return {**output, "status": "unknown", "code": "STATE_RECEIPT_UNKNOWN",
                    "state": bridge.snapshot()}
        return {**output, "status": error.status, "code": error.code,
                **({"state": bridge.snapshot()} if bridge else {})}
    except Exception:
        if began and bridge is not None:
            bridge.unknown()
        return {**output, "status": "unknown" if began else "rejected",
                "code": "WORKER_INTERNAL_ERROR",
                **({"state": bridge.snapshot()} if bridge else {})}
    finally:
        _dispatch_lock.release()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("execute")
    inspect = commands.add_parser("inspect-config")
    inspect.add_argument("--config", required=True)
    inspect.add_argument("--provider", required=True)
    inspect.add_argument("--model", required=True)
    inspect.add_argument("--profile")
    args = parser.parse_args()
    if args.command == "inspect-config":
        selection = {"mode": "config", "config": args.config,
                     "provider": args.provider, "model": args.model}
        if args.profile:
            selection["profile"] = args.profile
        result = inspect_config(selection)
    else:
        try:
            raw = sys.stdin.buffer.read(MAX_INPUT_BYTES + 1)
            if len(raw) > MAX_INPUT_BYTES:
                raise WorkerError("PACKET_TOO_LARGE")
            result = execute(_parse_json(raw))
        except WorkerError as error:
            result = {"schema": SCHEMA, "request_id": None,
                      "status": error.status, "code": error.code}
        except Exception:
            result = {"schema": SCHEMA, "request_id": None,
                      "status": "rejected", "code": "INVALID_PACKET"}
    print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))
    return 0 if result["status"] == "candidate" else 2


if __name__ == "__main__":
    raise SystemExit(main())
