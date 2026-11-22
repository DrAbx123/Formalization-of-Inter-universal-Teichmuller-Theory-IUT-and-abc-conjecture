"""Independent blackbox checks for the frozen DeepSeek worker v1 interface.

Only the named worker/state entrypoints execute outside this test's own files.
All credentials, configuration, prompts, responses, and state are fabricated.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time
import unittest
from unittest import mock
import urllib.error


WORKER_PATH = Path(r"D:\lean\tools\deepseek_worker.py")
STATE_PATH = Path(r"D:\lean\tools\agent_state.py")
STATE_DB = Path(r"D:\lean\logs\coordination\deepseek-worker-test.sqlite")
CONFIG_PATH = Path(r"D:\lean\logs\coordination\deepseek-worker-test-config.toml")
PROTOCOL = "iut-agent-tree/2026-10-13-v1"
RUN_ID = "deepseek-worker-blackbox-fixture-v1"
FABRICATED_KEY = "fabricated-validation-key-never-valid"


def load_worker():
    sys.path.insert(0, str(WORKER_PATH.parent))
    specification = importlib.util.spec_from_file_location("deepseek_worker", WORKER_PATH)
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


class FabricatedResponse:
    def __init__(self, payload, status=200, content_type="application/json"):
        self.status = status
        self.headers = {"Content-Type": content_type}
        if isinstance(payload, bytes):
            encoded = payload
        else:
            encoded = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.stream = io.BytesIO(encoded)
        self.read_limits = []

    def __enter__(self):
        return self

    def __exit__(self, exception_type, exception, traceback):
        return False

    def read(self, maximum=-1):
        self.read_limits.append(maximum)
        if maximum < 1:
            raise AssertionError("Response reads must have a finite positive bound")
        return self.stream.read(maximum)


class ConciseTestResult(unittest.TextTestResult):
    """Never print tracebacks that could quote another owner's source."""

    def _exc_info_to_string(self, err, test):
        exception_type, exception, _ = err
        if isinstance(exception, AssertionError):
            return exception_type.__name__ + ": " + str(exception)
        return exception_type.__name__ + " (cross-owner traceback suppressed)"


class DeepSeekWorkerBlackboxTests(unittest.TestCase):
    worker = None

    @classmethod
    def setUpClass(cls):
        cls.import_network_guard = mock.patch("urllib.request.urlopen", side_effect=AssertionError("REAL_NETWORK_FORBIDDEN"))
        cls.import_opener_guard = mock.patch("urllib.request.OpenerDirector.open", side_effect=AssertionError("REAL_NETWORK_FORBIDDEN"))
        cls.import_network_guard.start()
        cls.import_opener_guard.start()
        cls.addClassCleanup(cls.import_network_guard.stop)
        cls.addClassCleanup(cls.import_opener_guard.stop)
        cls.worker = load_worker()

    def setUp(self):
        self.environment = mock.patch.dict(os.environ, {"DEEPSEEK_API_KEY": FABRICATED_KEY}, clear=True)
        self.environment.start()
        self.network_guard = mock.patch("urllib.request.urlopen", side_effect=AssertionError("REAL_NETWORK_FORBIDDEN"))
        self.network_guard.start()
        self.opener_guard = mock.patch("urllib.request.OpenerDirector.open", side_effect=AssertionError("REAL_NETWORK_FORBIDDEN"))
        self.opener_guard.start()
        self.addCleanup(self.environment.stop)
        self.addCleanup(self.network_guard.stop)
        self.addCleanup(self.opener_guard.stop)
        self.selection = {
            "mode": "direct", "provider": "deepseek", "base_url": "https://api.deepseek.com",
            "model": "deepseek-flash", "wire_api": "chat_completions", "api_key_env": "DEEPSEEK_API_KEY",
        }
        self.task = {
            "kind": "dependency_graph", "question": "Explain which established dependency supports the requested graph.",
            "dependencies": [{"name": "base_identity", "statement": "The base identity is established.", "status": "established", "version": "base-v1"}],
            "required_dependencies": ["base_identity"],
        }
        self.budget = {"max_output_tokens": 256, "timeout_seconds": 8}
        self.packet = {
            "schema": "deepseek-worker/v1", "request_id": "blackbox-operation-1",
            "state": {}, "selection": self.selection, "task": self.task, "budget": self.budget,
        }
        self.state_revision = 0
        self.digests = {}
        self.generations = {"root": 1, "worker": 1}
        self.state_request_number = 0
        self.transport_requests = []

    def state_call(self, payload):
        completed = subprocess.run(
            [sys.executable, "-B", str(STATE_PATH), "--db", str(STATE_DB)],
            input=json.dumps(payload), text=True, encoding="utf-8", capture_output=True,
            timeout=15,
        )
        try:
            response = json.loads(completed.stdout)
        except (ValueError, TypeError):
            raise AssertionError("State CLI did not return a JSON envelope") from None
        if response.get("ok") is False or completed.returncode:
            raise AssertionError("State CLI rejected fixture operation " + payload["op"] + ": " + json.dumps(response, sort_keys=True))
        self.state_revision = response["revision"]
        return response

    def state_mutation(self, operation, agent_id, actor_id=None, actor_generation=None, **extra):
        actor_id = actor_id or agent_id
        actor_generation = self.generations[actor_id] if actor_generation is None else actor_generation
        self.state_request_number += 1
        payload = {
            "op": operation, "request_id": "fixture-state-" + str(self.state_request_number),
            "expected_revision": self.state_revision, "actor_id": actor_id,
            "generation": actor_generation, "agent_id": agent_id,
            "context": {"run_id": RUN_ID, "protocol_version": PROTOCOL, "contract_digest": self.digests[agent_id]},
        }
        payload.update(extra)
        response = self.state_call(payload)
        if operation == "begin_recovery":
            self.generations[agent_id] += 1
        return response

    def initialize_state(self):
        self.state_revision = 0
        self.generations = {"root": 1, "worker": 1}
        self.state_request_number = 0
        for suffix in ("", "-journal", "-wal", "-shm"):
            owned_path = Path(str(STATE_DB) + suffix)
            if owned_path.exists():
                owned_path.unlink()
        signed_packet = {"selection": self.selection, "task": self.task, "budget": self.budget}
        packet_hash = hashlib.sha256(json.dumps(signed_packet, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()
        contract = {
            "version": "blackbox-contract-v1", "target": "Validate a dependency graph candidate",
            "variables": [], "quantifiers": [], "assumptions": ["task_packet_sha256=" + packet_hash],
            "conclusion": "Return a candidate constrained to established dependencies", "dependencies": [],
        }
        nodes = [
            {"agent_id": "root", "parent_id": None, "role": "coordinator", "provider": "openai", "model": "gpt-6", "files": [], "contract": contract},
            {"agent_id": "worker", "parent_id": "root", "role": "atomic_worker", "provider": "deepseek", "model": "deepseek-flash", "files": [], "contract": contract},
        ]
        result = self.state_call({"op": "init", "request_id": "fixture-init", "expected_revision": 0, "run_id": RUN_ID, "protocol_version": PROTOCOL, "agents": nodes})
        self.digests = {node["agent_id"]: node["contract_digest"] for node in result["result"]["agents"]}
        self.generations = {node["agent_id"]: node["generation"] for node in result["result"]["agents"]}
        for node in result["result"]["agents"]:
            self.assertEqual(node["generation"], 1)
            self.assertEqual(node["state"], "NOT_READY")
        self.state_mutation("begin_recovery", "root")
        self.state_mutation("resume", "root", actor_id="@user", actor_generation=0, recovery_generation=2)
        self.state_mutation("start", "root")
        self.state_mutation("begin_recovery", "worker")
        self.state_mutation("resume", "worker", actor_id="root", recovery_generation=2)
        self.state_mutation("start", "worker")
        self.assertEqual(self.state_revision, 7)
        self.packet["state"] = {
            "db": str(STATE_DB), "agent_id": "worker", "generation": 2,
            "expected_revision": self.state_revision, "run_id": RUN_ID,
            "protocol_version": PROTOCOL, "contract_digest": self.digests["worker"],
        }

    def inspect_worker(self):
        return self.state_call({"op": "inspect", "actor_id": "worker", "generation": self.generations["worker"], "agent_id": "worker"})["result"]

    def chat_envelope(self, content=None, **choice_changes):
        if content is None:
            content = {"status": "candidate", "answer": "The graph uses the established base identity.", "used_dependencies": ["base_identity"]}
        if not isinstance(content, str):
            content = json.dumps(content)
        choice = {"index": 0, "finish_reason": "stop", "message": {"role": "assistant", "content": content}}
        choice.update(choice_changes)
        return {"choices": [choice]}

    def execute_fake(self, response=None, exception=None):
        if response is None:
            response = FabricatedResponse(self.chat_envelope())

        def fabricated_open(request, timeout):
            self.transport_requests.append((request, timeout))
            if exception is not None:
                raise exception
            return response

        with mock.patch.object(self.worker, "_open_request", side_effect=fabricated_open):
            output = self.worker.execute(copy.deepcopy(self.packet))
        self.assertNotIn(FABRICATED_KEY, json.dumps(output))
        self.assertEqual(output.get("schema"), "deepseek-worker/v1")
        return output, response

    def test_candidate_payload_and_receipt(self):
        self.initialize_state()
        output, response = self.execute_fake()
        self.assertEqual(output["status"], "candidate")
        self.assertEqual(output["candidate"]["used_dependencies"], ["base_identity"])
        self.assertEqual(len(self.transport_requests), 1)
        request, timeout = self.transport_requests[0]
        payload = json.loads(request.data)
        self.assertEqual(request.full_url, "https://api.deepseek.com/chat/completions")
        self.assertEqual(payload["model"], "deepseek-flash")
        self.assertEqual(payload["max_tokens"], 256)
        self.assertEqual(payload["thinking"], {"type": "disabled"})
        self.assertEqual(timeout, 8)
        self.assertTrue(response.read_limits)
        observed = self.inspect_worker()
        self.assertIn("SUCCEEDED", json.dumps(observed))
        self.assertNotIn(FABRICATED_KEY, json.dumps(observed))

    def assert_no_dispatch(self, expected_status=None, expected_code=None):
        output, _ = self.execute_fake()
        self.assertEqual(len(self.transport_requests), 0)
        self.assertNotEqual(output["status"], "candidate")
        if expected_status is not None:
            self.assertEqual(output["status"], expected_status)
        if expected_code is not None:
            self.assertEqual(output.get("code"), expected_code)
        return output

    def test_missing_required_dependency_prevents_network_and_state_mutation(self):
        self.task["dependencies"][0]["status"] = "missing"
        self.initialize_state()
        self.assert_no_dispatch("needs_feedback")
        self.inspect_worker()
        self.assertEqual(self.state_revision, 7)

    def test_missing_api_key_prevents_network(self):
        self.initialize_state()
        os.environ.pop("DEEPSEEK_API_KEY")
        self.assert_no_dispatch("needs_feedback")

    def test_packet_hash_change_prevents_network(self):
        self.initialize_state()
        self.packet["task"]["question"] = "A changed unsigned task question."
        self.assert_no_dispatch()

    def test_stale_revision_prevents_network(self):
        self.initialize_state()
        self.packet["state"]["expected_revision"] = 6
        self.assert_no_dispatch()

    def test_wrong_generation_prevents_network(self):
        self.initialize_state()
        self.packet["state"]["generation"] = 1
        self.assert_no_dispatch()

    def test_wrong_run_prevents_network(self):
        self.initialize_state()
        self.packet["state"]["run_id"] = "different-fabricated-run"
        self.assert_no_dispatch()

    def test_wrong_contract_digest_prevents_network(self):
        self.initialize_state()
        self.packet["state"]["contract_digest"] = "0" * 64
        self.assert_no_dispatch()

    def test_provider_model_mismatch_prevents_network(self):
        self.selection["model"] = "different-fabricated-model"
        self.initialize_state()
        self.assert_no_dispatch()

    def test_unknown_packet_fields_prevent_network(self):
        for forbidden_field in ("messages", "source", "files"):
            with self.subTest(field=forbidden_field):
                self.packet[forbidden_field] = "fabricated-disallowed-input"
                self.assert_no_dispatch()
                del self.packet[forbidden_field]

    def test_unknown_task_fields_prevent_network(self):
        self.task["source"] = "fabricated-disallowed-input"
        self.assert_no_dispatch()

    def test_invalid_budgets_prevent_network(self):
        for budget in (
            {"max_output_tokens": 0, "timeout_seconds": 8},
            {"max_output_tokens": 1025, "timeout_seconds": 8},
            {"max_output_tokens": 256, "timeout_seconds": 0},
            {"max_output_tokens": 256, "timeout_seconds": 61},
            {"max_output_tokens": True, "timeout_seconds": 8},
        ):
            with self.subTest(budget=budget):
                self.packet["budget"] = budget
                self.assert_no_dispatch()

    def test_response_wire_api_requires_feedback(self):
        self.selection["wire_api"] = "responses"
        self.initialize_state()
        self.assert_no_dispatch("needs_feedback", "RESPONSES_UNSUPPORTED")

    def test_insecure_http_prevents_network(self):
        self.selection["base_url"] = "http://api.deepseek.com"
        self.initialize_state()
        self.assert_no_dispatch()

    def test_duplicate_request_never_redispatches(self):
        self.initialize_state()
        first, _ = self.execute_fake()
        self.assertEqual(first["status"], "candidate")
        durable_before = self.inspect_worker()
        revision_before = self.state_revision
        self.packet["state"]["expected_revision"] = self.state_revision
        second, _ = self.execute_fake()
        self.assertEqual(second.get("code"), "ALREADY_EXECUTED", json.dumps(second, sort_keys=True))
        self.assertEqual(second["status"], "needs_feedback", json.dumps(second, sort_keys=True))
        self.assertEqual(len(self.transport_requests), 1)
        durable_after = self.inspect_worker()
        self.assertEqual(self.state_revision, revision_before)
        self.assertEqual(durable_after, durable_before)

    def test_remote_feedback_records_completed_operation(self):
        self.initialize_state()
        remote = {"status": "needs_feedback", "reason": "A supporting dependency is needed.", "missing_dependencies": ["additional_identity"]}
        output, _ = self.execute_fake(FabricatedResponse(self.chat_envelope(remote)))
        self.assertEqual(output["status"], "needs_feedback")
        self.assertEqual(len(self.transport_requests), 1)
        self.assertIn("SUCCEEDED", json.dumps(self.inspect_worker()))

    def test_unknown_or_unproved_candidate_dependency_is_rejected(self):
        for dependency in ("unknown_identity", "missing_identity"):
            with self.subTest(dependency=dependency):
                self.transport_requests.clear()
                self.task["dependencies"] = [self.task["dependencies"][0], {"name": "missing_identity", "statement": "An unproved identity.", "status": "missing", "version": "missing-v1"}]
                self.initialize_state()
                remote = {"status": "candidate", "answer": "A fabricated answer.", "used_dependencies": [dependency]}
                output, _ = self.execute_fake(FabricatedResponse(self.chat_envelope(remote)))
                self.assertEqual(output["status"], "rejected")
                self.assertEqual(len(self.transport_requests), 1)
                self.assertIn("FAILED", json.dumps(self.inspect_worker()))

    def test_strict_chat_envelope_rejection(self):
        cases = {
            "truncated": self.chat_envelope(finish_reason="length"),
            "tool_finish": self.chat_envelope(finish_reason="tool_calls"),
            "tool_message": self.chat_envelope(message={"role": "assistant", "content": "{}", "tool_calls": [{"id": "fabricated-tool"}]}),
            "missing_choices": {},
            "empty_choices": {"choices": []},
            "non_json_content": self.chat_envelope("This is not a JSON result."),
            "fenced_content": self.chat_envelope("```json\n{}\n```"),
            "unknown_result_status": self.chat_envelope({"status": "complete", "answer": "No valid status.", "used_dependencies": []}),
            "extra_result_field": self.chat_envelope({"status": "candidate", "answer": "A fabricated answer.", "used_dependencies": [], "source": "not-allowed"}),
            "non_string_answer": self.chat_envelope({"status": "candidate", "answer": 123, "used_dependencies": []}),
        }
        for name, payload in cases.items():
            with self.subTest(case=name):
                self.transport_requests.clear()
                self.initialize_state()
                output, _ = self.execute_fake(FabricatedResponse(payload))
                self.assertEqual(output["status"], "rejected")
                self.assertEqual(len(self.transport_requests), 1)

    def test_invalid_json_body_is_rejected(self):
        self.initialize_state()
        output, _ = self.execute_fake(FabricatedResponse(b"not a JSON body"))
        self.assertEqual(output["status"], "rejected")

    def test_non_json_content_type_is_rejected(self):
        self.initialize_state()
        output, _ = self.execute_fake(FabricatedResponse(self.chat_envelope(), content_type="text/html"))
        self.assertEqual(output["status"], "rejected")

    def test_oversized_body_is_bounded_and_rejected(self):
        self.initialize_state()
        output, response = self.execute_fake(FabricatedResponse(b"x" * (2 * 1024 * 1024)))
        self.assertEqual(output["status"], "rejected")
        self.assertTrue(response.read_limits)
        self.assertLessEqual(max(response.read_limits), 2 * 1024 * 1024)

    def test_http_failure_is_sanitized_without_retry(self):
        self.initialize_state()
        exception = urllib.error.HTTPError("https://api.deepseek.com/chat/completions", 401, FABRICATED_KEY, {}, io.BytesIO(FABRICATED_KEY.encode()))
        output, _ = self.execute_fake(exception=exception)
        self.assertNotEqual(output["status"], "candidate")
        self.assertEqual(len(self.transport_requests), 1)
        self.assertNotIn(FABRICATED_KEY, json.dumps(self.inspect_worker()))

    def test_timeout_records_unknown_and_requires_recovery(self):
        self.initialize_state()
        output, _ = self.execute_fake(exception=TimeoutError(FABRICATED_KEY))
        self.assertEqual(output["status"], "unknown")
        self.assertEqual(len(self.transport_requests), 1)
        self.generations["worker"] = 3
        observed = self.inspect_worker()
        self.assertIn("RECOVERING", json.dumps(observed))
        self.assertIn("UNKNOWN", json.dumps(observed))
        self.assertNotIn(FABRICATED_KEY, json.dumps(observed))
        self.state_mutation("resume", "worker", actor_id="root", recovery_generation=3)
        self.state_mutation("start", "worker")
        self.packet["state"]["generation"] = 3
        self.packet["state"]["expected_revision"] = self.state_revision
        blocked, _ = self.execute_fake()
        self.assertEqual(blocked.get("code"), "PENDING_OPERATION")
        self.assertEqual(len(self.transport_requests), 1)

    def test_network_error_is_unknown_and_sanitized(self):
        self.initialize_state()
        output, _ = self.execute_fake(exception=urllib.error.URLError(FABRICATED_KEY))
        self.assertEqual(output["status"], "unknown")
        self.assertEqual(len(self.transport_requests), 1)
        self.generations["worker"] = 3
        self.assertIn("UNKNOWN", json.dumps(self.inspect_worker()))

    def test_total_transport_deadline_records_unknown(self):
        self.budget["timeout_seconds"] = 1
        self.initialize_state()
        release_response = threading.Event()
        response_returned = threading.Event()

        def delayed_open(request, timeout):
            self.transport_requests.append((request, timeout))
            try:
                release_response.wait(5)
                return FabricatedResponse(self.chat_envelope())
            finally:
                response_returned.set()

        try:
            started = time.monotonic()
            with mock.patch.object(self.worker, "_open_request", side_effect=delayed_open):
                output = self.worker.execute(copy.deepcopy(self.packet))
            elapsed = time.monotonic() - started
            self.assertEqual(output["status"], "unknown")
            self.assertLess(elapsed, 4)
            self.assertEqual(len(self.transport_requests), 1)
        finally:
            release_response.set()
            self.assertTrue(response_returned.wait(3))

    def write_config(self, wire_api="chat", auth_line='env_key = "DEEPSEEK_API_KEY"'):
        CONFIG_PATH.write_text(
            'model = "fabricated-root-model"\nmodel_provider = "fabricated-root-provider"\n'
            '[model_providers.deepseek]\nname = "Fabricated DeepSeek"\n'
            'base_url = "https://api.deepseek.com"\nwire_api = "' + wire_api + '"\n' + auth_line + '\n',
            encoding="utf-8",
        )
        self.selection.clear()
        self.selection.update({"mode": "config", "config": str(CONFIG_PATH), "provider": "deepseek", "model": "deepseek-flash"})

    def test_config_chat_alias_and_explicit_model_execute(self):
        self.write_config()
        self.initialize_state()
        output, _ = self.execute_fake()
        self.assertEqual(output["status"], "candidate")
        payload = json.loads(self.transport_requests[0][0].data)
        self.assertEqual(payload["model"], "deepseek-flash")

    def test_config_inspection_reports_auth_names_without_values(self):
        self.write_config(auth_line='experimental_bearer_token = "' + FABRICATED_KEY + '"')
        output = self.worker.inspect_config(copy.deepcopy(self.selection))
        serialized = json.dumps(output)
        self.assertNotIn(FABRICATED_KEY, serialized)
        self.assertIn("deepseek", serialized)
        self.assertIn("deepseek-flash", serialized)
        self.assertIn("experimental_bearer_token", serialized)

    def test_duplicate_config_auth_sources_are_rejected(self):
        self.write_config(auth_line='env_key = "DEEPSEEK_API_KEY"\nexperimental_bearer_token = "' + FABRICATED_KEY + '"')
        self.initialize_state()
        self.assert_no_dispatch("rejected", "DUPLICATE_AUTH_HEADER")
        self.inspect_worker()
        self.assertEqual(self.state_revision, 7)

    def test_requires_openai_auth_is_not_an_auth_source(self):
        self.write_config(auth_line="requires_openai_auth = true")
        self.initialize_state()
        self.assert_no_dispatch("needs_feedback", "AUTH_SOURCE_REQUIRED")

    def test_config_missing_explicit_provider_prevents_network(self):
        self.write_config()
        del self.selection["provider"]
        self.assert_no_dispatch()

    def test_config_missing_explicit_model_prevents_network(self):
        self.write_config()
        del self.selection["model"]
        self.assert_no_dispatch()

    def test_bounded_text_candidate(self):
        self.task["kind"] = "bounded_text"
        self.task["question"] = "Return one brief plain-language explanation of the established dependency."
        self.initialize_state()
        output, _ = self.execute_fake()
        self.assertEqual(output["status"], "candidate")
        self.assertEqual(len(self.transport_requests), 1)

    def test_unsupported_task_kind_prevents_network(self):
        self.task["kind"] = "execute_files"
        self.assert_no_dispatch()

    def test_redirect_response_is_rejected_without_retry(self):
        self.initialize_state()
        redirected = FabricatedResponse(self.chat_envelope(), status=302)
        redirected.headers["Location"] = "https://fabricated-redirect.invalid/" + FABRICATED_KEY
        output, _ = self.execute_fake(redirected)
        self.assertEqual(output["status"], "rejected")
        self.assertEqual(len(self.transport_requests), 1)
        self.assertNotIn(FABRICATED_KEY, json.dumps(self.inspect_worker()))


if __name__ == "__main__":
    unittest.main(testRunner=unittest.TextTestRunner(verbosity=2, resultclass=ConciseTestResult))
