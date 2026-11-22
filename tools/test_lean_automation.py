"""Behavioral regressions; isolated fixtures, no model calls or production builds."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import lean_auto as auto
import lean_queue as queue
import lean_task_support as support
import lean_triage as triage
import lean_worker as worker


def execution(output="", exit=0, status="finished"):
    return {"output": output, "exit": exit, "execution_status": status, "log": "fixture.log"}


class AutomationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lean-automation-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.runtime = self.root / "runtime"
        self.file = self.write("Owner.lean", "theorem ownerIdentity (n : Nat) : n = n := rfl\n")
        self.queue = self.root / "queue.jsonl"

    def write(self, name, text):
        file = self.root / name
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text, encoding="utf-8")
        return file

    def audit(self, **kwargs):
        return auto.audit(self.file, root=self.root, runtime=self.runtime, **kwargs)

    def test_nested_comments_strings_and_names_do_not_trigger_policy(self):
        source = '/- sorry /- axiom -/ admit -/\n-- sorry\ndef s := "axiom \\\" sorry"\n'
        source += 'def raw := r##"sorry " admit"##\ndef «sorry» := 1\n'
        source += 'theorem unfinished : True := by\n  sorry\n'
        findings = support.forbidden_tokens(source)
        self.assertEqual([finding["token"] for finding in findings], ["sorry"])
        self.assertEqual(len(support.lean_code(source)), len(source))

    def test_actual_forbidden_tokens_are_reported(self):
        self.assertEqual([item["token"] for item in support.forbidden_tokens(
            "private axiom gap : True\ntheorem other : True := by admit\n")], ["axiom", "admit"])

    def test_quote_character_does_not_hide_following_axiom(self):
        findings = support.forbidden_tokens("def quote := '\"'\naxiom gap : True\n")
        self.assertEqual([item["token"] for item in findings], ["axiom"])

    def test_import_scanning_stops_before_namespaces(self):
        self.assertEqual(support.imports("import Alpha\nBeta\n  namespace Owner\n"), ["Alpha", "Beta"])

    def test_public_imports_multiline_and_nested_comments(self):
        self.assertEqual(support.imports("module\npublic import LeanFormal.A Iut.B\n  Mathlib.C\n"
            "/- import Fake -/\nimport LeanFormal.D\ndef text := \"import Fake\"\n"),
            ["LeanFormal.A", "Iut.B", "Mathlib.C", "LeanFormal.D"])

    def test_windows_diagnostics_keep_file_and_multiline_goals(self):
        errors = auto.parse_errors("D:\\repo\\Owner.lean:8:2: error: unsolved goals\n"
                                  "n : Nat\n⊢ n = n\nOther.lean:2:1: warning: hello\n")
        self.assertEqual(len(errors), 1)
        self.assertEqual(errors[0]["file"], r"D:\repo\Owner.lean")
        self.assertIn("⊢ n = n", errors[0]["message"])

    def test_lean_432_coded_diagnostics_route_local_errors(self):
        output = f"{self.file}:4:8: error(lean.unknownIdentifier): Unknown identifier `missing`\n"
        errors = auto.parse_errors(output)
        self.assertEqual(errors[0]["line"], 4)
        self.assertEqual(auto.classify(execution(output, 1), errors, []), ("local_repair", "small_model_candidate"))

    def test_coded_sorry_warning_is_not_green(self):
        output = f"{self.file}:1:1: warning(lean.sorry): declaration uses 'sorry'\n"
        self.assertEqual(auto.classify(execution(output), [], [])[0], "proof_policy")

    def test_compact_worker_output_omits_source_and_logs(self):
        result = worker.compact_result({"status": "local_repair", "route": "small_model_candidate",
            "context": [{"text": "source"}], "tail": ["long log"], "result_file": "packet.json"})
        self.assertNotIn("context", result)
        self.assertNotIn("tail", result)
        self.assertEqual(result["result_file"], "packet.json")

    def test_dependency_error_does_not_read_wrong_source_context(self):
        errors = [{"file": "Other.lean", "line": 1}]
        self.assertEqual(auto.context_for(self.file, errors, root=self.root), [])

    def test_success_packet_has_exit_zero(self):
        with patch.object(auto, "guarded_run", return_value=execution()):
            result = auto.packet_from_result(self.file, self.audit())
        self.assertEqual((result["status"], result["exit"]), ("green", 0))

    def test_unchanged_failures_compile_once(self):
        output = f"{self.file}:1:1: error: unknown identifier 'missing'"
        with patch.object(auto, "guarded_run", return_value=execution(output, 1)) as runner:
            first, second = self.audit(), self.audit()
        self.assertEqual(runner.call_count, 1)
        self.assertFalse(first["cached"])
        self.assertTrue(second["cached"])
        self.assertEqual(second["route"], "small_model_candidate")

    def test_transitive_source_change_invalidates_cache(self):
        self.file.write_text("import Local.First\n", encoding="utf-8")
        self.write("Local/First.lean", "public import Local.Second\n")
        leaf = self.write("Local/Second.lean", "def currentVersion := 1\n")
        with patch.object(auto, "guarded_run", return_value=execution()) as runner:
            self.audit()
            leaf.write_text("def currentVersion := 2\n", encoding="utf-8")
            self.audit()
        self.assertEqual(runner.call_count, 2)

    def test_artifact_and_config_changes_invalidate_fingerprint(self):
        self.file.write_text("import Local.First\n", encoding="utf-8")
        self.write("Local/First.lean", "def localValue := 1\n")
        initial = support.snapshot(self.file, self.root)
        self.write(".lake/build/lib/lean/Local/First.olean", "compiled")
        rebuilt = support.snapshot(self.file, self.root)
        self.assertNotEqual(initial["fingerprint"], rebuilt["fingerprint"])
        self.write("lean-toolchain", "leanprover/lean4:v4.32.2")
        self.assertNotEqual(rebuilt["fingerprint"], support.snapshot(self.file, self.root)["fingerprint"])

    def test_concurrent_edits_are_not_reported_green_or_cached(self):
        def edit_during_compile(*args):
            self.file.write_text("changed during compile\n", encoding="utf-8")
            return execution()
        with patch.object(auto, "guarded_run", side_effect=edit_during_compile):
            result = self.audit()
        self.assertEqual(result["status"], "inputs_changed")
        self.assertNotEqual(result["exit"], 0)
        self.assertFalse((self.runtime / "cache").exists())

    def test_resource_wait_is_not_model_work_or_cached(self):
        with patch.object(auto, "guarded_run", return_value=execution("busy", 2, "resource_wait")) as runner:
            self.audit()
            result = self.audit()
        self.assertEqual(runner.call_count, 2)
        self.assertEqual(result["route"], "operations")

    def test_proof_placeholders_cannot_be_green(self):
        self.file.write_text("theorem invalid : False := by sorry\n", encoding="utf-8")
        with patch.object(auto, "guarded_run", return_value=execution()):
            result = self.audit()
        self.assertEqual(result["status"], "proof_policy")
        self.assertNotEqual(result["exit"], 0)

    def test_fresh_forces_recompile(self):
        with patch.object(auto, "guarded_run", return_value=execution()) as runner:
            self.audit()
            self.audit(fresh=True)
        self.assertEqual(runner.call_count, 2)

    def test_duplicate_fix_preserves_comments_modifiers_and_lines(self):
        source = "import Init\nimport Init\npublic import Init\nimport Init -- retained\n"
        candidate, removed = auto.duplicate_import_fix(source)
        self.assertEqual(removed, 1)
        self.assertEqual(candidate, "import Init\n\npublic import Init\nimport Init -- retained\n")

    def test_failed_mechanical_fix_restores_original_bytes(self):
        original = b"import Init\r\nimport Init\r\n"
        self.file.write_bytes(original)
        with patch.object(auto, "guarded_run", side_effect=[execution(), execution("failed", 1)]):
            result = auto.repair(self.file, apply=True, runtime=self.runtime, root=self.root)
        self.assertEqual(self.file.read_bytes(), original)
        self.assertEqual(result["actions"][0]["action"], "duplicate_imports_rolled_back")

    def test_missing_dependency_builds_only_named_module_then_retries(self):
        missing = execution("error: object file 'Some.olean' of module Local.First does not exist", 1)
        with patch.object(auto, "guarded_run", side_effect=[missing, execution(), execution()]) as runner:
            result = auto.repair(self.file, build_deps=True, runtime=self.runtime, root=self.root)
        self.assertEqual(result["status"], "green")
        self.assertEqual(runner.call_args_list[1].args[0], ["lake", "build", "Local.First"])
        self.assertEqual(runner.call_count, 3)

    def test_queue_init_preserves_history_and_deduplicates(self):
        first = queue.operate(self.queue, "add", file=str(self.file))
        history = self.queue.read_bytes()
        self.assertEqual(queue.operate(self.queue, "init")["status"], "exists")
        self.assertEqual(self.queue.read_bytes(), history)
        second = queue.operate(self.queue, "add", file=str(self.root / "sub/../Owner.lean"))
        self.assertEqual(first["id"], second["id"])
        self.assertTrue(second["deduplicated"])

    def test_corrupt_history_is_not_silently_discarded(self):
        self.queue.write_text('{"op":', encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "corrupt"):
            queue.operate(self.queue, "list")

    def test_claim_token_prevents_wrong_worker_completion(self):
        queue.operate(self.queue, "add", file=str(self.file))
        task = queue.operate(self.queue, "claim", worker="correct")
        with self.assertRaisesRegex(ValueError, "worker/token"):
            queue.operate(self.queue, "complete", id=task["id"], worker="incorrect", token=task["token"])
        result = queue.operate(self.queue, "complete", id=task["id"], worker="correct", token=task["token"])
        self.assertEqual(result["status"], "green")

    def test_concurrent_process_claims_cannot_take_same_file(self):
        queue.operate(self.queue, "add", file=str(self.file), kind="audit")
        queue.operate(self.queue, "add", file=str(self.file), kind="repair")
        def claim(index):
            completed = subprocess.run([sys.executable, "-X", "utf8", "-B", str(Path(queue.__file__)),
                "--queue", str(self.queue), "claim", "--worker", f"worker-{index}"],
                capture_output=True, text=True, encoding="utf-8", timeout=20)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            return json.loads(completed.stdout)
        with ThreadPoolExecutor(max_workers=6) as pool:
            results = list(pool.map(claim, range(6)))
        self.assertEqual(sum(result["status"] == "running" for result in results), 1)

    def test_crashed_claim_requires_explicit_confirmed_release(self):
        queue.operate(self.queue, "add", file=str(self.file))
        task = queue.operate(self.queue, "claim", worker="stopped")
        with self.assertRaisesRegex(ValueError, "confirmed-stopped"):
            queue.operate(self.queue, "release", id=task["id"], reason="process ended")
        queue.operate(self.queue, "release", id=task["id"], reason="process ended", confirmed_stopped=True)
        new = queue.operate(self.queue, "claim", worker="replacement")
        self.assertNotEqual(new["token"], task["token"])

    def test_build_job_blocks_other_claims(self):
        queue.operate(self.queue, "add", file="LeanFormal.IUT.Project", kind="build")
        queue.operate(self.queue, "add", file=str(self.file), kind="audit")
        self.assertEqual(queue.operate(self.queue, "claim", worker="build")["kind"], "build")
        self.assertEqual(queue.operate(self.queue, "claim", worker="other")["status"], "empty")

    def test_worker_dispatches_build_and_promotion(self):
        with patch.object(auto, "build", return_value={"status": "green"}) as build:
            worker.execute_task({"kind": "build", "file": "LeanFormal.IUT.Project"}, self.runtime, 10, 10)
            self.assertEqual(build.call_args.args[0], "LeanFormal.IUT.Project")
        with patch.object(auto, "promote", return_value={"status": "promoted_pending_batch"}) as promote:
            worker.execute_task({"kind": "promote", "file": str(self.file),
                "dest": str(self.root / "LeanFormal/Candidate.lean"), "after": "Init"}, self.runtime, 10, 10)
            promote.assert_called_once()

    def test_worker_completes_green_and_persists_result(self):
        queue.operate(self.queue, "add", file=str(self.file))
        with patch.object(auto, "guarded_run", return_value=execution()):
            result = worker.work_once(self.queue, "worker", runtime=self.runtime)
        self.assertEqual(result["queue_status"], "green")
        self.assertEqual(result["automatic_model_calls"], 0)
        self.assertTrue(Path(result["result_file"]).is_file())

    def test_worker_rejects_stale_queued_source(self):
        queue.operate(self.queue, "add", file=str(self.file))
        self.file.write_text("edited\n", encoding="utf-8")
        with patch.object(auto, "guarded_run") as runner:
            result = worker.work_once(self.queue, "worker", runtime=self.runtime)
        self.assertEqual(result["status"], "inputs_changed")
        runner.assert_not_called()

    def promotion_fixture(self, existing=True):
        project = self.write("LeanFormal/IUT/Project.lean", "import Init\n")
        dest = self.root / "LeanFormal/IUT/Candidate.lean"
        if existing:
            dest.write_bytes(b"original destination\r\n")
        return project, dest

    def test_failed_forced_promotion_restores_both_files(self):
        project, dest = self.promotion_fixture()
        before = project.read_bytes(), dest.read_bytes()
        with patch.object(auto, "guarded_run", side_effect=[execution(), execution("bad destination", 1)]):
            result = auto.promote(self.file, dest, "Init", True, runtime=self.runtime,
                                  root=self.root, project=project)
        self.assertEqual(result["status"], "rolled_back")
        self.assertEqual((project.read_bytes(), dest.read_bytes()), before)

    def test_failed_new_promotion_removes_only_created_destination(self):
        project, dest = self.promotion_fixture(existing=False)
        before = project.read_bytes()
        with patch.object(auto, "guarded_run", side_effect=[execution(), execution("bad destination", 1)]):
            result = auto.promote(self.file, dest, "Init", runtime=self.runtime, root=self.root, project=project)
        self.assertEqual(result["status"], "rolled_back")
        self.assertFalse(dest.exists())
        self.assertEqual(project.read_bytes(), before)

    def test_promotion_does_not_overwrite_concurrent_project_edit_on_rollback(self):
        project, dest = self.promotion_fixture(existing=False)
        def concurrent_edit(*args):
            project.write_bytes(b"concurrent owner edit\n")
            return execution("failed", 1)
        responses = iter([False, True])
        def runner(*args):
            return concurrent_edit() if next(responses) else execution()
        with patch.object(auto, "guarded_run", side_effect=runner):
            result = auto.promote(self.file, dest, "Init", runtime=self.runtime, root=self.root, project=project)
        self.assertEqual(result["status"], "rollback_conflict")
        self.assertEqual(project.read_bytes(), b"concurrent owner edit\n")

    def test_promotion_success_is_staged_not_project_verified(self):
        project, dest = self.promotion_fixture(existing=False)
        with patch.object(auto, "guarded_run", return_value=execution()) as runner:
            result = auto.promote(self.file, dest, "Init", runtime=self.runtime, root=self.root, project=project)
        self.assertEqual(result["status"], "promoted_pending_batch")
        self.assertFalse(any(call.args[0][1] == "build" for call in runner.call_args_list))

    def test_reachability_uses_correct_root_and_keeps_same_name_matches(self):
        project = self.write("LeanFormal/IUT/Project.lean", "public import LeanFormal.First\n")
        first = self.write("LeanFormal/First.lean", "import Iut.Second\n")
        second = self.write("Iut/Second.lean", "def second := 2\n")
        other = self.write("tmp/First.lean", "def other := 3\n")
        inventory = triage.inventory([project, first, second, other], project=project, root=self.root)
        self.assertEqual(inventory["not_in_project_review_candidates"], [str(other)])
        self.assertEqual(len(inventory["same_name_groups"][0]), 2)

    def test_timeout_terminates_owned_process(self):
        result = support.run_bounded([sys.executable, "-c", "import time; time.sleep(20)"], 1, self.root)
        self.assertEqual(result.returncode, 124)
        self.assertIn("lean-auto-timeout", result.stderr)

    def test_newer_dependency_source_is_not_certified_against_old_artifact(self):
        import os
        self.file.write_text("import Local.First\n", encoding="utf-8")
        source = self.write("Local/First.lean", "def localValue := 1\n")
        artifact = self.write(".lake/build/lib/lean/Local/First.olean", "old")
        stat = artifact.stat()
        os.utime(source, ns=(stat.st_atime_ns, stat.st_mtime_ns + 10_000_000_000))
        with patch.object(auto, "guarded_run") as runner:
            result = self.audit()
        self.assertEqual(result["status"], "stale_dependency")
        runner.assert_not_called()

    def test_unchanged_failed_dependency_build_is_not_repeated(self):
        missing = execution("error: object file 'Some.olean' of module Local.First does not exist", 1)
        with patch.object(auto, "guarded_run", side_effect=[missing, execution("failed", 1)]) as runner:
            auto.repair(self.file, build_deps=True, runtime=self.runtime, root=self.root)
            auto.repair(self.file, build_deps=True, runtime=self.runtime, root=self.root)
        self.assertEqual(runner.call_count, 2)

    def test_powershell_quoting_keeps_metacharacters_literal(self):
        self.assertEqual(support.ps_quote("a'b $(danger) `literal"), "'a''b $(danger) `literal'")


if __name__ == "__main__":
    unittest.main(verbosity=2)
