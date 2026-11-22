#!/usr/bin/env python3
"""Guarded checks, deterministic repairs and bounded packets. No model calls."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import uuid

from lean_task_support import (ROOT, MODULE, atomic_json, canonical, digest, file_lock,
                               forbidden_tokens, guarded_run, imports, json_digest,
                               lean_code, snapshot)

RUNTIME = ROOT / "tmp" / "lean-automation"
PROJECT = ROOT / "LeanFormal" / "IUT" / "Project.lean"
DIAGNOSTIC = re.compile(r"^(.*?):(\d+):(\d+):\s*(error|warning|info)(?:\([^)]*\))?:\s*(.*)$")


def parse_errors(output: str) -> list[dict]:
    errors, current = [], None
    for raw in output.splitlines():
        line = re.sub(r"\x1b\[[0-9;]*m", "", raw)
        match = DIAGNOSTIC.match(line)
        if match:
            file, row, col, severity, message = match.groups()
            current = {"file": file, "line": int(row), "col": int(col),
                       "severity": severity, "message": message[:2500]}
            if severity == "error":
                errors.append(current)
        elif current and not re.match(r"^(?:\d\d:\d\d:\d\d |-----|error:|✔|✖)", line):
            if len(current["message"]) < 2500:
                current["message"] = (current["message"] + "\n" + line)[:2500]
        else:
            current = None
    return errors


def classify(execution: dict, errors: list[dict], findings: list[dict]) -> tuple[str, str]:
    if execution["execution_status"] != "finished":
        return execution["execution_status"], "operations"
    output = execution["output"]
    if "[lean-auto-infrastructure]" in output:
        return "infrastructure_error", "operations"
    if findings or re.search(r"warning(?:\([^)]*\))?:.*(?:uses 'sorry'|declaration uses sorry)", output):
        return "proof_policy", "source_owner"
    if execution["exit"] == 0:
        return "green", "none"
    if re.search(r"object file .* does not exist|unknown module prefix|unknown package", output):
        return "missing_dependency", "dependency_build"
    if re.search(r"maximum (?:recursion depth|number of heartbeats)|out of memory|stack overflow", output, re.I):
        return "resource_limit", "operations"
    if not errors:
        return "unclassified_failure", "source_owner"
    if all(re.search(r"unknown (?:identifier|constant|tactic)|unexpected token|type mismatch|"
                     r"application type mismatch|invalid (?:field|argument)|failed to synthesize|"
                     r"unsolved goals|simp made no progress|tactic .* failed", error["message"], re.I)
           for error in errors):
        return "local_repair", "small_model_candidate"
    return "proof_review", "source_owner"


def audit(file: Path, *, runtime: Path = RUNTIME, fresh: bool = False,
          timeout: int = 900, wait_timeout: int = 180, root: Path = ROOT) -> dict:
    file = canonical(file, root)
    before = snapshot(file, root)
    cache = runtime / "cache" / (before["fingerprint"] + ".json")
    with file_lock(runtime / "locks" / (json_digest(str(file)) + ".lock"), timeout=1):
        if not fresh and cache.exists():
            try:
                result = json.loads(cache.read_text(encoding="utf-8"))
                if result.get("fingerprint") == before["fingerprint"]:
                    return {**result, "cached": True}
            except (OSError, ValueError):
                pass
        source = file.read_text(encoding="utf-8-sig")
        findings = forbidden_tokens(source)
        if before["stale_modules"]:
            execution = {"exit": 1, "execution_status": "finished", "log": "",
                         "output": "Dependency sources are newer than their compiled artifacts: "
                         + ", ".join(before["stale_modules"])}
        else:
            execution = guarded_run(["lake", "env", "lean", "-j1", str(file)], runtime,
                                    timeout, wait_timeout, root)
        after = snapshot(file, root)
        errors = parse_errors(execution["output"])
        status, route = classify(execution, errors, findings)
        if before["stale_modules"] and not findings:
            status, route = "stale_dependency", "dependency_build"
        if before != after:
            status, route = "inputs_changed", "retry_after_edits"
        result = {"schema": "lean-auto/v2", "file": str(file), **before,
                  "exit": execution["exit"] if status == "green" else execution["exit"] or 1,
                  "status": status, "route": route, "cached": False, "errors": errors[:20],
                  "error_count": len(errors), "forbidden": findings, "log": execution["log"],
                  "tail": [] if status == "green" else execution["output"][-4000:].splitlines()[-16:],
                  "validation_scope": "local compilation and lexical policy check; not an axiom or paper audit"}
        if status not in {"timeout", "resource_wait", "infrastructure_error", "inputs_changed", "resource_limit"}:
            atomic_json(cache, result)
        return result


def context_for(file: Path, errors: list[dict], radius: int = 6, *, root: Path = ROOT) -> list[dict]:
    lines = file.read_text(encoding="utf-8-sig").splitlines()
    selected, result, budget = set(), [], 5000
    for error in errors[:6]:
        if canonical(error["file"], root) != file.resolve():
            continue
        for row in range(max(1, error["line"] - radius), min(len(lines), error["line"] + radius) + 1):
            if row in selected or budget <= 0:
                continue
            selected.add(row)
            text = lines[row - 1][:min(500, budget)]
            budget -= len(text)
            result.append({"line": row, "text": text})
    return result


def packet_from_result(file: Path, result: dict, target: str = "", radius: int = 6,
                       *, root: Path = ROOT) -> dict:
    packet = {**result, "schema": "lean-auto/packet/v2", "target": target,
              "automatic_model_calls": 0}
    if result["status"] != "green":
        packet["errors"] = [{**error, "message": error["message"][:1200]} for error in result["errors"][:6]]
        packet["tail"] = [] if result["errors"] else "\n".join(result.get("tail", []))[-1600:].splitlines()
        packet["context"] = context_for(file, result["errors"], radius, root=root)
        packet["instruction"] = ("Candidate only: preserve the exact statement, hypotheses and objects. "
            "Edit only the named owner file; no sorry/axiom/native_decide, no weakening, no added assumptions. "
            "Give the smallest patch and explain its dependency. Missing mathematical premises go to the owner. "
            "A small_model_candidate route is a heuristic, not evidence the proof is easy. Recompile before acceptance.")
        packet["packet_id"] = json_digest([result["fingerprint"], result["status"], result["errors"], target])
    return packet


def duplicate_import_fix(source: str) -> tuple[str, int]:
    """Only remove repeated plain, single-line imports; leave comments and modifiers."""
    seen, output, count = set(), [], 0
    masked = lean_code(source).splitlines(keepends=True)
    for original, code in zip(source.splitlines(keepends=True), masked):
        match = re.fullmatch(r"import ([A-Za-z_][\w'.]*)\s*", code)
        if match and original.strip() == code.strip():
            module = match.group(1)
            if module in seen:
                output.append("\r\n" if original.endswith("\r\n") else "\n" if original.endswith("\n") else "")
                count += 1
                continue
            seen.add(module)
        output.append(original)
    return "".join(output), count


def repair(file: Path, *, target: str = "", apply: bool = False, build_deps: bool = False,
           runtime: Path = RUNTIME, root: Path = ROOT, **options) -> dict:
    result = audit(file, runtime=runtime, root=root, **options)
    actions = []
    if result["status"] in {"missing_dependency", "stale_dependency"} and build_deps:
        text = "\n".join(result["tail"]) + "\n" + "\n".join(e["message"] for e in result["errors"])
        missing = re.search(r"of module ([A-Za-z_][\w'.]*) does not exist", text)
        module = result.get("stale_modules", [None])[0] if result.get("stale_modules") else missing.group(1) if missing else None
        if module and MODULE.fullmatch(module) and module != "LeanFormal.IUT.Project":
            attempt = runtime / "dependency-attempts" / (json_digest([result["fingerprint"], module]) + ".json")
            if attempt.exists() and not options.get("fresh"):
                built = json.loads(attempt.read_text(encoding="utf-8"))
            else:
                built = build(module, runtime=runtime, root=root,
                              timeout=options.get("timeout", 900), wait_timeout=options.get("wait_timeout", 180))
                if built["status"] not in {"timeout", "resource_wait", "infrastructure_error", "resource_limit"}:
                    atomic_json(attempt, built)
            actions.append({"action": "build_dependency", "module": module,
                            "status": built["status"], "log": built["log"]})
            if built["status"] == "green":
                result = audit(file, runtime=runtime, root=root, **{**options, "fresh": True})
    if apply and result["status"] == "green":
        before = file.read_bytes()
        candidate, removed = duplicate_import_fix(before.decode("utf-8-sig"))
        if removed:
            encoded = (b"\xef\xbb\xbf" if before.startswith(b"\xef\xbb\xbf") else b"") + candidate.encode("utf-8")
            backup = runtime / ("repair-" + uuid.uuid4().hex + ".before")
            backup.parent.mkdir(parents=True, exist_ok=True)
            backup.write_bytes(before)
            with file_lock(runtime / "locks" / (json_digest(str(file)) + ".edit.lock")):
                if digest(file.read_bytes()) != result["sha256"]:
                    return {**result, "status": "inputs_changed", "exit": 1, "route": "retry_after_edits"}
                file.write_bytes(encoded)
                try:
                    checked = audit(file, runtime=runtime, root=root, **{**options, "fresh": True})
                except Exception:
                    if file.read_bytes() == encoded:
                        file.write_bytes(before)
                    raise
                if checked["status"] != "green":
                    if file.read_bytes() == encoded:
                        file.write_bytes(before)
                        actions.append({"action": "duplicate_imports_rolled_back", "backup": str(backup)})
                    else:
                        checked.update(status="rollback_conflict", route="source_owner", exit=1)
                else:
                    actions.append({"action": "duplicate_imports_removed", "count": removed, "backup": str(backup)})
                result = checked
    packet = packet_from_result(file, result, target, root=root)
    packet["actions"] = actions
    return packet


def build(module: str, *, runtime: Path = RUNTIME, timeout: int = 1800,
          wait_timeout: int = 180, root: Path = ROOT) -> dict:
    if not MODULE.fullmatch(module):
        raise ValueError("build expects a module name, e.g. LeanFormal.IUT.Project")
    result = guarded_run(["lake", "build", module], runtime, timeout, wait_timeout, root)
    errors = parse_errors(result["output"])
    status, route = classify(result, errors, [])
    return {"schema": "lean-auto/build/v2", "module": module, "status": status, "route": route,
            "exit": result["exit"] if status == "green" else result["exit"] or 1,
            "log": result["log"], "errors": errors[:20], "tail": result["output"][-4000:].splitlines()[-16:],
            "cached": False, "validation_scope": "Lake incremental build; not a paper-faithfulness audit"}


def promote(src: Path, dest: Path, after: str, force: bool = False, *, runtime: Path = RUNTIME,
            root: Path = ROOT, project: Path = PROJECT, **options) -> dict:
    """Explicit staging, with version-checked rollback. Project build is a batch task."""
    relative = dest.relative_to(root)
    if relative.parts[0] not in {"LeanFormal", "Iut"} or dest.suffix != ".lean" or dest in {src, project}:
        raise ValueError("destination must be a distinct production .lean file")
    if dest.exists() and not force:
        raise ValueError("destination exists; --force explicitly authorizes replacement")
    source_check = audit(src, runtime=runtime, root=root, **options)
    if source_check["status"] != "green":
        return {**source_check, "promotion": "rejected"}
    module = ".".join(relative.with_suffix("").parts)
    with file_lock(runtime / "promotion.lock", timeout=1):
        if dest.exists() and not force:
            raise ValueError("destination appeared before promotion; refusing to overwrite")
        originals = {dest: dest.read_bytes() if dest.exists() else None, project: project.read_bytes()}
        original_project = originals[project].decode("utf-8-sig")
        lines = original_project.splitlines(keepends=True)
        if module not in imports(original_project):
            anchors = [i for i, line in enumerate(lines) if imports(line) == [after]]
            if len(anchors) != 1:
                raise ValueError("--after must identify exactly one import line")
            newline = "\r\n" if "\r\n" in original_project else "\n"
            index = anchors[0]
            if not lines[index].endswith("\n"):
                lines[index] += newline
            lines.insert(index + 1, f"import {module}{newline}")
        project_bytes = (b"\xef\xbb\xbf" if originals[project].startswith(b"\xef\xbb\xbf") else b"") + "".join(lines).encode("utf-8")
        intended = {dest: src.read_bytes(), project: project_bytes}
        if digest(intended[dest]) != source_check["sha256"]:
            raise ValueError("source changed after validation")
        transaction = runtime / ("promotion-" + uuid.uuid4().hex)
        transaction.mkdir(parents=True)
        for index, (path, data) in enumerate(originals.items()):
            if data is not None:
                (transaction / f"original-{index}").write_bytes(data)
        journal = {"state": "prepared", "files": [{"path": str(path), "existed": data is not None,
                   "backup": f"original-{index}" if data is not None else None,
                   "intended_sha256": digest(intended[path])}
                  for index, (path, data) in enumerate(originals.items())]}
        atomic_json(transaction / "journal.json", journal)
        written = []
        try:
            for path, data in intended.items():
                if (path.read_bytes() if path.exists() else None) != originals[path]:
                    raise ValueError(f"concurrent edit: {path}")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                written.append(path)
            checked = audit(dest, runtime=runtime, root=root, **{**options, "fresh": True})
            if checked["status"] != "green":
                raise ValueError("destination compilation failed; see " + checked.get("log", ""))
            if any(path.read_bytes() != data for path, data in intended.items()):
                raise ValueError("concurrent edit during destination validation")
        except Exception as exc:
            conflicts = []
            for path in reversed(written):
                if not path.exists() or path.read_bytes() != intended[path]:
                    conflicts.append(str(path))
                elif originals[path] is None:
                    path.unlink()
                else:
                    path.write_bytes(originals[path])
            status = "rollback_conflict" if conflicts else "rolled_back"
            atomic_json(transaction / "journal.json", {**journal, "state": status, "conflicts": conflicts})
            return {"status": status, "exit": 1, "route": "source_owner", "reason": str(exc),
                    "conflicts": conflicts, "transaction": str(transaction)}
        atomic_json(transaction / "journal.json", {**journal, "state": "staged"})
        return {"status": "promoted_pending_batch", "exit": 0, "route": "batch_build", "file": str(dest),
                "sha256": checked["sha256"], "import": module, "transaction": str(transaction),
                "validation_scope": "destination compiled; Project integration awaits explicit batch build"}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command in ("audit", "packet", "repair", "build", "promote"):
        child = sub.add_parser(command)
        child.add_argument("file", help="source path, or module name for build")
        child.add_argument("--runtime", type=Path, default=RUNTIME)
        child.add_argument("--timeout", type=int, default=900)
        child.add_argument("--wait-timeout", type=int, default=180)
        child.add_argument("--fresh", action="store_true")
        if command in {"packet", "repair"}:
            child.add_argument("--target", default="")
        if command == "packet":
            child.add_argument("--max-context", type=int, default=6)
        if command == "repair":
            child.add_argument("--apply", action="store_true", help="remove duplicate plain imports, validate and rollback")
            child.add_argument("--build-deps", action="store_true", help="build one missing module, then retry once")
        if command == "promote":
            child.add_argument("dest")
            child.add_argument("--after", required=True)
            child.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    options = {"runtime": canonical(args.runtime), "timeout": args.timeout, "wait_timeout": args.wait_timeout}
    try:
        if args.timeout <= 0 or not 1 <= args.wait_timeout <= 86400:
            raise ValueError("positive timeout and wait-timeout 1..86400 required")
        if args.command == "build":
            result = build(args.file, **options)
        else:
            file = canonical(args.file)
            options["fresh"] = args.fresh
            if args.command == "promote":
                result = promote(file, canonical(args.dest), args.after, args.force, **options)
            elif args.command == "repair":
                result = repair(file, target=args.target, apply=args.apply, build_deps=args.build_deps, **options)
            else:
                result = audit(file, **options)
                if args.command == "packet":
                    result = packet_from_result(file, result, args.target, max(0, min(12, args.max_context)))
    except (OSError, ValueError, TimeoutError) as exc:
        result = {"schema": "lean-auto/v2", "status": "tool_error", "route": "operations", "exit": 2, "reason": str(exc)}
    print(json.dumps(result, ensure_ascii=True, indent=2))
    return result.get("exit", 1)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

