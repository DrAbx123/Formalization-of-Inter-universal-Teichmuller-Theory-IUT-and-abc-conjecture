#!/usr/bin/env python3
"""Locked append-only task queue. No model calls, no implicit retries."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import time
import uuid

from lean_task_support import ROOT, canonical, file_lock, json_digest, path_key, snapshot, MODULE

DEFAULT_QUEUE = ROOT / "tmp" / "lean-queue.jsonl"


def append(path: Path, event: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps({**event, "ts": time.time()}, ensure_ascii=True, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def task_files(task: dict) -> set[str]:
    if task["kind"] == "build":
        return {"@build"}  # Builds conflict with all other jobs in this queue.
    files = {path_key(task["file"])}
    if task.get("dest"):
        files |= {path_key(task["dest"]), path_key(ROOT / "LeanFormal/IUT/Project.lean")}
    return files


def replay(path: Path) -> tuple[dict, dict]:
    tasks = {}
    if path.exists():
        for number, line in enumerate(path.read_text(encoding="utf-8-sig").splitlines(), 1):
            if not line.strip():
                continue
            try:
                event = json.loads(line)
                op, identity = event["op"], event.get("id")
            except (ValueError, KeyError, TypeError) as exc:
                raise ValueError(f"queue corrupt at line {number}; preserve history and repair explicitly") from exc
            if op == "create":
                if not identity or identity in tasks:
                    raise ValueError(f"duplicate/missing task ID at line {number}")
                tasks[identity] = {**event, "status": "pending", "worker": None, "token": None}
            elif op in {"claim", "complete", "fail", "retry", "release"}:
                if identity not in tasks:
                    raise ValueError(f"unknown task at line {number}")
                task = tasks[identity]
                if op == "claim":
                    task.update(status="running", worker=event["worker"], token=event.get("token"),
                                claimed=event.get("ts"))
                elif op == "complete":
                    task.update(status=event.get("status", "green"), sha256=event.get("sha256"),
                                result=event.get("result"))
                elif op == "fail":
                    task.update(status="failed", reason=event.get("reason"), result=event.get("result"))
                else:
                    task.update(status="pending", worker=None, token=None)
            else:
                raise ValueError(f"unknown queue event at line {number}: {op}")
    active = {}
    for identity, task in tasks.items():
        if task["status"] == "running":
            for file in task_files(task):
                if file in active:
                    raise ValueError(f"conflicting active owners: {file}")
                active[file] = identity
    return tasks, active


def operate(path: Path, operation: str, **args) -> dict:
    path = canonical(path)
    with file_lock(Path(str(path) + ".lock")):
        if operation == "init":
            existed = path.exists()
            if not existed:
                path.touch()
            return {"status": "exists" if existed else "initialized", "queue": str(path)}
        tasks, active = replay(path)
        if operation == "list":
            return {"tasks": list(tasks.values()), "active_files": active}
        if operation == "add":
            kind, file = args.get("kind", "audit"), args["file"]
            if kind not in {"audit", "repair", "promote", "build"}:
                raise ValueError("unsupported task kind")
            if kind == "build":
                if not MODULE.fullmatch(file):
                    raise ValueError("build --file expects a module name")
                fingerprint = None  # Lake itself does incremental build checks.
            else:
                file = str(canonical(file))
                fingerprint = snapshot(Path(file))["fingerprint"]
            dest = str(canonical(args["dest"])) if args.get("dest") else ""
            if kind == "promote" and (not dest or not args.get("after")):
                raise ValueError("promotion requires --dest and --after")
            key = json_digest([kind, path_key(file) if kind != "build" else file, fingerprint,
                               args.get("target", ""), dest, args.get("after", ""),
                               args.get("apply", False), args.get("build_deps", False)])
            for task in tasks.values():
                if task.get("dedupe_key") == key and not args.get("new"):
                    if kind != "build" or task["status"] in {"pending", "running"}:
                        return {"id": task["id"], "status": task["status"], "deduplicated": True}
            identity = "T" + uuid.uuid4().hex[:16]
            event = {"op": "create", "id": identity, "file": file, "kind": kind,
                     "target": args.get("target", ""), "dest": dest, "after": args.get("after", ""),
                     "apply": args.get("apply", False), "build_deps": args.get("build_deps", False),
                     "fingerprint": fingerprint, "dedupe_key": key}
            append(path, event)
            return {"id": identity, "status": "pending", "deduplicated": False}
        if operation == "claim":
            for task in tasks.values():
                if task["status"] != "pending" or args.get("kind") and task["kind"] != args["kind"]:
                    continue
                needed = task_files(task)
                if needed & active.keys() or "@build" in active or "@build" in needed and active:
                    continue
                token = uuid.uuid4().hex
                append(path, {"op": "claim", "id": task["id"], "worker": args["worker"], "token": token})
                return {**task, "status": "running", "worker": args["worker"], "token": token}
            return {"status": "empty"}
        identity = args["id"]
        if identity not in tasks:
            raise ValueError(f"unknown task: {identity}")
        task = tasks[identity]
        if operation == "retry":
            if task["status"] != "failed":
                raise ValueError("only a failed task can be explicitly retried")
            append(path, {"op": "retry", "id": identity, "reason": args["reason"]})
            return {"id": identity, "status": "pending"}
        if task["status"] != "running":
            raise ValueError("task is not running")
        if operation == "release":
            if not args.get("confirmed_stopped"):
                raise ValueError("release requires --confirmed-stopped; elapsed time is not proof")
            append(path, {"op": "release", "id": identity, "reason": args["reason"]})
            return {"id": identity, "status": "pending"}
        if task.get("worker") != args.get("worker") or not task.get("token") or task["token"] != args.get("token"):
            raise ValueError("worker/token does not own the claim")
        if operation == "complete":
            status = args.get("status", "green")
            if status not in {"green", "staged"}:
                raise ValueError("invalid completion status")
            append(path, {"op": "complete", "id": identity, "status": status,
                          "sha256": args.get("sha256"), "result": args.get("result")})
            return {"id": identity, "status": status}
        if operation == "fail":
            append(path, {"op": "fail", "id": identity, "reason": args["reason"], "result": args.get("result")})
            return {"id": identity, "status": "failed"}
        raise ValueError("unsupported operation")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, default=DEFAULT_QUEUE)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("init")
    commands.add_parser("list")
    add = commands.add_parser("add")
    add.add_argument("--file", required=True)
    add.add_argument("--kind", default="audit", choices=["audit", "repair", "promote", "build"])
    for name in ("target", "dest", "after"):
        add.add_argument("--" + name, default="")
    for name in ("new", "apply", "build-deps"):
        add.add_argument("--" + name, action="store_true")
    claim = commands.add_parser("claim")
    claim.add_argument("--worker", required=True)
    claim.add_argument("--kind")
    for command in ("complete", "fail", "retry", "release"):
        child = commands.add_parser(command)
        child.add_argument("--id", required=True)
        if command in {"complete", "fail"}:
            child.add_argument("--worker", required=True)
            child.add_argument("--token", required=True)
        if command == "complete":
            child.add_argument("--sha256", default="")
            child.add_argument("--status", choices=["green", "staged"], default="green")
        else:
            child.add_argument("--reason", required=True)
        if command == "release":
            child.add_argument("--confirmed-stopped", action="store_true")
    args = vars(parser.parse_args(argv))
    path, operation = args.pop("queue"), args.pop("command")
    try:
        result = operate(path, operation, **args)
    except (OSError, ValueError, TimeoutError) as exc:
        result = {"status": "queue_error", "reason": str(exc)}
    print(json.dumps(result, ensure_ascii=True, indent=2))
    return 2 if result.get("status") == "queue_error" else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

