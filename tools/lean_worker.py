#!/usr/bin/env python3
"""Run a bounded queue batch. Automatic model-call budget is always zero."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import lean_auto
import lean_queue
from lean_task_support import ROOT, atomic_json, canonical, snapshot


def execute_task(task: dict, runtime: Path, timeout: int, wait_timeout: int) -> dict:
    kind = task["kind"]
    options = {"runtime": runtime, "timeout": timeout, "wait_timeout": wait_timeout}
    if kind == "build":
        return lean_auto.build(task["file"], **options)
    file = canonical(task["file"])
    if task.get("fingerprint") and snapshot(file)["fingerprint"] != task["fingerprint"]:
        return {"status": "inputs_changed", "exit": 1, "route": "requeue_current_version",
                "file": str(file), "reason": "queued inputs differ; add a task for the current version"}
    if kind == "audit":
        result = lean_auto.audit(file, **options)
        return lean_auto.packet_from_result(file, result, task.get("target", ""))
    if kind == "repair":
        return lean_auto.repair(file, target=task.get("target", ""), apply=task.get("apply", False),
                                build_deps=task.get("build_deps", False), **options)
    if kind == "promote":
        return lean_auto.promote(file, canonical(task["dest"]), task["after"], **options)
    raise ValueError(f"unsupported task kind: {kind}")


def work_once(queue: Path, worker: str, *, kind: str | None = None,
              runtime: Path = lean_auto.RUNTIME, timeout: int = 900, wait_timeout: int = 180) -> dict:
    task = lean_queue.operate(queue, "claim", worker=worker, kind=kind)
    if task["status"] == "empty":
        return {"status": "empty", "exit": 0, "automatic_model_calls": 0}
    try:
        result = execute_task(task, runtime, timeout, wait_timeout)
    except (OSError, ValueError, TimeoutError) as exc:
        result = {"status": "tool_error", "route": "operations", "exit": 2, "reason": str(exc)}
    packet_path = runtime / "results" / (task["id"] + "-" + task["token"] + ".json")
    result.update(task_id=task["id"], automatic_model_calls=0)
    atomic_json(packet_path, result)
    owner = {"id": task["id"], "worker": worker, "token": task["token"], "result": str(packet_path)}
    if result.get("exit") == 0 and result["status"] in {"green", "promoted_pending_batch"}:
        status = "staged" if result["status"] == "promoted_pending_batch" else "green"
        completed = lean_queue.operate(queue, "complete", status=status, sha256=result.get("sha256", ""), **owner)
    else:
        completed = lean_queue.operate(queue, "fail", reason=result["status"], **owner)
    return {**result, "queue_status": completed["status"], "result_file": str(packet_path)}


def compact_result(result: dict) -> dict:
    fields = ("task_id", "status", "exit", "route", "cached", "queue_status", "error_count",
              "result_file", "automatic_model_calls", "reason", "actions")
    return {key: result[key] for key in fields if key in result}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, default=lean_queue.DEFAULT_QUEUE)
    parser.add_argument("--worker", required=True)
    parser.add_argument("--kind", choices=["audit", "repair", "promote", "build"])
    parser.add_argument("--out", type=Path)
    parser.add_argument("--details", action="store_true", help="print full packets instead of compact statuses")
    parser.add_argument("--runtime", type=Path, default=lean_auto.RUNTIME)
    parser.add_argument("--max-tasks", type=int, default=1, help="bounded batch, not a resident daemon")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--wait-timeout", type=int, default=180)
    args = parser.parse_args(argv)
    try:
        if not 1 <= args.max_tasks <= 100 or args.timeout <= 0 or not 1 <= args.wait_timeout <= 86400:
            raise ValueError("max-tasks 1..100 and positive bounded timeouts required")
        results = []
        for _ in range(args.max_tasks):
            result = work_once(canonical(args.queue), args.worker, kind=args.kind,
                               runtime=canonical(args.runtime), timeout=args.timeout, wait_timeout=args.wait_timeout)
            if result["status"] == "empty":
                if not results:
                    results.append(result)
                break
            results.append(result)
        output = results[0] if args.max_tasks == 1 else {"results": results, "automatic_model_calls": 0}
        exit_code = int(any(result.get("exit", 1) != 0 for result in results))
    except (OSError, ValueError, TimeoutError) as exc:
        output, exit_code = {"status": "worker_error", "reason": str(exc), "automatic_model_calls": 0}, 2
    if args.out:
        atomic_json(canonical(args.out), output)
    display = output
    if not args.details:
        display = {"results": [compact_result(item) for item in output["results"]], "automatic_model_calls": 0} \
            if "results" in output else compact_result(output)
    print(json.dumps(display, ensure_ascii=True, indent=2))
    return exit_code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

