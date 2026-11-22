#!/usr/bin/env python3
"""Read-only inventory. Explicit files by default; --all-project enables broad scanning."""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
from pathlib import Path

from lean_task_support import ROOT, canonical, digest, forbidden_tokens, imports

PROJECT = ROOT / "LeanFormal/IUT/Project.lean"


def module_path(module: str, root: Path = ROOT) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def reachable_from_project(project: Path = PROJECT, root: Path = ROOT) -> set[Path]:
    pending, seen = deque([project]), set()
    while pending:
        file = pending.popleft().resolve()
        if file in seen or not file.is_file():
            continue
        seen.add(file)
        for module in imports(file.read_text(encoding="utf-8-sig")):
            candidate = module_path(module, root)
            if candidate.is_file():
                pending.append(candidate)
    return seen


def inventory(files: list[Path], *, project: Path | None = None, root: Path = ROOT) -> dict:
    files = sorted(set(file.resolve() for file in files))
    reached = reachable_from_project(project, root) if project else None
    records, by_name, by_hash = [], defaultdict(list), defaultdict(list)
    for file in files:
        data = file.read_bytes()
        source = data.decode("utf-8-sig")
        modules = imports(source)
        record = {"file": str(file), "sha256": digest(data),
                  "imports": modules, "forbidden": forbidden_tokens(source),
                  "duplicate_imports": sorted({module for module in modules if modules.count(module) > 1})}
        if reached is not None:
            record["reachable_from_project"] = file in reached
        records.append(record)
        by_name[file.name].append(str(file))
        by_hash[record["sha256"]].append(str(file))
    return {"schema": "lean-triage/v2", "files": records,
            "same_name_groups": [group for group in by_name.values() if len(group) > 1],
            "same_bytes_groups": [group for group in by_hash.values() if len(group) > 1],
            "not_in_project_review_candidates": [record["file"] for record in records
                if record.get("reachable_from_project") is False],
            "meaning": "Inventory only. Unreachable or duplicate files are not automatically useless, deletable or promotable.",
            "automatic_model_calls": 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group(required=True)
    scope.add_argument("--files", nargs="+", type=Path)
    scope.add_argument("--all-project", action="store_true", help="explicitly authorize repository/scratch inventory")
    parser.add_argument("--scratch-root", type=Path, default=ROOT / "tmp")
    args = parser.parse_args()
    try:
        if args.all_project:
            files = [file for directory in (ROOT / "LeanFormal", ROOT / "Iut", canonical(args.scratch_root))
                     if directory.exists() for file in directory.rglob("*.lean")]
            result = inventory(files, project=PROJECT)
        else:
            result = inventory([canonical(file) for file in args.files])
    except (OSError, ValueError) as exc:
        print(json.dumps({"status": "inventory_error", "reason": str(exc)}, ensure_ascii=True))
        return 2
    print(json.dumps(result, ensure_ascii=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

