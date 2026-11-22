"""Shared, standard-library-only mechanics for Lean automation (no model calls)."""
from __future__ import annotations

import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
VERSION = "lean-automation/v2"
MODULE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\Z")


def canonical(path: str | Path, root: Path = ROOT) -> Path:
    return (root / path).resolve()


def path_key(path: str | Path) -> str:
    return os.path.normcase(str(canonical(path)))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_digest(value) -> str:
    return digest(json.dumps(value, sort_keys=True, ensure_ascii=True).encode())


def atomic_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        temporary.write_text(json.dumps(value, ensure_ascii=True, indent=2), encoding="utf-8")
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


@contextlib.contextmanager
def file_lock(path: Path, timeout: float = 10):
    """OS lock, released even on process death; never delete a shared lock file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+b") as handle:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"\0")
            handle.flush()
        deadline = time.monotonic() + timeout
        while True:
            try:
                handle.seek(0)
                if os.name == "nt":
                    import msvcrt
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    import fcntl
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError:
                if time.monotonic() >= deadline:
                    raise TimeoutError(f"lock busy: {path}")
                time.sleep(0.05)
        try:
            yield
        finally:
            handle.seek(0)
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def lean_code(source: str) -> str:
    """Mask nested comments, normal/raw strings and quoted names; keep offsets."""
    chars = list(source)
    size, pos = len(source), 0

    def mask(start, end):
        for index in range(start, end):
            if chars[index] not in "\r\n":
                chars[index] = " "

    while pos < size:
        start = pos
        if source.startswith("--", pos):
            end = source.find("\n", pos)
            pos = size if end < 0 else end
        elif source.startswith("/-", pos):
            depth, pos = 1, pos + 2
            while pos < size and depth:
                if source.startswith("/-", pos):
                    depth, pos = depth + 1, pos + 2
                elif source.startswith("-/", pos):
                    depth, pos = depth - 1, pos + 2
                else:
                    pos += 1
        elif source[pos] == '"' or re.match(r'r#+"', source[pos:pos + 32]):
            raw = re.match(r'r(#+)"', source[pos:])
            if raw:
                end_token = '"' + raw.group(1)
                end = source.find(end_token, pos + len(raw.group(0)))
                pos = size if end < 0 else end + len(end_token)
            else:
                pos += 1
                while pos < size:
                    if source[pos] == "\\":
                        pos += 2
                    elif source[pos] == '"':
                        pos += 1
                        break
                    else:
                        pos += 1
                pos = min(pos, size)
        elif source[pos] == "«":
            end = source.find("»", pos + 1)
            pos = size if end < 0 else end + 1
        elif source[pos] == "'" and (character := re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\r\n])'", source[pos:])):
            pos += len(character.group(0))
        else:
            pos += 1
            continue
        mask(start, pos)
    return "".join(chars)


def imports(source: str) -> list[str]:
    code = lean_code(source)
    # Import lists may continue on following lines. Stop at the next command.
    names = []
    continuation = False
    commands = {"namespace", "section", "end", "open", "set_option", "attribute", "def", "theorem",
                "lemma", "example", "instance", "structure", "class", "inductive", "noncomputable",
                "private", "protected", "variable", "variables", "universe", "universes", "axiom"}
    for line in code.splitlines():
        if line.strip() in {"module", "prelude"}:
            continue
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$", line)
        if match:
            tokens = match.group(1).split()
            continuation = True
        elif continuation and line.strip():
            tokens = line.split()
        elif not line.strip():
            continue
        else:
            break
        if any(token in commands for token in tokens) or not all(MODULE.fullmatch(token) for token in tokens):
            break
        names.extend(tokens)
    return names


def forbidden_tokens(source: str) -> list[dict]:
    code = lean_code(source)
    pattern = r"(?<![\w.'])\b(?:sorry|admit|native_decide|axiom)\b(?![\w'])"
    return [{"token": m.group(), "offset": m.start(),
             "line": code.count("\n", 0, m.start()) + 1}
            for m in re.finditer(pattern, code)]


def snapshot(file: Path, root: Path = ROOT) -> dict:
    """Hash source import closure; include compiled artifact metadata and config.

    This is reuse of recorded evidence, not a fresh kernel/axiom audit. Generated
    files read by metaprograms, environment variables and external IO need --fresh.
    """
    packages = root / ".lake" / "packages"
    bases = [root] + (sorted(p for p in packages.iterdir() if p.is_dir())
                      if packages.exists() else [])
    pending, seen, source_rows, artifacts, stale_modules = [file], set(), [], [], set()
    while pending:
        current = pending.pop().resolve()
        if current in seen:
            continue
        seen.add(current)
        if not current.is_file():
            source_rows.append((str(current), "missing"))
            continue
        data = current.read_bytes()
        source_rows.append((str(current), digest(data)))
        for module in imports(data.decode("utf-8-sig", errors="replace")):
            relative = Path(*module.split("."))
            resolved = False
            for base in bases:
                source = base / relative.with_suffix(".lean")
                artifact = base / ".lake" / "build" / "lib" / "lean" / relative.with_suffix(".olean")
                if source.is_file() or artifact.is_file():
                    if source.is_file():
                        pending.append(source)
                    stat = artifact.stat() if artifact.exists() else None
                    if stat and source.is_file() and source.stat().st_mtime_ns > stat.st_mtime_ns:
                        stale_modules.add(module)
                    artifacts.append((str(artifact), [stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns]
                                      if stat else None))
                    resolved = True
                    break
            if not resolved:
                # Toolchain modules are identified by lean-toolchain below.
                artifacts.append((module, "toolchain-or-unresolved"))
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml",
                 "tools/lean_task_support.py", "tools/lean_auto.py", "tools/build_guard.ps1"):
        config = root / name
        source_rows.append((str(config), digest(config.read_bytes()) if config.exists() else None))
    source_stamp = json_digest(sorted(source_rows))
    return {"fingerprint": json_digest([VERSION, source_stamp, sorted(stale_modules), sorted(set(
                (name, json.dumps(stat)) for name, stat in artifacts))]),
            "source_stamp": source_stamp, "sha256": digest(file.read_bytes()),
            "source_count": len(seen), "stale_modules": sorted(stale_modules)[:8],
            "stale_module_count": len(stale_modules)}


def ps_quote(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def run_bounded(command: list[str], timeout: int, cwd: Path) -> subprocess.CompletedProcess:
    options = {"creationflags": subprocess.CREATE_NO_WINDOW} if os.name == "nt" else {"start_new_session": True}
    with subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, encoding="utf-8", errors="replace", **options) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        except subprocess.TimeoutExpired:
            if os.name == "nt":
                subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                               capture_output=True, timeout=20, creationflags=subprocess.CREATE_NO_WINDOW)
            else:
                os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate(timeout=20)
            return subprocess.CompletedProcess(command, 124, stdout, stderr + "\n[lean-auto-timeout]\n")


def guarded_run(command: list[str], runtime: Path, timeout: int = 900,
                wait_timeout: int = 180, root: Path = ROOT) -> dict:
    runtime.mkdir(parents=True, exist_ok=True)
    log = runtime / ("build-" + uuid.uuid4().hex + ".log")
    # Bound the child inside the guard: the guard survives timeout and releases its slot.
    child = [sys.executable, "-X", "utf8", "-B", str(Path(__file__).resolve()),
             "run", str(timeout), str(root), *command]
    shell_command = "& " + " ".join(ps_quote(part) for part in child)
    guard = ["pwsh", "-NoProfile", "-File", str(root / "tools" / "build_guard.ps1"),
             "-Command", shell_command, "-Log", str(log), "-WorkDir", str(root),
             "-WaitTimeoutSec", str(wait_timeout)]
    try:
        result = run_bounded(guard, timeout + wait_timeout + 60, root)
        output = log.read_text(encoding="utf-8-sig", errors="replace") if log.exists() else ""
        output += "\n" + result.stderr
        if "[lean-auto-timeout]" in output or result.returncode == 124:
            status = "timeout"
        elif "TIMEOUT waiting" in output:
            status = "resource_wait"
        elif not re.search(r"cmd exit=-?\d+", output):
            status = "infrastructure_error"
        else:
            status = "finished"
        return {"exit": result.returncode, "execution_status": status, "output": output, "log": str(log)}
    except (OSError, subprocess.SubprocessError) as exc:
        return {"exit": 2, "execution_status": "infrastructure_error", "output": str(exc), "log": str(log)}


if __name__ == "__main__":
    if len(sys.argv) < 5 or sys.argv[1] != "run":
        raise SystemExit("Internal usage: run TIMEOUT CWD COMMAND [ARGS...]")
    try:
        result = run_bounded(sys.argv[4:], int(sys.argv[2]), Path(sys.argv[3]))
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    except OSError as exc:
        print(f"[lean-auto-infrastructure] {exc}", file=sys.stderr)
        raise SystemExit(125)
