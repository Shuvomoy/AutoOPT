#!/usr/bin/env python3
"""Check Lean project hygiene and optionally run `lake build`.

The checker is intentionally conservative: it scans Lean source after removing
comments and strings, then rejects placeholder or unsafe constructs that would
invalidate a Lean-verification claim for this skill.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

FORBIDDEN = ("sorry", "axiom", "admit", "unsafe")
TOKEN_RE = re.compile(r"\b(" + "|".join(FORBIDDEN) + r")\b")


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    while i < len(text):
        c = text[i]
        nxt = text[i : i + 2]
        if in_line_comment:
            if c == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if nxt == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif nxt == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if in_string:
            if c == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if nxt == "--":
            in_line_comment = True
            out.extend("  ")
            i += 2
        elif nxt == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def lean_files(root: Path) -> list[Path]:
    skip = {".lake", ".git", ".elan", "__pycache__"}
    files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in skip]
        for name in filenames:
            if name.endswith(".lean"):
                files.append(Path(dirpath) / name)
    return sorted(files)


def scan_forbidden(root: Path) -> int:
    rc = 0
    files = lean_files(root)
    if not files:
        print(f"ERROR: no .lean files found under {root}", file=sys.stderr)
        return 1
    for path in files:
        raw = path.read_text(encoding="utf-8", errors="replace")
        stripped = strip_comments_and_strings(raw)
        for lineno, line in enumerate(stripped.splitlines(), start=1):
            match = TOKEN_RE.search(line)
            if match:
                print(f"ERROR: forbidden `{match.group(1)}` in {path}:{lineno}", file=sys.stderr)
                rc = 1
    if rc == 0:
        print(f"Lean hygiene scan passed for {len(files)} file(s).")
    return rc


def run_lake_build(root: Path, timeout: int) -> int:
    if not ((root / "lakefile.lean").exists() or (root / "lakefile.toml").exists()):
        print("ERROR: no lakefile.lean or lakefile.toml found; use --no-build for static scans.", file=sys.stderr)
        return 1
    print(f"Running `lake build` in {root} with timeout {timeout} seconds.")
    try:
        proc = subprocess.run(
            ["lake", "build"],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except FileNotFoundError:
        print("ERROR: `lake` not found on PATH.", file=sys.stderr)
        return 1
    except subprocess.TimeoutExpired as exc:
        if exc.stdout:
            print(exc.stdout, end="")
        print(f"ERROR: `lake build` timed out after {timeout} seconds.", file=sys.stderr)
        return 1
    print(proc.stdout, end="")
    if proc.returncode != 0:
        print(f"ERROR: `lake build` exited {proc.returncode}.", file=sys.stderr)
    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project_root", type=Path)
    parser.add_argument("--no-build", action="store_true", help="skip `lake build` and run only the static scan")
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    args = parser.parse_args()

    root = args.project_root.resolve()
    if not root.exists() or not root.is_dir():
        print(f"ERROR: project root does not exist or is not a directory: {root}", file=sys.stderr)
        return 1

    rc = scan_forbidden(root)
    if rc != 0 or args.no_build:
        return rc
    return run_lake_build(root, args.timeout_seconds)


if __name__ == "__main__":
    raise SystemExit(main())
