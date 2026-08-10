#!/usr/bin/env python3
"""Audit RawSources hashes against sources.lock.json."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, cast


DEFAULT_LOCK = "sources.lock.json"
DEFAULT_RAW_SOURCES = "RawSources"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def relative_posix(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def scan_raw_sources(root: Path, raw_sources: str) -> dict[str, dict[str, Any]]:
    raw_root = root / raw_sources
    if not raw_root.exists():
        raise ValueError(f"RawSources directory does not exist: {raw_root}")
    if not raw_root.is_dir():
        raise ValueError(f"RawSources path is not a directory: {raw_root}")

    records: dict[str, dict[str, Any]] = {}
    for path in sorted(raw_root.rglob("*")):
        if not path.is_file():
            continue
        rel_path = relative_posix(path, root)
        records[rel_path] = {
            "sha256": sha256_file(path),
            "size_bytes": path.stat().st_size,
        }
    return records


def load_lock(path: Path) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    if not path.is_file():
        raise ValueError(f"lock path exists but is not a file: {path}")

    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"lock file must contain a JSON object: {path}")

    normalized: dict[str, dict[str, Any]] = {}
    for key, value in data.items():
        if not isinstance(key, str) or not isinstance(value, dict):
            raise ValueError(f"invalid lock entry for key: {key!r}")
        normalized[key] = dict(value)
    return normalized


def max_source_number(lock: dict[str, dict[str, Any]]) -> int:
    max_seen = 0
    for record in lock.values():
        source_id = record.get("source_id")
        if not isinstance(source_id, str) or not source_id.startswith("S"):
            continue
        suffix = source_id[1:]
        if suffix.isdigit():
            max_seen = max(max_seen, int(suffix))
    return max_seen


def classify_drift(
    current: dict[str, dict[str, Any]],
    lock: dict[str, dict[str, Any]],
) -> dict[str, list[str] | list[tuple[str, str]]]:
    current_paths = set(current)
    locked_paths = set(lock)

    new = sorted(current_paths - locked_paths)
    missing = sorted(locked_paths - current_paths)
    hash_changed = sorted(
        path
        for path in current_paths & locked_paths
        if lock[path].get("sha256") != current[path]["sha256"]
    )

    current_by_hash = {
        record["sha256"]: path
        for path, record in current.items()
        if isinstance(record.get("sha256"), str)
    }
    possible_renames = sorted(
        (old_path, current_by_hash[lock[old_path]["sha256"]])
        for old_path in missing
        if isinstance(lock[old_path].get("sha256"), str)
        and lock[old_path]["sha256"] in current_by_hash
    )

    return {
        "new": new,
        "missing": missing,
        "hash_changed": hash_changed,
        "possible_renames": possible_renames,
    }


def merged_lock(
    current: dict[str, dict[str, Any]],
    old_lock: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    next_source_number = max_source_number(old_lock) + 1
    new_lock: dict[str, dict[str, Any]] = {
        key: dict(value) for key, value in old_lock.items()
    }

    for path in sorted(current):
        record = dict(new_lock.get(path, {}))
        record.update(
            {
                "sha256": current[path]["sha256"],
                "size_bytes": current[path]["size_bytes"],
            }
        )
        if "source_id" not in record:
            record["source_id"] = f"S{next_source_number:03d}"
            next_source_number += 1
        record.setdefault("type", "unknown")
        record.setdefault("provenance", "unknown")
        record.setdefault("supports", [])
        new_lock[path] = record

    return {key: new_lock[key] for key in sorted(new_lock)}


def print_section(title: str, values: list[str]) -> None:
    print(f"{title}: {len(values)}")
    for value in values:
        print(f"  - {value}")


def print_report(drift: dict[str, list[str] | list[tuple[str, str]]]) -> None:
    print_section("New sources", cast(list[str], drift["new"]))
    print_section("Missing locked sources", cast(list[str], drift["missing"]))
    print_section("Hash-changed sources", cast(list[str], drift["hash_changed"]))

    renames = cast(list[tuple[str, str]], drift["possible_renames"])
    print(f"Possible renames: {len(renames)}")
    for old_path, new_path in renames:
        print(f"  - {old_path} -> {new_path}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit RawSources/ hashes against a sources.lock.json file.",
    )
    parser.add_argument(
        "target",
        nargs="?",
        default=".",
        help="Research repository root. Defaults to the current directory.",
    )
    parser.add_argument(
        "--raw-sources",
        default=DEFAULT_RAW_SOURCES,
        help="Raw source directory relative to the repository root.",
    )
    parser.add_argument(
        "--lock",
        default=DEFAULT_LOCK,
        help="Lock file path relative to the repository root.",
    )
    parser.add_argument(
        "--write-lock",
        action="store_true",
        help="Write or update the lock file. This never modifies RawSources/.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.target).expanduser().resolve()
    lock_path = root / args.lock

    try:
        current = scan_raw_sources(root, args.raw_sources)
        old_lock = load_lock(lock_path)
        drift = classify_drift(current, old_lock)
        print_report(drift)

        if args.write_lock:
            new_lock = merged_lock(current, old_lock)
            lock_path.write_text(
                json.dumps(new_lock, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            print(f"Wrote lock file: {lock_path}")
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
