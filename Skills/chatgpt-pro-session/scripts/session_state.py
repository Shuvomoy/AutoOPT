#!/usr/bin/env python3
"""Manage ChatGPT Pro Session metadata.

This script intentionally does not control Chrome, upload files, or validate
ChatGPT artifacts. It only creates deterministic local JSON state for reusable
ChatGPT Pro conversations.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
REQUESTED_MODEL = "GPT-5.6 Sol with Intelligence set to Pro"


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def timestamp_id(prefix: str) -> str:
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    return f"{prefix}-{stamp}"


def resolve_path(value: str | None) -> str | None:
    if value is None:
        return None
    return str(Path(value).expanduser().resolve(strict=False))


def read_json(path: Path, default: Any | None = None) -> Any:
    if not path.exists():
        if default is not None:
            return default
        raise SystemExit(f"Missing JSON file: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Invalid JSON in {path}: {exc}") from exc


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def validate_chat_url(url: str) -> None:
    if not re.match(r"^https://chatgpt\.com(/|$)", url):
        raise SystemExit(f"ChatGPT URL must start with https://chatgpt.com/: {url}")


def session_path(handoff_dir: str | Path) -> Path:
    return Path(handoff_dir).expanduser().resolve(strict=False) / "session.json"


def load_session(handoff_dir: str | Path) -> dict[str, Any]:
    path = session_path(handoff_dir)
    session = read_json(path)
    if session.get("schema_version") != SCHEMA_VERSION:
        raise SystemExit(f"Unsupported session schema in {path}: {session.get('schema_version')}")
    return session


def save_session(session: dict[str, Any]) -> None:
    session["updated_at"] = utc_now()
    write_json(Path(session["handoff_dir"]) / "session.json", session)
    update_index(session)


def index_path(workspace: str | Path) -> Path:
    return Path(workspace).expanduser().resolve(strict=False) / ".chatgpt_handoffs" / "session-index.json"


def update_index(session: dict[str, Any]) -> None:
    workspace = Path(session["workspace"]).expanduser().resolve(strict=False)
    path = index_path(workspace)
    index = read_json(path, {"schema_version": SCHEMA_VERSION, "sessions": []})
    sessions = [item for item in index.get("sessions", []) if item.get("session_id") != session["session_id"]]
    sessions.append(
        {
            "session_id": session["session_id"],
            "handoff_dir": session["handoff_dir"],
            "chat_url": session["chat_url"],
            "source": session["source"],
            "status": session["status"],
            "updated_at": session["updated_at"],
            "workspace": session["workspace"],
        }
    )
    sessions.sort(key=lambda item: item.get("updated_at", ""))
    index["schema_version"] = SCHEMA_VERSION
    index["latest_session"] = session["session_id"]
    index["updated_at"] = utc_now()
    index["sessions"] = sessions
    write_json(path, index)


def make_context_snapshot(
    label: str,
    context_zip: str | None = None,
    manifest: str | None = None,
    prompt_file: str | None = None,
    note: str | None = None,
) -> dict[str, Any]:
    snapshot = {
        "label": label,
        "created_at": utc_now(),
        "context_zip": resolve_path(context_zip),
        "manifest": resolve_path(manifest),
        "prompt": resolve_path(prompt_file),
    }
    if note:
        snapshot["note"] = note
    return snapshot


def command_init(args: argparse.Namespace) -> None:
    validate_chat_url(args.chat_url)
    workspace = Path(args.workspace).expanduser().resolve(strict=False)
    handoff_dir = Path(args.handoff_dir).expanduser().resolve(strict=False)
    handoff_dir.mkdir(parents=True, exist_ok=True)
    path = handoff_dir / "session.json"
    if path.exists() and not args.replace:
        raise SystemExit(f"Session already exists: {path}. Use --replace to overwrite metadata.")

    now = utc_now()
    session = {
        "schema_version": SCHEMA_VERSION,
        "session_id": handoff_dir.name,
        "source": "created",
        "status": "active",
        "created_at": now,
        "updated_at": now,
        "workspace": str(workspace),
        "handoff_dir": str(handoff_dir),
        "chat_url": args.chat_url,
        "requested_model": args.requested_model,
        "context_snapshots": [
            make_context_snapshot(
                "initial",
                context_zip=args.context_zip,
                manifest=args.manifest,
                prompt_file=args.prompt_file,
                note=args.note,
            )
        ],
        "turns": [],
    }
    save_session(session)
    print(json.dumps({"session": str(path), "session_id": session["session_id"]}, indent=2, sort_keys=True))


def command_claim(args: argparse.Namespace) -> None:
    validate_chat_url(args.chat_url)
    workspace = Path(args.workspace).expanduser().resolve(strict=False)
    if args.handoff_dir:
        handoff_dir = Path(args.handoff_dir).expanduser().resolve(strict=False)
    else:
        handoff_dir = workspace / ".chatgpt_handoffs" / timestamp_id("claimed")
    handoff_dir.mkdir(parents=True, exist_ok=True)
    path = handoff_dir / "session.json"
    if path.exists() and not args.replace:
        raise SystemExit(f"Session already exists: {path}. Use --replace to overwrite metadata.")

    now = utc_now()
    snapshots: list[dict[str, Any]] = []
    if args.context_zip or args.manifest or args.prompt_file or args.note:
        snapshots.append(
            make_context_snapshot(
                "claimed-context",
                context_zip=args.context_zip,
                manifest=args.manifest,
                prompt_file=args.prompt_file,
                note=args.note,
            )
        )
    session = {
        "schema_version": SCHEMA_VERSION,
        "session_id": handoff_dir.name,
        "source": "claimed",
        "status": "active",
        "created_at": now,
        "updated_at": now,
        "workspace": str(workspace),
        "handoff_dir": str(handoff_dir),
        "chat_url": args.chat_url,
        "requested_model": args.requested_model,
        "context_snapshots": snapshots,
        "turns": [],
    }
    save_session(session)
    print(json.dumps({"session": str(path), "session_id": session["session_id"]}, indent=2, sort_keys=True))


def next_turn_id(session: dict[str, Any]) -> str:
    used = []
    for turn in session.get("turns", []):
        try:
            used.append(int(str(turn.get("id", "0"))))
        except ValueError:
            continue
    return f"{(max(used) if used else 0) + 1:03d}"


def write_prompt(turn_dir: Path, args: argparse.Namespace) -> str | None:
    prompt_path = turn_dir / "prompt.md"
    if args.prompt_file:
        source = Path(args.prompt_file).expanduser().resolve(strict=False)
        shutil.copyfile(source, prompt_path)
        return str(prompt_path)
    if args.prompt is not None:
        prompt_path.write_text(args.prompt.rstrip() + "\n", encoding="utf-8")
        return str(prompt_path)
    return None


def command_new_turn(args: argparse.Namespace) -> None:
    session = load_session(args.handoff_dir)
    turn_id = args.turn_id or next_turn_id(session)
    if any(str(turn.get("id")) == turn_id for turn in session.get("turns", [])):
        raise SystemExit(f"Turn already exists in session: {turn_id}")
    turn_dir = Path(session["handoff_dir"]) / "turns" / turn_id
    artifacts_dir = turn_dir / "artifacts"
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    prompt_path = write_prompt(turn_dir, args)
    turn = {
        "id": turn_id,
        "kind": args.kind,
        "status": "started",
        "created_at": utc_now(),
        "updated_at": utc_now(),
        "turn_dir": str(turn_dir),
        "artifacts_dir": str(artifacts_dir),
    }
    if prompt_path:
        turn["prompt"] = prompt_path
    if args.note:
        turn["note"] = args.note
    session.setdefault("turns", []).append(turn)
    save_session(session)
    print(json.dumps({"turn_id": turn_id, "turn_dir": str(turn_dir), "artifacts_dir": str(artifacts_dir)}, indent=2, sort_keys=True))


def parse_artifacts(values: list[str] | None) -> dict[str, str]:
    artifacts: dict[str, str] = {}
    for value in values or []:
        if "=" in value:
            key, path = value.split("=", 1)
            key = key.strip()
            if not key:
                raise SystemExit(f"Artifact key is empty: {value}")
        else:
            path = value
            key = Path(value).name
        artifacts[key] = resolve_path(path) or path
    return artifacts


def command_complete_turn(args: argparse.Namespace) -> None:
    session = load_session(args.handoff_dir)
    for turn in session.get("turns", []):
        if str(turn.get("id")) == args.turn_id:
            turn["status"] = args.status
            turn["updated_at"] = utc_now()
            if args.raw_response:
                turn["raw_response"] = resolve_path(args.raw_response)
            if args.response:
                turn["response"] = resolve_path(args.response)
            if args.response_import:
                turn["response_import"] = resolve_path(args.response_import)
            artifacts = parse_artifacts(args.artifact)
            if artifacts:
                turn.setdefault("artifacts", {}).update(artifacts)
            if args.note:
                turn["completion_note"] = args.note
            save_session(session)
            print(json.dumps({"turn_id": args.turn_id, "status": turn["status"]}, indent=2, sort_keys=True))
            return
    raise SystemExit(f"Turn not found: {args.turn_id}")


def command_add_context(args: argparse.Namespace) -> None:
    session = load_session(args.handoff_dir)
    label = args.label or f"context-{len(session.get('context_snapshots', [])) + 1}"
    snapshot = make_context_snapshot(
        label,
        context_zip=args.context_zip,
        manifest=args.manifest,
        prompt_file=args.prompt_file,
        note=args.note,
    )
    session.setdefault("context_snapshots", []).append(snapshot)
    save_session(session)
    print(json.dumps({"label": label, "session_id": session["session_id"]}, indent=2, sort_keys=True))


def command_show(args: argparse.Namespace) -> None:
    session = load_session(args.handoff_dir)
    if args.summary:
        data = {
            "session_id": session["session_id"],
            "source": session["source"],
            "status": session["status"],
            "chat_url": session["chat_url"],
            "handoff_dir": session["handoff_dir"],
            "turn_count": len(session.get("turns", [])),
            "context_snapshot_count": len(session.get("context_snapshots", [])),
            "updated_at": session["updated_at"],
        }
    else:
        data = session
    print(json.dumps(data, indent=2, sort_keys=True))


def command_latest(args: argparse.Namespace) -> None:
    path = index_path(args.workspace)
    index = read_json(path)
    latest_id = index.get("latest_session")
    for session in index.get("sessions", []):
        if session.get("session_id") == latest_id:
            print(json.dumps(session, indent=2, sort_keys=True))
            return
    raise SystemExit(f"Latest session not found in index: {path}")


def command_list(args: argparse.Namespace) -> None:
    path = index_path(args.workspace)
    index = read_json(path, {"schema_version": SCHEMA_VERSION, "sessions": []})
    print(json.dumps(index, indent=2, sort_keys=True))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Manage ChatGPT Pro Session metadata.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    common_model = argparse.ArgumentParser(add_help=False)
    common_model.add_argument("--requested-model", default=REQUESTED_MODEL)

    init = subparsers.add_parser("init", parents=[common_model], help="Create session metadata for a newly started Pro chat.")
    init.add_argument("--workspace", required=True)
    init.add_argument("--handoff-dir", required=True)
    init.add_argument("--chat-url", required=True)
    init.add_argument("--context-zip")
    init.add_argument("--manifest")
    init.add_argument("--prompt-file")
    init.add_argument("--note")
    init.add_argument("--replace", action="store_true")
    init.set_defaults(func=command_init)

    claim = subparsers.add_parser("claim", parents=[common_model], help="Claim an existing ChatGPT URL as a reusable session.")
    claim.add_argument("--workspace", required=True)
    claim.add_argument("--chat-url", required=True)
    claim.add_argument("--handoff-dir")
    claim.add_argument("--context-zip")
    claim.add_argument("--manifest")
    claim.add_argument("--prompt-file")
    claim.add_argument("--note")
    claim.add_argument("--replace", action="store_true")
    claim.set_defaults(func=command_claim)

    new_turn = subparsers.add_parser("new-turn", help="Create a new turn directory and metadata entry.")
    new_turn.add_argument("--handoff-dir", required=True)
    new_turn.add_argument("--kind", default="followup")
    new_turn.add_argument("--turn-id")
    prompt_group = new_turn.add_mutually_exclusive_group()
    prompt_group.add_argument("--prompt-file")
    prompt_group.add_argument("--prompt")
    new_turn.add_argument("--note")
    new_turn.set_defaults(func=command_new_turn)

    complete = subparsers.add_parser("complete-turn", help="Mark a turn complete and attach response paths.")
    complete.add_argument("--handoff-dir", required=True)
    complete.add_argument("--turn-id", required=True)
    complete.add_argument("--status", default="completed", choices=["completed", "invalid", "blocked", "superseded"])
    complete.add_argument("--raw-response")
    complete.add_argument("--response")
    complete.add_argument("--response-import")
    complete.add_argument("--artifact", action="append", help="Artifact path or key=path. Repeatable.")
    complete.add_argument("--note")
    complete.set_defaults(func=command_complete_turn)

    context = subparsers.add_parser("add-context", help="Record an additional context upload in the session.")
    context.add_argument("--handoff-dir", required=True)
    context.add_argument("--label")
    context.add_argument("--context-zip")
    context.add_argument("--manifest")
    context.add_argument("--prompt-file")
    context.add_argument("--note")
    context.set_defaults(func=command_add_context)

    show = subparsers.add_parser("show", help="Print session metadata.")
    show.add_argument("--handoff-dir", required=True)
    show.add_argument("--summary", action="store_true")
    show.set_defaults(func=command_show)

    latest = subparsers.add_parser("latest", help="Print the latest session entry for a workspace.")
    latest.add_argument("--workspace", required=True)
    latest.set_defaults(func=command_latest)

    list_cmd = subparsers.add_parser("list", help="Print the session index for a workspace.")
    list_cmd.add_argument("--workspace", required=True)
    list_cmd.set_defaults(func=command_list)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    args.func(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
