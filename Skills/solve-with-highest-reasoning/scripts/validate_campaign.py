#!/usr/bin/env python3
"""Validate a highest-reasoning campaign record without judging its mathematics."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timedelta
from pathlib import Path, PurePosixPath
from typing import Any


MINIMUM_HOURS = 8
MINIMUM_ACTIVE_SECONDS = 8 * 60 * 60
NONTERMINAL_STATUSES = {"prepared", "running", "paused"}
TERMINAL_STATUSES = {
    "complete",
    "incomplete",
    "user_stopped",
    "environment_blocked",
}
COUNTABLE_WORK_KINDS = {"research", "verification", "computation"}
EXCLUDED_WORK_KINDS = {"idle", "user_wait", "permission_wait"}
ROUND_KINDS = {"research", "rediversification", "audit", "repair"}
REQUIRED_AUDIT_SCOPES = {
    "dependency_quantifier_edge_case",
    "adversarial_counterexample_circularity",
}
PUBLIC_RETRIEVAL_CLASSES = {
    "ordinary_background",
    "standard_named_theorem",
}
PUBLIC_RETRIEVAL_BANNED_PATTERNS = (
    re.compile(r"\bexact[- ]target\b", re.IGNORECASE),
    re.compile(r"\bexact[- ]problem\b", re.IGNORECASE),
    re.compile(r"\bproblem[- ]solution\b", re.IGNORECASE),
    re.compile(
        r"\bsolution\s+(?:to|of|for)\s+(?:(?:the|this|our|exact)\s+)?"
        r"(?:problem|target|benchmark|conjecture)\b",
        re.IGNORECASE,
    ),
    re.compile(r"\bopen[- ]status\b", re.IGNORECASE),
    re.compile(r"\bopen\s+problem\b", re.IGNORECASE),
    re.compile(
        r"\b(?:problem|target|benchmark|conjecture)\b.{0,40}"
        r"\bknown\s+to\s+be\s+(?:open|closed|solved)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\bwhether\b.{0,80}\b(?:problem|target|benchmark|conjecture)\b"
        r".{0,40}\b(?:open|closed|solved)\b",
        re.IGNORECASE,
    ),
)
CLAIM_STATUSES = {
    "Proven",
    "Derivation checked",
    "Computed",
    "Literature",
    "Conjectured",
    "Refuted",
    "Needs check",
}
REQUIRED_FILES = {
    "campaign.yaml",
    "problem-contract.md",
    "source-manifest.md",
    "approach-registry.md",
    "claim-ledger.md",
    "audit-log.md",
    "reproducibility.md",
    "final-report.md",
    "work-intervals.jsonl",
    "agent-runs.jsonl",
    "rounds.jsonl",
    "audits.jsonl",
}
REQUIRED_DIRECTORIES = {"checkpoints", "artifacts"}
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
REQUESTED_CAPABILITY_POLICY = (
    "strongest available Codex GPT and that model's highest supported "
    "reasoning setting"
)
PUBLIC_SEARCH_POLICY = (
    "background-and-standard-named-theorems-only; "
    "no exact-target, solution, or open-status retrieval"
)
LOCAL_SOURCE_POLICY = "allowed, including exact-target repository material"
EXTERNAL_CONSULTATION_POLICY = "disabled without separate user authorization"


class ValidationFailure(RuntimeError):
    """Raised for an unreadable campaign input."""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Validate a highest-reasoning campaign protocol record."
    )
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument(
        "--allow-incomplete",
        action="store_true",
        help="Allow a nonterminal prepared/running/paused checkpoint.",
    )
    return parser.parse_args()


def parse_scalar(text: str, line_number: int) -> Any:
    stripped = text.strip()
    if stripped == "":
        return ""
    if stripped[0] in '"[{' or stripped in {"true", "false", "null"}:
        try:
            return json.loads(stripped)
        except json.JSONDecodeError as exc:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: invalid JSON-compatible scalar: {exc}"
            ) from exc
    if re.fullmatch(r"-?[0-9]+", stripped):
        return int(stripped)
    if re.fullmatch(r"-?[0-9]+\.[0-9]+", stripped):
        return float(stripped)
    return stripped


def parse_simple_yaml(path: Path) -> dict[str, Any]:
    """Parse the deliberately small mapping-only YAML subset used by the template."""
    root: dict[str, Any] = {}
    stack: list[tuple[int, dict[str, Any]]] = [(-2, root)]
    for line_number, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not raw_line.strip() or raw_line.lstrip().startswith("#"):
            continue
        if "\t" in raw_line:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: tabs are not permitted"
            )
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        if indent % 2:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: indentation must use multiples of 2"
            )
        content = raw_line.strip()
        if ":" not in content:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: expected a key-value mapping"
            )
        key, value_text = content.split(":", 1)
        key = key.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: invalid key {key!r}"
            )
        while stack[-1][0] >= indent:
            stack.pop()
        parent_indent, parent = stack[-1]
        if indent > parent_indent + 2:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: indentation skips a mapping level"
            )
        if key in parent:
            raise ValidationFailure(
                f"campaign.yaml:{line_number}: duplicate key {key!r}"
            )
        if value_text.strip() == "":
            child: dict[str, Any] = {}
            parent[key] = child
            stack.append((indent, child))
        else:
            parent[key] = parse_scalar(value_text, line_number)
    return root


def nested(data: dict[str, Any], dotted_key: str, errors: list[str]) -> Any:
    current: Any = data
    for component in dotted_key.split("."):
        if not isinstance(current, dict) or component not in current:
            errors.append(f"campaign.yaml is missing {dotted_key}")
            return None
        current = current[component]
    return current


def parse_datetime(value: Any, label: str, errors: list[str]) -> datetime | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{label} must be a nonempty ISO-8601 timestamp")
        return None
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        errors.append(f"{label} is not a valid ISO-8601 timestamp: {value!r}")
        return None
    if parsed.tzinfo is None or parsed.utcoffset() is None:
        errors.append(f"{label} must include a time-zone offset")
        return None
    return parsed


def safe_relative_path(value: Any, label: str, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{label} must be a nonempty relative path")
        return None
    pure = PurePosixPath(value)
    if pure.is_absolute() or ".." in pure.parts:
        errors.append(f"{label} must not be absolute or contain '..': {value!r}")
        return None
    return Path(*pure.parts)


def confined_path(
    run_dir: Path,
    value: Any,
    label: str,
    errors: list[str],
) -> Path | None:
    relative = safe_relative_path(value, label, errors)
    if relative is None:
        return None
    candidate = run_dir / relative
    resolved = candidate.resolve(strict=False)
    try:
        resolved.relative_to(run_dir)
    except ValueError:
        errors.append(f"{label} resolves outside the campaign directory")
        return None
    return candidate


def require_namespaced_id(
    value: Any,
    field: str,
    label: str,
    run_id: str | None,
    errors: list[str],
) -> bool:
    if not isinstance(value, str) or not value:
        errors.append(f"{label}: {field} must be nonempty")
        return False
    if run_id is not None and not value.startswith(f"{run_id}:"):
        errors.append(
            f"{label}: {field} must start with the run namespace {run_id!r} followed by ':'"
        )
        return False
    return True


def load_jsonl(path: Path, errors: list[str]) -> list[tuple[int, dict[str, Any]]]:
    records: list[tuple[int, dict[str, Any]]] = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not raw_line.strip():
            continue
        try:
            value = json.loads(raw_line)
        except json.JSONDecodeError as exc:
            errors.append(f"{path.name}:{line_number}: invalid JSON: {exc}")
            continue
        if not isinstance(value, dict):
            errors.append(f"{path.name}:{line_number}: each line must be an object")
            continue
        records.append((line_number, value))
    return records


def require_fields(
    record: dict[str, Any],
    fields: tuple[str, ...],
    label: str,
    errors: list[str],
) -> bool:
    missing = [field for field in fields if field not in record]
    if missing:
        errors.append(f"{label} is missing fields: {', '.join(missing)}")
        return False
    return True


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_required_tree(run_dir: Path, errors: list[str]) -> None:
    for filename in sorted(REQUIRED_FILES):
        path = run_dir / filename
        if not path.is_file():
            errors.append(f"missing required file: {filename}")
            continue
        try:
            path.resolve(strict=True).relative_to(run_dir)
        except ValueError:
            errors.append(f"required file resolves outside campaign: {filename}")
    for dirname in sorted(REQUIRED_DIRECTORIES):
        path = run_dir / dirname
        if not path.is_dir():
            errors.append(f"missing required directory: {dirname}/")
            continue
        try:
            path.resolve(strict=True).relative_to(run_dir)
        except ValueError:
            errors.append(f"required directory resolves outside campaign: {dirname}/")


def validate_identity(
    data: dict[str, Any], run_dir: Path, errors: list[str]
) -> tuple[Path | None, str | None]:
    schema_version = nested(data, "schema_version", errors)
    run_id = nested(data, "run_id", errors)
    repository_root_value = nested(data, "repository_root", errors)
    run_directory_value = nested(data, "run_directory", errors)
    if schema_version != 1:
        errors.append("schema_version must equal 1")
    expected_run_id = "hr-" + run_dir.name
    if not isinstance(run_id, str) or run_id != expected_run_id:
        errors.append(
            f"run_id must exactly match the campaign directory: {expected_run_id!r}"
        )
        run_id = None
    repository_root: Path | None = None
    if isinstance(repository_root_value, str) and repository_root_value:
        repository_root = Path(repository_root_value).expanduser().resolve()
        if not repository_root.is_dir():
            errors.append("repository_root does not resolve to a directory")
    else:
        errors.append("repository_root must be a nonempty path")
    if not isinstance(run_directory_value, str) or not run_directory_value:
        errors.append("run_directory must be a nonempty path")
    elif Path(run_directory_value).expanduser().resolve() != run_dir:
        errors.append("run_directory does not match --run-dir")
    if repository_root is not None:
        expected_parent = (
            repository_root / "ResearchLog" / "highest-reasoning-runs"
        ).resolve()
        if run_dir.parent != expected_parent:
            errors.append(
                "run directory is not under "
                "ResearchLog/highest-reasoning-runs in repository_root"
            )
        if "RawSources" in run_dir.parts:
            errors.append("run directory must not be inside RawSources")
    return repository_root, run_id


def validate_capability(
    data: dict[str, Any],
    run_dir: Path,
    status: str | None,
    errors: list[str],
) -> tuple[str | None, str | None, str | None, int | None, int | None]:
    requested = nested(data, "capability.requested_policy", errors)
    models = nested(data, "capability.available_models", errors)
    resolved_model = nested(
        data, "capability.resolved_strongest_model", errors
    )
    selected_model = nested(data, "capability.selected_model", errors)
    reasoning_values = nested(
        data, "capability.available_reasoning_for_selected_model", errors
    )
    resolved_reasoning = nested(
        data, "capability.resolved_highest_reasoning", errors
    )
    selected_reasoning = nested(data, "capability.selected_reasoning", errors)
    source = nested(data, "capability.capability_source", errors)
    model_basis = nested(data, "capability.model_selection_basis", errors)
    reasoning_basis = nested(data, "capability.reasoning_selection_basis", errors)
    evidence_value = nested(data, "capability.evidence_artifact", errors)
    evidence_hash = nested(data, "capability.evidence_sha256", errors)
    verified = nested(data, "capability.verified", errors)
    available = nested(data, "capability.available_concurrency", errors)
    peak = nested(data, "capability.peak_concurrency", errors)
    downgrade = nested(data, "capability.downgrade", errors)

    if requested != REQUESTED_CAPABILITY_POLICY:
        errors.append("capability.requested_policy differs from the highest policy")
    if downgrade != "none":
        errors.append("capability.downgrade must be 'none'; silent fallback is forbidden")

    strict = status in (NONTERMINAL_STATUSES - {"prepared"}) | TERMINAL_STATUSES
    if strict:
        if not isinstance(models, list) or not all(
            isinstance(item, str) and item for item in models
        ):
            errors.append("capability.available_models must be a nonempty string list")
        if not isinstance(selected_model, str) or not selected_model:
            errors.append("capability.selected_model must be nonempty")
        elif isinstance(models, list) and selected_model not in models:
            errors.append("selected_model is not present in available_models")
        if not isinstance(resolved_model, str) or not resolved_model:
            errors.append("capability.resolved_strongest_model must be nonempty")
        elif resolved_model != selected_model:
            errors.append(
                "selected_model differs from resolved_strongest_model"
            )
        if not isinstance(reasoning_values, list) or not all(
            isinstance(item, str) and item for item in reasoning_values
        ):
            errors.append(
                "available_reasoning_for_selected_model must be a nonempty string list"
            )
        if not isinstance(selected_reasoning, str) or not selected_reasoning:
            errors.append("capability.selected_reasoning must be nonempty")
        elif (
            isinstance(reasoning_values, list)
            and selected_reasoning not in reasoning_values
        ):
            errors.append(
                "selected_reasoning is not present in "
                "available_reasoning_for_selected_model"
            )
        if not isinstance(resolved_reasoning, str) or not resolved_reasoning:
            errors.append(
                "capability.resolved_highest_reasoning must be nonempty"
            )
        elif resolved_reasoning != selected_reasoning:
            errors.append(
                "selected_reasoning differs from resolved_highest_reasoning"
            )
        if not isinstance(source, str) or not source:
            errors.append("capability.capability_source must be nonempty")
        if not isinstance(model_basis, str) or not model_basis.strip():
            errors.append("capability.model_selection_basis must be nonempty")
        if not isinstance(reasoning_basis, str) or not reasoning_basis.strip():
            errors.append("capability.reasoning_selection_basis must be nonempty")
        evidence_path = confined_path(
            run_dir,
            evidence_value,
            "capability.evidence_artifact",
            errors,
        )
        if evidence_path is not None:
            if not evidence_path.is_file():
                errors.append("capability.evidence_artifact does not exist")
            else:
                try:
                    evidence_record = json.loads(
                        evidence_path.read_text(encoding="utf-8")
                    )
                except (OSError, UnicodeError, json.JSONDecodeError):
                    errors.append(
                        "capability.evidence_artifact must be readable JSON"
                    )
                else:
                    if not isinstance(evidence_record, dict):
                        errors.append(
                            "capability.evidence_artifact must contain a JSON object"
                        )
                    else:
                        expected_evidence = {
                            "schema_version": 1,
                            "verification_mode": verified,
                            "available_models": models,
                            "resolved_strongest_model": resolved_model,
                            "selected_model": selected_model,
                            "available_reasoning_for_selected_model": reasoning_values,
                            "resolved_highest_reasoning": resolved_reasoning,
                            "selected_reasoning": selected_reasoning,
                            "capability_source": source,
                            "model_selection_basis": model_basis,
                            "reasoning_selection_basis": reasoning_basis,
                        }
                        for field, expected in expected_evidence.items():
                            if evidence_record.get(field) != expected:
                                errors.append(
                                    "capability evidence field "
                                    f"{field!r} differs from campaign.yaml"
                                )
                        captured_at = parse_datetime(
                            evidence_record.get("captured_at"),
                            "capability.evidence_artifact.captured_at",
                            errors,
                        )
                        campaign_started = parse_datetime(
                            nested(data, "started_at", errors),
                            "started_at",
                            errors,
                        )
                        if (
                            captured_at is not None
                            and captured_at > datetime.now().astimezone()
                        ):
                            errors.append(
                                "capability evidence captured_at lies in the future"
                            )
                        if (
                            captured_at is not None
                            and campaign_started is not None
                            and captured_at > campaign_started
                        ):
                            errors.append(
                                "capability evidence must be captured no later "
                                "than campaign start"
                            )
                        selection_evidence = evidence_record.get(
                            "selection_evidence"
                        )
                        if (
                            not isinstance(selection_evidence, str)
                            or len(selection_evidence.split()) < 8
                        ):
                            errors.append(
                                "capability selection_evidence must be substantive"
                            )
                        else:
                            lowered_evidence = selection_evidence.lower()
                            for label, selected in (
                                ("model", selected_model),
                                ("reasoning", selected_reasoning),
                            ):
                                if (
                                    not isinstance(selected, str)
                                    or selected.lower() not in lowered_evidence
                                ):
                                    errors.append(
                                        "capability selection_evidence does not "
                                        f"identify the selected {label}"
                                    )
                            provenance_tokens = (
                                ("runtime", "host")
                                if verified == "runtime_verified"
                                else ("user",)
                            )
                            if not any(
                                token in lowered_evidence
                                for token in provenance_tokens
                            ):
                                errors.append(
                                    "capability selection_evidence does not "
                                    "identify its verification provenance"
                                )
                if not isinstance(evidence_hash, str) or not SHA256_RE.fullmatch(
                    evidence_hash
                ):
                    errors.append(
                        "capability.evidence_sha256 must be lowercase SHA-256"
                    )
                elif evidence_hash != sha256_file(evidence_path):
                    errors.append(
                        "capability.evidence_sha256 does not match its artifact"
                    )
        if not isinstance(verified, str) or verified not in {
            "runtime_verified",
            "user_selected",
        }:
            errors.append(
                "capability.verified must be runtime_verified or user_selected"
            )
        if not isinstance(available, int) or isinstance(available, bool) or available < 1:
            errors.append("available_concurrency must be a positive integer")
        if not isinstance(peak, int) or isinstance(peak, bool) or peak < 0:
            errors.append("peak_concurrency must be a nonnegative integer")
        elif isinstance(available, int) and peak > available:
            errors.append("peak_concurrency exceeds available_concurrency")
    return (
        selected_model if isinstance(selected_model, str) else None,
        selected_reasoning if isinstance(selected_reasoning, str) else None,
        verified if isinstance(verified, str) else None,
        available if isinstance(available, int) and not isinstance(available, bool) else None,
        peak if isinstance(peak, int) and not isinstance(peak, bool) else None,
    )


def validate_policies(data: dict[str, Any], errors: list[str]) -> None:
    public = nested(data, "policies.public_search", errors)
    local = nested(data, "policies.local_sources", errors)
    external = nested(data, "policies.external_consultation", errors)
    max_execution_minutes = nested(
        data, "policies.max_execution_minutes", errors
    )
    if public != PUBLIC_SEARCH_POLICY:
        errors.append("policies.public_search differs from the approved restriction")
    if local != LOCAL_SOURCE_POLICY:
        errors.append("policies.local_sources differs from the approved allowance")
    if external != EXTERNAL_CONSULTATION_POLICY:
        errors.append("policies.external_consultation differs from the approval gate")
    if max_execution_minutes != 180:
        errors.append("policies.max_execution_minutes must equal 180")


def validate_work_intervals(
    records: list[tuple[int, dict[str, Any]]],
    run_dir: Path,
    run_id: str | None,
    data: dict[str, Any],
    errors: list[str],
) -> tuple[int, int, list[tuple[datetime, datetime, int]]]:
    seen_ids: set[str] = set()
    parsed: list[tuple[datetime, datetime, int, str, int]] = []
    for line_number, record in records:
        label = f"work-intervals.jsonl:{line_number}"
        if not require_fields(
            record,
            (
                "interval_id",
                "started_at",
                "ended_at",
                "duration_seconds",
                "kind",
                "checkpoint",
            ),
            label,
            errors,
        ):
            continue
        interval_id = record["interval_id"]
        valid_id = require_namespaced_id(
            interval_id, "interval_id", label, run_id, errors
        )
        if valid_id and interval_id in seen_ids:
            errors.append(f"{label}: duplicate interval_id {interval_id!r}")
        elif valid_id:
            seen_ids.add(interval_id)
        started = parse_datetime(record["started_at"], f"{label}.started_at", errors)
        ended = parse_datetime(record["ended_at"], f"{label}.ended_at", errors)
        duration = record["duration_seconds"]
        kind = record["kind"]
        if (
            not isinstance(duration, int)
            or isinstance(duration, bool)
            or duration <= 0
        ):
            errors.append(f"{label}: duration_seconds must be a positive integer")
            continue
        if not isinstance(kind, str) or kind not in (
            COUNTABLE_WORK_KINDS | EXCLUDED_WORK_KINDS
        ):
            errors.append(f"{label}: unsupported work kind {kind!r}")
            continue
        checkpoint = confined_path(
            run_dir,
            record["checkpoint"],
            f"{label}.checkpoint",
            errors,
        )
        if checkpoint is not None:
            try:
                checkpoint.resolve(strict=False).relative_to(
                    (run_dir / "checkpoints").resolve(strict=True)
                )
            except ValueError:
                errors.append(
                    f"{label}: checkpoint must resolve inside checkpoints/"
                )
        if checkpoint is not None and not (run_dir / checkpoint).is_file():
            errors.append(
                f"{label}: checkpoint file does not exist: "
                f"{record['checkpoint']!r}"
            )
        if started is None or ended is None:
            continue
        elapsed = ended - started
        if elapsed <= timedelta(0):
            errors.append(f"{label}: ended_at must be later than started_at")
            continue
        if elapsed != timedelta(seconds=duration):
            errors.append(
                f"{label}: duration_seconds={duration} but timestamps imply "
                f"{elapsed.total_seconds()}"
            )
        parsed.append((started, ended, duration, kind, line_number))

    parsed.sort(key=lambda item: (item[0], item[1]))
    for previous, current in zip(parsed, parsed[1:]):
        if current[0] < previous[1]:
            errors.append(
                "work intervals overlap: "
                f"lines {previous[4]} and {current[4]} in work-intervals.jsonl"
            )
    active = sum(
        duration for _, _, duration, kind, _ in parsed if kind in COUNTABLE_WORK_KINDS
    )
    paused = sum(
        duration for _, _, duration, kind, _ in parsed if kind in EXCLUDED_WORK_KINDS
    )
    declared_active = nested(data, "timing.active_work_seconds", errors)
    declared_paused = nested(data, "timing.paused_seconds", errors)
    if declared_active != active:
        errors.append(
            f"timing.active_work_seconds={declared_active!r} but intervals sum to {active}"
        )
    if declared_paused != paused:
        errors.append(
            f"timing.paused_seconds={declared_paused!r} but intervals sum to {paused}"
        )
    interval_bounds = [(started, ended, line) for started, ended, _, _, line in parsed]
    return active, paused, interval_bounds


def validate_rounds(
    records: list[tuple[int, dict[str, Any]]],
    run_dir: Path,
    run_id: str | None,
    data: dict[str, Any],
    status: str | None,
    errors: list[str],
) -> list[tuple[datetime, datetime, int]]:
    seen_ids: set[str] = set()
    seen_sequences: set[int] = set()
    parsed: list[dict[str, Any]] = []
    for line_number, record in records:
        label = f"rounds.jsonl:{line_number}"
        if not require_fields(
            record,
            (
                "round_id",
                "sequence",
                "kind",
                "started_at",
                "ended_at",
                "materially_productive",
                "terminal_obstruction_survived",
                "obstruction_id",
                "defensible_next_step",
                "material_result",
                "evidence_artifact",
            ),
            label,
            errors,
        ):
            continue
        round_id = record["round_id"]
        valid_round_id = require_namespaced_id(
            round_id, "round_id", label, run_id, errors
        )
        if valid_round_id and round_id in seen_ids:
            errors.append(f"{label}: duplicate round_id {round_id!r}")
        elif valid_round_id:
            seen_ids.add(round_id)
        sequence = record["sequence"]
        if (
            not isinstance(sequence, int)
            or isinstance(sequence, bool)
            or sequence < 1
        ):
            errors.append(f"{label}: sequence must be a positive integer")
            continue
        if sequence in seen_sequences:
            errors.append(f"{label}: duplicate sequence {sequence}")
        seen_sequences.add(sequence)
        if not isinstance(record["kind"], str) or record["kind"] not in ROUND_KINDS:
            errors.append(f"{label}: unsupported round kind {record['kind']!r}")
        for field in (
            "materially_productive",
            "terminal_obstruction_survived",
            "defensible_next_step",
        ):
            if not isinstance(record[field], bool):
                errors.append(f"{label}: {field} must be boolean")
        obstruction_id = record["obstruction_id"]
        if record["terminal_obstruction_survived"] is True:
            require_namespaced_id(
                obstruction_id, "obstruction_id", label, run_id, errors
            )
        elif not isinstance(obstruction_id, str):
            errors.append(f"{label}: obstruction_id must be a string")
        if not isinstance(record["material_result"], str) or not record[
            "material_result"
        ].strip():
            errors.append(f"{label}: material_result must be nonempty")
        evidence_path = confined_path(
            run_dir,
            record["evidence_artifact"],
            f"{label}.evidence_artifact",
            errors,
        )
        if evidence_path is not None and not evidence_path.is_file():
            errors.append(f"{label}: evidence_artifact does not exist")
        started = parse_datetime(
            record["started_at"], f"{label}.started_at", errors
        )
        ended = parse_datetime(record["ended_at"], f"{label}.ended_at", errors)
        if started is None or ended is None:
            continue
        if ended <= started:
            errors.append(f"{label}: ended_at must be later than started_at")
            continue
        parsed.append(
            {
                **record,
                "_line_number": line_number,
                "_started_at": started,
                "_ended_at": ended,
            }
        )

    parsed.sort(key=lambda record: record["sequence"])
    if parsed:
        sequences = [record["sequence"] for record in parsed]
        if sequences != list(range(1, len(sequences) + 1)):
            errors.append("rounds.jsonl sequence values must be consecutive from 1")
        for previous, current in zip(parsed, parsed[1:]):
            if current["_started_at"] < previous["_ended_at"]:
                errors.append(
                    "rounds overlap or are out of chronological order: "
                    f"lines {previous['_line_number']} and {current['_line_number']}"
                )

    earliest = parse_datetime(
        nested(data, "earliest_finalization_at", errors),
        "earliest_finalization_at",
        errors,
    )
    after_minimum = (
        [
            record
            for record in parsed
            if earliest is not None and record["_started_at"] >= earliest
        ]
        if earliest is not None
        else []
    )
    productive_count = sum(
        record["materially_productive"] is True for record in after_minimum
    )
    declared_productive = nested(
        data, "timing.productive_rounds_after_minimum", errors
    )
    if declared_productive != productive_count:
        errors.append(
            "timing.productive_rounds_after_minimum="
            f"{declared_productive!r} but rounds.jsonl implies {productive_count}"
        )

    final_obstruction_id = nested(
        data, "status.terminal_obstruction_id", errors
    )
    suffix_count = 0
    for record in reversed(after_minimum):
        if not (
            isinstance(final_obstruction_id, str)
            and final_obstruction_id
            and record["terminal_obstruction_survived"] is True
            and record["obstruction_id"] == final_obstruction_id
            and record["materially_productive"] is False
            and record["defensible_next_step"] is False
            and isinstance(record["kind"], str)
            and record["kind"] in {"rediversification", "audit"}
        ):
            break
        suffix_count += 1
    declared_terminal_rounds = nested(
        data, "timing.terminal_obstruction_rounds", errors
    )
    if declared_terminal_rounds != suffix_count:
        errors.append(
            "timing.terminal_obstruction_rounds="
            f"{declared_terminal_rounds!r} but the qualifying suffix has "
            f"{suffix_count} rounds"
        )
    if status == "incomplete" and suffix_count < 3:
        errors.append(
            "incomplete status requires three consecutive post-minimum "
            "rediversification or audit rounds with the same obstruction"
        )
    return [
        (record["_started_at"], record["_ended_at"], record["_line_number"])
        for record in parsed
    ]


def validate_agent_runs(
    records: list[tuple[int, dict[str, Any]]],
    run_id: str | None,
    selected_model: str | None,
    selected_reasoning: str | None,
    campaign_verification: str | None,
    declared_peak: int | None,
    available: int | None,
    status: str | None,
    errors: list[str],
) -> tuple[
    dict[str, dict[str, Any]],
    int,
    list[tuple[datetime, datetime, str, int]],
]:
    agents: dict[str, dict[str, Any]] = {}
    seen_context_ids: set[str] = set()
    intervals: list[tuple[datetime, datetime, str, int]] = []
    for line_number, record in records:
        label = f"agent-runs.jsonl:{line_number}"
        if not require_fields(
            record,
            (
                "agent_id",
                "context_id",
                "wave_id",
                "role",
                "actual_model",
                "actual_reasoning",
                "capability_provenance",
                "verification_mode",
                "fresh_context",
                "started_at",
                "ended_at",
            ),
            label,
            errors,
        ):
            continue
        agent_id = record["agent_id"]
        if not require_namespaced_id(
            agent_id, "agent_id", label, run_id, errors
        ):
            continue
        if agent_id in agents:
            errors.append(f"{label}: duplicate agent_id {agent_id!r}")
            continue
        for field in ("context_id", "wave_id"):
            require_namespaced_id(record[field], field, label, run_id, errors)
        context_id = record["context_id"]
        if isinstance(context_id, str) and context_id:
            if context_id in seen_context_ids:
                errors.append(f"{label}: duplicate context_id {context_id!r}")
            else:
                seen_context_ids.add(context_id)
        for field in ("role", "capability_provenance"):
            if not isinstance(record[field], str) or not record[field].strip():
                errors.append(f"{label}: {field} must be a nonempty string")
        if record["actual_model"] != selected_model:
            errors.append(f"{label}: actual_model differs from selected_model")
        if record["actual_reasoning"] != selected_reasoning:
            errors.append(f"{label}: actual_reasoning differs from selected_reasoning")
        if not isinstance(record["verification_mode"], str) or record[
            "verification_mode"
        ] not in {
            "runtime_verified",
            "user_selected",
        }:
            errors.append(f"{label}: invalid verification_mode")
        elif record["verification_mode"] != campaign_verification:
            errors.append(
                f"{label}: verification_mode differs from capability.verified"
            )
        if not isinstance(record["fresh_context"], bool):
            errors.append(f"{label}: fresh_context must be boolean")
        started = parse_datetime(record["started_at"], f"{label}.started_at", errors)
        ended = parse_datetime(record["ended_at"], f"{label}.ended_at", errors)
        if started is not None and ended is not None:
            if ended <= started:
                errors.append(f"{label}: ended_at must be later than started_at")
            else:
                intervals.append((started, ended, agent_id, line_number))
        stored_record = dict(record)
        stored_record["_parsed_started_at"] = started
        stored_record["_parsed_ended_at"] = ended
        agents[agent_id] = stored_record

    events: list[tuple[datetime, int]] = []
    for started, ended, _, _ in intervals:
        events.append((started, 1))
        events.append((ended, -1))
    current = 0
    computed_peak = 0
    for _, delta in sorted(events, key=lambda item: (item[0], item[1])):
        current += delta
        computed_peak = max(computed_peak, current)
    if declared_peak is not None and declared_peak != computed_peak:
        errors.append(
            f"capability.peak_concurrency={declared_peak} "
            f"but agent intervals imply {computed_peak}"
        )
    if available is not None and computed_peak > available:
        errors.append("agent intervals exceed available_concurrency")
    if status in {"complete", "incomplete"} and not agents:
        errors.append("voluntary terminal campaigns require agent-runs evidence")
    if status in {"complete", "incomplete"} and agents and not any(
        "root" in str(record.get("role", "")).lower()
        for record in agents.values()
    ):
        errors.append(
            "voluntary terminal campaigns require a root-orchestrator agent record"
        )
    return agents, computed_peak, intervals


def validate_audits(
    records: list[tuple[int, dict[str, Any]]],
    agents: dict[str, dict[str, Any]],
    run_dir: Path,
    run_id: str | None,
    data: dict[str, Any],
    status: str | None,
    errors: list[str],
) -> int:
    required = nested(data, "audits.required_fresh", errors)
    declared_completed = nested(data, "audits.completed_fresh", errors)
    if not isinstance(required, int) or isinstance(required, bool) or required < 2:
        errors.append("audits.required_fresh must be an integer of at least 2")
        required = 2

    final_candidate_version = nested(data, "completion.candidate_version", errors)
    final_candidate_artifact = nested(
        data, "completion.candidate_artifact", errors
    )
    final_candidate_hash = nested(data, "completion.candidate_sha256", errors)
    final_contract_version = nested(data, "completion.contract_version", errors)
    final_contract_hash = nested(data, "completion.contract_sha256", errors)
    repair_value = nested(data, "completion.last_material_repair_at", errors)
    repair_time = (
        parse_datetime(
            repair_value,
            "completion.last_material_repair_at",
            errors,
        )
        if repair_value
        else None
    )

    seen_audit_ids: set[str] = set()
    qualifying: list[tuple[str, str, str]] = []
    for line_number, record in records:
        label = f"audits.jsonl:{line_number}"
        if not require_fields(
            record,
            (
                "audit_id",
                "auditor_id",
                "context_id",
                "authoring_involvement",
                "candidate_version",
                "candidate_sha256",
                "candidate_artifact",
                "contract_version",
                "contract_sha256",
                "audit_scope",
                "outcome",
                "completed_at",
                "last_material_repair_at",
                "audit_artifact",
            ),
            label,
            errors,
        ):
            continue
        audit_id = record["audit_id"]
        valid_audit_id = require_namespaced_id(
            audit_id, "audit_id", label, run_id, errors
        )
        if valid_audit_id and audit_id in seen_audit_ids:
            errors.append(f"{label}: duplicate audit_id {audit_id!r}")
        elif valid_audit_id:
            seen_audit_ids.add(audit_id)
        auditor_id = record["auditor_id"]
        context_id = record["context_id"]
        require_namespaced_id(
            auditor_id, "auditor_id", label, run_id, errors
        )
        require_namespaced_id(
            context_id, "context_id", label, run_id, errors
        )
        agent = agents.get(auditor_id) if isinstance(auditor_id, str) else None
        if agent is None:
            errors.append(f"{label}: auditor_id has no matching agent-runs record")
        else:
            if agent.get("context_id") != context_id:
                errors.append(f"{label}: context_id differs from agent-runs record")
            if agent.get("fresh_context") is not True:
                errors.append(f"{label}: auditor must use a fresh context")
            if "audit" not in str(agent.get("role", "")).lower():
                errors.append(f"{label}: matching agent role must identify an auditor")
        if record["authoring_involvement"] is not False:
            errors.append(f"{label}: authoring_involvement must be false")
        audit_scope = record["audit_scope"]
        if (
            not isinstance(audit_scope, str)
            or audit_scope not in REQUIRED_AUDIT_SCOPES
        ):
            errors.append(f"{label}: unsupported audit_scope {audit_scope!r}")
        for field in ("candidate_sha256", "contract_sha256"):
            if not isinstance(record[field], str) or not SHA256_RE.fullmatch(
                record[field]
            ):
                errors.append(f"{label}: {field} must be lowercase SHA-256")
        candidate_path = confined_path(
            run_dir,
            record["candidate_artifact"],
            f"{label}.candidate_artifact",
            errors,
        )
        if candidate_path is not None:
            if not candidate_path.is_file():
                errors.append(
                    f"{label}: candidate artifact does not exist: "
                    f"{record['candidate_artifact']!r}"
                )
            elif record["candidate_sha256"] != sha256_file(candidate_path):
                errors.append(f"{label}: candidate SHA-256 does not match its artifact")
        audit_path = confined_path(
            run_dir,
            record["audit_artifact"],
            f"{label}.audit_artifact",
            errors,
        )
        if audit_path is not None and not audit_path.is_file():
            errors.append(
                f"{label}: audit artifact does not exist: "
                f"{record['audit_artifact']!r}"
            )
        completed_at = parse_datetime(
            record["completed_at"], f"{label}.completed_at", errors
        )
        audit_repair = parse_datetime(
            record["last_material_repair_at"],
            f"{label}.last_material_repair_at",
            errors,
        )
        if repair_time is not None and audit_repair is not None and audit_repair != repair_time:
            errors.append(f"{label}: last_material_repair_at differs from campaign")
        if (
            completed_at is not None
            and repair_time is not None
            and completed_at <= repair_time
        ):
            errors.append(
                f"{label}: audit must complete after the last material repair"
            )
        if agent is not None and completed_at is not None:
            agent_started = agent.get("_parsed_started_at")
            agent_ended = agent.get("_parsed_ended_at")
            if (
                isinstance(agent_started, datetime)
                and repair_time is not None
                and agent_started <= repair_time
            ):
                errors.append(
                    f"{label}: auditor context must start after the last material repair"
                )
            if (
                isinstance(agent_started, datetime)
                and completed_at < agent_started
            ) or (
                isinstance(agent_ended, datetime)
                and completed_at > agent_ended
            ):
                errors.append(
                    f"{label}: completed_at lies outside the auditor's run interval"
                )
        if not isinstance(record["outcome"], str) or record["outcome"] not in {
            "pass",
            "fail",
            "inconclusive",
        }:
            errors.append(f"{label}: unsupported audit outcome")

        matches_final = (
            record["candidate_version"] == final_candidate_version
            and record["candidate_artifact"] == final_candidate_artifact
            and record["candidate_sha256"] == final_candidate_hash
            and record["contract_version"] == final_contract_version
            and record["contract_sha256"] == final_contract_hash
        )
        if (
            record["outcome"] == "pass"
            and record["authoring_involvement"] is False
            and matches_final
            and completed_at is not None
            and repair_time is not None
            and completed_at > repair_time
            and agent is not None
            and isinstance(auditor_id, str)
            and isinstance(context_id, str)
            and agent.get("fresh_context") is True
            and agent.get("context_id") == context_id
            and "audit" in str(agent.get("role", "")).lower()
            and isinstance(agent.get("_parsed_started_at"), datetime)
            and agent["_parsed_started_at"] > repair_time
            and isinstance(agent.get("_parsed_ended_at"), datetime)
            and agent["_parsed_started_at"] <= completed_at <= agent["_parsed_ended_at"]
            and isinstance(audit_scope, str)
            and audit_scope in REQUIRED_AUDIT_SCOPES
        ):
            qualifying.append((auditor_id, context_id, audit_scope))

    distinct_auditors = {auditor for auditor, _, _ in qualifying}
    distinct_contexts = {context for _, context, _ in qualifying}
    covered_scopes = {scope for _, _, scope in qualifying}
    qualifying_count = min(
        len(qualifying), len(distinct_auditors), len(distinct_contexts)
    )
    if declared_completed != qualifying_count:
        errors.append(
            f"audits.completed_fresh={declared_completed!r} "
            f"but logs contain {qualifying_count} qualifying fresh audits"
        )
    if status == "complete" and qualifying_count < required:
        errors.append(
            f"complete status requires {required} qualifying fresh audits; "
            f"found {qualifying_count}"
        )
    if status == "complete" and not REQUIRED_AUDIT_SCOPES.issubset(covered_scopes):
        errors.append(
            "complete status requires passing dependency/quantifier and "
            "adversarial-counterexample audit scopes"
        )
    return qualifying_count


def split_markdown_table_row(raw_line: str) -> list[str]:
    """Split a Markdown table row while preserving escaped literal pipes."""
    stripped = raw_line.strip()
    content = stripped[1:-1]
    cells: list[str] = []
    current: list[str] = []
    escaped = False
    for character in content:
        if escaped:
            current.append(character)
            escaped = False
        elif character == "\\":
            current.append(character)
            escaped = True
        elif character == "|":
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(character)
    cells.append("".join(current).strip())
    return cells


def markdown_tables(path: Path) -> list[list[tuple[int, list[str]]]]:
    tables: list[list[tuple[int, list[str]]]] = []
    current: list[tuple[int, list[str]]] = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        stripped = raw_line.strip()
        if stripped.startswith("|") and stripped.endswith("|"):
            cells = split_markdown_table_row(raw_line)
            if not (
                cells
                and all(re.fullmatch(r":?-{3,}:?", cell) for cell in cells)
            ):
                current.append((line_number, cells))
        elif current:
            tables.append(current)
            current = []
    if current:
        tables.append(current)
    return tables


def find_markdown_table(
    path: Path,
    required_headers: set[str],
    errors: list[str],
) -> list[tuple[int, list[str]]]:
    for table in markdown_tables(path):
        if table and required_headers.issubset(set(table[0][1])):
            return table
    errors.append(
        f"{path.name} is missing a table with headers "
        f"{', '.join(sorted(required_headers))}"
    )
    return []


def markdown_sections(text: str) -> dict[str, str]:
    sections: dict[str, list[str]] = {}
    current: str | None = None
    for line in text.splitlines():
        match = re.match(r"^##\s+(.+?)\s*$", line)
        if match:
            current = match.group(1)
            sections.setdefault(current, [])
        elif current is not None:
            sections[current].append(line)
    return {
        heading: "\n".join(lines).strip()
        for heading, lines in sections.items()
    }


def validate_markdown_identity_and_contract(
    run_dir: Path,
    run_id: str | None,
    data: dict[str, Any],
    status: str | None,
    errors: list[str],
) -> None:
    markdown_files = (
        "problem-contract.md",
        "source-manifest.md",
        "approach-registry.md",
        "claim-ledger.md",
        "audit-log.md",
        "reproducibility.md",
        "final-report.md",
    )
    for filename in markdown_files:
        text = (run_dir / filename).read_text(encoding="utf-8")
        match = re.search(r"^- Run ID:\s*`([^`]+)`\s*$", text, re.MULTILINE)
        if match is None or match.group(1) != run_id:
            errors.append(f"{filename} does not record the campaign run_id")

    contract_text = (run_dir / "problem-contract.md").read_text(
        encoding="utf-8"
    )
    target_match = re.search(
        r"^- Target ID:\s*`?([^`\n]*?)`?\s*$",
        contract_text,
        re.MULTILINE,
    )
    target_id = nested(data, "target_id", errors)
    if status in {"running", "paused", "complete", "incomplete"}:
        if (
            target_match is None
            or not target_match.group(1).strip()
            or target_match.group(1).strip() != target_id
        ):
            errors.append(
                "problem-contract.md Target ID must match campaign target_id"
            )
        required_sections = {
            "Verbatim request",
            "Normalized target",
            "Objects, definitions, and parameter domains",
            "Quantifiers and assumptions",
            "Boundary and degenerate cases",
            "Admissible resolutions and exact certificates",
            "Completion obligations",
            "Useful but insufficient partial progress",
            "Source, tool, and side-effect boundaries",
            "Requested output",
            "Material ambiguities and decisions",
            "Revision history",
        }
        sections = markdown_sections(contract_text)
        for heading in sorted(required_sections):
            body = sections.get(heading, "")
            if not body or re.search(r"\bpopulate\b", body, re.IGNORECASE):
                errors.append(
                    f"problem-contract.md section {heading!r} is not populated"
                )

    version_match = re.search(
        r"^- Contract version:\s*(\S+)\s*$",
        contract_text,
        re.MULTILINE,
    )
    if version_match is None:
        errors.append("problem-contract.md is missing Contract version")
    elif status == "complete":
        completion_version = nested(
            data, "completion.contract_version", errors
        )
        if version_match.group(1) != str(completion_version):
            errors.append(
                "problem-contract.md Contract version differs from completion record"
            )


def validate_claim_statuses(
    run_dir: Path, run_id: str | None, errors: list[str]
) -> None:
    rows = find_markdown_table(
        run_dir / "claim-ledger.md", {"Claim ID", "Status"}, errors
    )
    if not rows:
        return
    header = rows[0][1]
    claim_index = header.index("Claim ID")
    status_index = header.index("Status")
    for line_number, cells in rows[1:]:
        if len(cells) <= max(claim_index, status_index) or not cells[claim_index]:
            continue
        claim_id = cells[claim_index]
        require_namespaced_id(
            claim_id,
            "Claim ID",
            f"claim-ledger.md:{line_number}",
            run_id,
            errors,
        )
        if cells[status_index] not in CLAIM_STATUSES:
            errors.append(
                f"claim-ledger.md:{line_number} has unsupported status "
                f"{cells[status_index]!r}"
            )


def validate_source_manifest(
    run_dir: Path,
    run_id: str | None,
    errors: list[str],
) -> None:
    path = run_dir / "source-manifest.md"
    required_header_set = {
        "Retrieval ID",
        "Boundary class",
        "Exact query or URL",
        "Purpose",
        "Standard theorem/background claim",
        "Checked",
        "Source citation",
    }
    matching_tables = [
        table
        for table in markdown_tables(path)
        if table and required_header_set.issubset(set(table[0][1]))
    ]
    if not matching_tables:
        errors.append(
            "source-manifest.md is missing the structured public-retrieval table"
        )
        return
    required_headers = (
        "Retrieval ID",
        "Boundary class",
        "Exact query or URL",
        "Purpose",
        "Standard theorem/background claim",
        "Checked",
        "Source citation",
    )
    seen_retrieval_ids: set[str] = set()
    for rows in matching_tables:
        header = rows[0][1]
        indexes = {name: header.index(name) for name in required_headers}
        for line_number, cells in rows[1:]:
            if not cells or not any(cell.strip() for cell in cells):
                continue
            if len(cells) <= max(indexes.values()):
                errors.append(
                    f"source-manifest.md:{line_number} public-retrieval row is malformed"
                )
                continue
            values = {
                name: cells[indexes[name]].strip() for name in required_headers
            }
            if not values["Retrieval ID"]:
                errors.append(
                    f"source-manifest.md:{line_number} leaves 'Retrieval ID' empty"
                )
                continue
            require_namespaced_id(
                values["Retrieval ID"],
                "Retrieval ID",
                f"source-manifest.md:{line_number}",
                run_id,
                errors,
            )
            if values["Retrieval ID"] in seen_retrieval_ids:
                errors.append(
                    f"source-manifest.md:{line_number} repeats Retrieval ID "
                    f"{values['Retrieval ID']!r}"
                )
            seen_retrieval_ids.add(values["Retrieval ID"])
            boundary_class = values["Boundary class"]
            if boundary_class not in PUBLIC_RETRIEVAL_CLASSES:
                errors.append(
                    f"source-manifest.md:{line_number} has unsupported "
                    f"Boundary class {boundary_class!r}"
                )
            for name in required_headers[2:]:
                if not values[name]:
                    errors.append(
                        f"source-manifest.md:{line_number} leaves {name!r} empty"
                    )
            if values["Checked"].lower() != "true":
                errors.append(
                    f"source-manifest.md:{line_number} must set Checked to true"
                )
            searchable = " ".join(values[name] for name in required_headers[1:])
            if any(
                pattern.search(searchable)
                for pattern in PUBLIC_RETRIEVAL_BANNED_PATTERNS
            ):
                errors.append(
                    f"source-manifest.md:{line_number} explicitly records prohibited "
                    "exact-target, solution, or open-status retrieval"
                )


def validate_incomplete_approaches(
    run_dir: Path, run_id: str | None, errors: list[str]
) -> None:
    rows = find_markdown_table(
        run_dir / "approach-registry.md",
        {"Family ID", "Status", "Exact blocker", "Reopening condition"},
        errors,
    )
    if not rows:
        return
    header = rows[0][1]
    family_index = header.index("Family ID")
    status_index = header.index("Status")
    blocker_index = header.index("Exact blocker")
    reopening_index = header.index("Reopening condition")
    data_rows = [
        (line_number, cells)
        for line_number, cells in rows[1:]
        if len(cells) > family_index and cells[family_index]
    ]
    if not data_rows:
        errors.append("incomplete closeout requires recorded approach families")
        return
    allowed_terminal = {"blocked", "refuted", "merged", "abandoned"}
    for line_number, cells in data_rows:
        if len(cells) <= max(status_index, blocker_index, reopening_index):
            errors.append(
                f"approach-registry.md:{line_number} table row is malformed"
            )
            continue
        require_namespaced_id(
            cells[family_index],
            "Family ID",
            f"approach-registry.md:{line_number}",
            run_id,
            errors,
        )
        normalized_status = cells[status_index].strip().lower()
        if normalized_status not in allowed_terminal:
            errors.append(
                f"approach-registry.md:{line_number} is not terminal: "
                f"{cells[status_index]!r}"
            )
        if normalized_status in {"blocked", "abandoned"}:
            if not cells[blocker_index].strip():
                errors.append(
                    f"approach-registry.md:{line_number} needs an exact blocker"
                )
            if not cells[reopening_index].strip():
                errors.append(
                    f"approach-registry.md:{line_number} needs a reopening condition"
                )


def safe_core_research_files(
    repository_root: Path,
    errors: list[str],
) -> list[str]:
    core = ("GOALS.md", "SOURCES.md", "FINDINGS.md", "NEXTSTEP.md")
    present: list[str] = []
    for name in core:
        path = repository_root / name
        if not path.exists() and not path.is_symlink():
            continue
        try:
            resolved = path.resolve(strict=True)
        except (OSError, RuntimeError):
            errors.append(f"core research path is dangling or unreadable: {name}")
            continue
        try:
            resolved.relative_to(repository_root)
        except ValueError:
            errors.append(f"core research path resolves outside repository: {name}")
            continue
        if "RawSources" in resolved.parts:
            errors.append(f"core research path resolves inside RawSources: {name}")
            continue
        if resolved.is_file():
            present.append(name)
    return present


def validate_managed_repository(
    data: dict[str, Any],
    repository_root: Path | None,
    status: str | None,
    errors: list[str],
) -> None:
    detected = nested(data, "managed_repository.detected", errors)
    basis = nested(data, "managed_repository.detection_basis", errors)
    handoff = nested(data, "managed_repository.handoff_completed", errors)
    if not isinstance(detected, bool):
        errors.append("managed_repository.detected must be boolean")
        return
    if not isinstance(basis, str) or not basis:
        errors.append("managed_repository.detection_basis must be nonempty")
    if not isinstance(handoff, bool):
        errors.append("managed_repository.handoff_completed must be boolean")
    if repository_root is not None:
        present = safe_core_research_files(repository_root, errors)
        if len(present) == 4 and not detected:
            errors.append("all core research files exist but managed_repository is false")
        if detected and len(present) != 4:
            if not isinstance(basis, str) or not basis.startswith("applicable_AGENTS:"):
                errors.append(
                    "managed repository without all core files requires an "
                    "applicable_AGENTS detection basis"
                )
            else:
                policy_value = basis.removeprefix("applicable_AGENTS:")
                policy_file = Path(policy_value).expanduser().resolve()
                try:
                    repository_root.relative_to(policy_file.parent)
                except ValueError:
                    errors.append(
                        "managed AGENTS.md basis is not an ancestor policy file"
                    )
                if not policy_file.is_file() or policy_file.name != "AGENTS.md":
                    errors.append("managed AGENTS.md basis does not resolve to a file")
                else:
                    try:
                        policy_text = policy_file.read_text(encoding="utf-8")
                    except (OSError, UnicodeError):
                        errors.append("managed AGENTS.md basis is unreadable")
                    else:
                        if "research-repo-manager" not in policy_text:
                            errors.append(
                                "managed AGENTS.md basis lacks "
                                "research-repo-manager policy text"
                            )
    if detected and status in {"complete", "incomplete"} and handoff is not True:
        errors.append("managed voluntary closeout requires handoff_completed: true")


def validate_timing_and_status(
    data: dict[str, Any],
    run_dir: Path,
    run_id: str | None,
    status: str | None,
    allow_incomplete: bool,
    active_seconds: int,
    work_bounds: list[tuple[datetime, datetime, int]],
    agent_bounds: list[tuple[datetime, datetime, str, int]],
    round_bounds: list[tuple[datetime, datetime, int]],
    errors: list[str],
) -> None:
    started = parse_datetime(nested(data, "started_at", errors), "started_at", errors)
    earliest = parse_datetime(
        nested(data, "earliest_finalization_at", errors),
        "earliest_finalization_at",
        errors,
    )
    last_checkpoint = parse_datetime(
        nested(data, "last_checkpoint_at", errors), "last_checkpoint_at", errors
    )
    last_resumed = parse_datetime(
        nested(data, "timing.last_resumed_at", errors),
        "timing.last_resumed_at",
        errors,
    )
    terminal_value = nested(data, "status.terminal_at", errors)
    terminal_at: datetime | None = None
    if status in TERMINAL_STATUSES:
        terminal_at = parse_datetime(
            terminal_value, "status.terminal_at", errors
        )
    elif terminal_value is not None and terminal_value != "":
        errors.append("nonterminal status must leave status.terminal_at empty")

    target_id = nested(data, "target_id", errors)
    if status == "prepared" or (
        status in {"user_stopped", "environment_blocked"}
        and active_seconds == 0
    ):
        if not isinstance(target_id, str):
            errors.append("target_id must be a string")
    else:
        require_namespaced_id(
            target_id, "target_id", "campaign.yaml", run_id, errors
        )

    minimum_hours = nested(data, "timing.minimum_hours", errors)
    if minimum_hours != MINIMUM_HOURS:
        errors.append(f"timing.minimum_hours must equal {MINIMUM_HOURS}")
    if started is not None and earliest is not None:
        if earliest - started != timedelta(hours=MINIMUM_HOURS):
            errors.append(
                "earliest_finalization_at must be exactly eight hours after started_at"
            )
    if started is not None and last_checkpoint is not None and last_checkpoint < started:
        errors.append("last_checkpoint_at predates started_at")
    if started is not None and last_resumed is not None and last_resumed < started:
        errors.append("timing.last_resumed_at predates started_at")
    now = datetime.now().astimezone()
    if started is not None and started > now:
        errors.append("started_at lies in the future")
    if terminal_at is not None:
        if started is not None and terminal_at < started:
            errors.append("status.terminal_at predates started_at")
        if terminal_at > now:
            errors.append("status.terminal_at lies in the future")
        if last_checkpoint is not None and last_checkpoint > terminal_at:
            errors.append("last_checkpoint_at is later than status.terminal_at")
    elif last_checkpoint is not None and last_checkpoint > now:
        errors.append("last_checkpoint_at lies in the future")

    upper_bound = terminal_at if terminal_at is not None else now
    if last_resumed is not None and last_resumed > upper_bound:
        errors.append("timing.last_resumed_at exceeds the campaign time bound")
    all_bounds: list[tuple[str, datetime, datetime, int]] = []
    all_bounds.extend(
        ("work-intervals.jsonl", start, end, line)
        for start, end, line in work_bounds
    )
    all_bounds.extend(
        ("agent-runs.jsonl", start, end, line)
        for start, end, _, line in agent_bounds
    )
    all_bounds.extend(
        ("rounds.jsonl", start, end, line)
        for start, end, line in round_bounds
    )
    for source, record_start, record_end, line_number in all_bounds:
        if started is not None and record_start < started:
            errors.append(
                f"{source}:{line_number} starts before the campaign"
            )
        if record_end > upper_bound:
            boundary = "terminal timestamp" if terminal_at is not None else "present"
            errors.append(
                f"{source}:{line_number} ends after the campaign {boundary}"
            )
    latest_record_end = max(
        (record_end for _, _, record_end, _ in all_bounds),
        default=None,
    )
    if (
        latest_record_end is not None
        and last_checkpoint is not None
        and last_checkpoint < latest_record_end
    ):
        errors.append("last_checkpoint_at predates the latest recorded work")

    if status in NONTERMINAL_STATUSES:
        if not allow_incomplete:
            errors.append(
                f"nonterminal status {status!r} requires --allow-incomplete"
            )
    elif status in TERMINAL_STATUSES:
        if allow_incomplete:
            errors.append("--allow-incomplete must not validate a terminal record")
    else:
        errors.append(f"unsupported status.value: {status!r}")

    stopping_reason = nested(data, "status.stopping_reason", errors)
    exact_gap = nested(data, "status.exact_remaining_gap", errors)
    terminal_obstruction_id = nested(
        data, "status.terminal_obstruction_id", errors
    )
    no_defensible_next_step = nested(
        data, "status.no_defensible_next_step", errors
    )
    interruption_kind = nested(data, "status.interruption_kind", errors)
    interruption_evidence_value = nested(
        data, "status.interruption_evidence_artifact", errors
    )
    obstruction_rounds = nested(
        data, "timing.terminal_obstruction_rounds", errors
    )
    productive_rounds = nested(
        data, "timing.productive_rounds_after_minimum", errors
    )
    for label, value in (
        ("timing.productive_rounds_after_minimum", productive_rounds),
        ("timing.terminal_obstruction_rounds", obstruction_rounds),
    ):
        if (
            not isinstance(value, int)
            or isinstance(value, bool)
            or value < 0
        ):
            errors.append(f"{label} must be a nonnegative integer")
    if status in TERMINAL_STATUSES:
        if not isinstance(stopping_reason, str) or not stopping_reason.strip():
            errors.append("terminal status requires a nonempty stopping_reason")
        elif any(
            phrase in stopping_reason.lower()
            for phrase in ("problem is open", "open problem", "known to be open")
        ):
            errors.append("stopping_reason must not substitute an open-status answer")
        checkpoint_root = (run_dir / "checkpoints").resolve(strict=True)
        valid_checkpoints = []
        for checkpoint_path in checkpoint_root.rglob("*"):
            if not checkpoint_path.is_file():
                continue
            try:
                checkpoint_path.resolve(strict=True).relative_to(checkpoint_root)
            except (OSError, RuntimeError, ValueError):
                continue
            valid_checkpoints.append(checkpoint_path)
        if not valid_checkpoints:
            errors.append("terminal status requires a preserved checkpoint artifact")
    if status in {"complete", "incomplete"}:
        if (
            earliest is not None
            and terminal_at is not None
            and terminal_at < earliest
        ):
            errors.append(
                "voluntary terminal status occurs before the wall-clock floor"
            )
        if active_seconds < MINIMUM_ACTIVE_SECONDS:
            errors.append(
                "voluntary terminal status requires at least 28,800 active-work seconds"
            )
    if status == "complete":
        freeze_at = parse_datetime(
            nested(data, "completion.last_material_repair_at", errors),
            "completion.last_material_repair_at",
            errors,
        )
        if (
            freeze_at is not None
            and started is not None
            and freeze_at < started
        ):
            errors.append(
                "completion.last_material_repair_at predates campaign start"
            )
        if (
            freeze_at is not None
            and terminal_at is not None
            and freeze_at > terminal_at
        ):
            errors.append(
                "completion.last_material_repair_at follows terminal time"
            )
    if status == "incomplete":
        if not isinstance(exact_gap, str) or not exact_gap.strip():
            errors.append("incomplete status requires status.exact_remaining_gap")
        require_namespaced_id(
            terminal_obstruction_id,
            "status.terminal_obstruction_id",
            "campaign.yaml",
            run_id,
            errors,
        )
        if no_defensible_next_step is not True:
            errors.append(
                "incomplete status requires status.no_defensible_next_step: true"
            )
        if (
            not isinstance(obstruction_rounds, int)
            or isinstance(obstruction_rounds, bool)
            or obstruction_rounds < 3
        ):
            errors.append(
                "incomplete status requires at least 3 terminal obstruction rounds"
            )
    if status == "complete":
        if isinstance(exact_gap, str) and exact_gap.strip():
            errors.append("complete status must not declare an exact remaining gap")
        if isinstance(terminal_obstruction_id, str) and terminal_obstruction_id:
            errors.append("complete status must not declare a terminal obstruction")
        if no_defensible_next_step is not False:
            errors.append(
                "complete status requires status.no_defensible_next_step: false"
            )
    if status == "user_stopped":
        if interruption_kind != "user_request":
            errors.append(
                "user_stopped requires status.interruption_kind: user_request"
            )
    elif status == "environment_blocked":
        if not isinstance(interruption_kind, str) or interruption_kind not in {
                "permission",
                "credential",
                "capability",
                "environment",
                "required_tool",
            }:
            errors.append(
                "environment_blocked requires a recognized interruption_kind"
            )
    elif interruption_kind is not None and interruption_kind != "":
        errors.append(
            "voluntary or nonterminal status must leave interruption_kind empty"
        )
    if status in {"user_stopped", "environment_blocked"}:
        evidence_path = confined_path(
            run_dir,
            interruption_evidence_value,
            "status.interruption_evidence_artifact",
            errors,
        )
        if evidence_path is not None:
            try:
                evidence_path.resolve(strict=False).relative_to(
                    (run_dir / "checkpoints").resolve(strict=True)
                )
            except ValueError:
                errors.append(
                    "interruption evidence must resolve inside checkpoints/"
                )
            if not evidence_path.is_file():
                errors.append("interruption evidence artifact does not exist")
            else:
                try:
                    evidence_text = evidence_path.read_text(encoding="utf-8")
                    evidence_words = len(evidence_text.split())
                except (OSError, UnicodeError):
                    errors.append("interruption evidence artifact is unreadable")
                else:
                    if evidence_words < 5:
                        errors.append(
                            "interruption evidence artifact needs substantive evidence"
                        )
                    lowered_evidence = evidence_text.lower()
                    if status == "user_stopped" and not all(
                        token in lowered_evidence for token in ("user", "stop")
                    ):
                        errors.append(
                            "user-stop evidence must identify the user's stop request"
                        )
                    if status == "environment_blocked":
                        evidence_token = (
                            "tool"
                            if interruption_kind == "required_tool"
                            else str(interruption_kind)
                        )
                        if evidence_token not in lowered_evidence:
                            errors.append(
                                "environment-block evidence must identify its kind"
                            )
    elif interruption_evidence_value is not None and interruption_evidence_value != "":
        errors.append(
            "non-interruption status must leave interruption evidence empty"
        )


def validate_completion_hashes(
    data: dict[str, Any], run_dir: Path, status: str | None, errors: list[str]
) -> None:
    if status != "complete":
        return
    candidate_version = nested(data, "completion.candidate_version", errors)
    candidate_artifact_value = nested(
        data, "completion.candidate_artifact", errors
    )
    candidate_hash = nested(data, "completion.candidate_sha256", errors)
    contract_version = nested(data, "completion.contract_version", errors)
    contract_hash = nested(data, "completion.contract_sha256", errors)
    if not isinstance(candidate_version, str) or not candidate_version:
        errors.append("complete status requires completion.candidate_version")
    candidate_artifact = confined_path(
        run_dir,
        candidate_artifact_value,
        "completion.candidate_artifact",
        errors,
    )
    if candidate_artifact is not None:
        if not candidate_artifact.is_file():
            errors.append("completion.candidate_artifact does not exist")
        elif (
            isinstance(candidate_hash, str)
            and SHA256_RE.fullmatch(candidate_hash)
            and sha256_file(candidate_artifact) != candidate_hash
        ):
            errors.append(
                "completion.candidate_sha256 does not match candidate_artifact"
            )
    if not isinstance(contract_version, str) or not contract_version:
        errors.append("complete status requires completion.contract_version")
    if not isinstance(candidate_hash, str) or not SHA256_RE.fullmatch(candidate_hash):
        errors.append("complete status requires a lowercase candidate SHA-256")
    if not isinstance(contract_hash, str) or not SHA256_RE.fullmatch(contract_hash):
        errors.append("complete status requires a lowercase contract SHA-256")
    else:
        actual_contract_hash = sha256_file(run_dir / "problem-contract.md")
        if contract_hash != actual_contract_hash:
            errors.append(
                "completion.contract_sha256 does not match problem-contract.md"
            )


def validate_final_report(
    run_dir: Path,
    data: dict[str, Any],
    status: str | None,
    errors: list[str],
) -> None:
    if status not in TERMINAL_STATUSES:
        return
    text = (run_dir / "final-report.md").read_text(encoding="utf-8")
    status_match = re.search(r"^- Terminal status:\s*(.+?)\s*$", text, re.MULTILINE)
    if status_match is None or status_match.group(1).strip() != status:
        errors.append("final-report.md must record the exact terminal status")
    terminal_match = re.search(
        r"^- Terminal at:\s*(.+?)\s*$", text, re.MULTILINE
    )
    terminal_value = nested(data, "status.terminal_at", errors)
    if (
        terminal_match is None
        or terminal_match.group(1).strip() != str(terminal_value)
    ):
        errors.append("final-report.md must record the exact terminal timestamp")
    body_lines = [
        line
        for line in text.splitlines()
        if line.strip()
        and not line.lstrip().startswith("#")
        and not line.startswith("- Run ID:")
        and not line.startswith("- Terminal status:")
        and not line.startswith("- Terminal at:")
    ]
    minimum_words = 20 if status in {"user_stopped", "environment_blocked"} else 50
    if len(" ".join(body_lines).split()) < minimum_words:
        errors.append(
            f"final-report.md needs at least {minimum_words} substantive words "
            f"for terminal status {status}"
        )
    sections = markdown_sections(text)
    if status in {"complete", "incomplete"}:
        required_sections = {
            "Normalized target",
            "Resolution or strongest verified result",
            "Proof, certificate, or exact remaining gap",
            "Assumptions and dependencies",
            "Reproducibility and artifacts",
            "Residual risks and next decisive action",
        }
        if status == "complete":
            required_sections.add("Independent audits")
        else:
            required_sections.add("Failed or blocked approaches")
        for heading in sorted(required_sections):
            if not sections.get(heading, "").strip():
                errors.append(
                    f"final-report.md section {heading!r} is not populated"
                )
    if status == "incomplete" and not re.search(
        r"exact remaining gap", text, re.IGNORECASE
    ):
        errors.append(
            "incomplete final-report.md must explicitly identify the exact remaining gap"
        )
    if status == "incomplete" and any(
        phrase in text.lower()
        for phrase in ("problem is open", "open problem", "known to be open")
    ):
        errors.append(
            "incomplete final-report.md must not substitute an open-status answer"
        )


def _validate_campaign_impl(run_dir: Path, allow_incomplete: bool) -> list[str]:
    errors: list[str] = []
    run_dir = run_dir.expanduser().resolve()
    if not run_dir.is_dir():
        return [f"run directory does not exist: {run_dir}"]
    validate_required_tree(run_dir, errors)
    if errors:
        return errors
    campaign_path = run_dir / "campaign.yaml"
    try:
        data = parse_simple_yaml(campaign_path)
    except (OSError, ValidationFailure) as exc:
        return errors + [str(exc)]

    status_value = nested(data, "status.value", errors)
    status = status_value if isinstance(status_value, str) else None
    repository_root, run_id = validate_identity(data, run_dir, errors)
    (
        selected_model,
        selected_reasoning,
        campaign_verification,
        available,
        declared_peak,
    ) = validate_capability(
        data, run_dir, status, errors
    )
    validate_policies(data, errors)

    work_records = load_jsonl(run_dir / "work-intervals.jsonl", errors)
    agent_records = load_jsonl(run_dir / "agent-runs.jsonl", errors)
    round_records = load_jsonl(run_dir / "rounds.jsonl", errors)
    audit_records = load_jsonl(run_dir / "audits.jsonl", errors)
    active_seconds, _, work_bounds = validate_work_intervals(
        work_records, run_dir, run_id, data, errors
    )
    round_bounds = validate_rounds(
        round_records,
        run_dir,
        run_id,
        data,
        status,
        errors,
    )
    agents, _, agent_bounds = validate_agent_runs(
        agent_records,
        run_id,
        selected_model,
        selected_reasoning,
        campaign_verification,
        declared_peak,
        available,
        status,
        errors,
    )
    validate_completion_hashes(data, run_dir, status, errors)
    validate_audits(
        audit_records,
        agents,
        run_dir,
        run_id,
        data,
        status,
        errors,
    )
    validate_markdown_identity_and_contract(
        run_dir, run_id, data, status, errors
    )
    validate_source_manifest(run_dir, run_id, errors)
    validate_claim_statuses(run_dir, run_id, errors)
    if status == "incomplete":
        validate_incomplete_approaches(run_dir, run_id, errors)
    validate_managed_repository(data, repository_root, status, errors)
    validate_timing_and_status(
        data,
        run_dir,
        run_id,
        status,
        allow_incomplete,
        active_seconds,
        work_bounds,
        agent_bounds,
        round_bounds,
        errors,
    )
    validate_final_report(run_dir, data, status, errors)
    return errors


def validate_campaign(run_dir: Path, allow_incomplete: bool) -> list[str]:
    try:
        return _validate_campaign_impl(run_dir, allow_incomplete)
    except (OSError, RuntimeError, UnicodeError) as exc:
        return [f"campaign record is unreadable or path-unsafe: {exc}"]


def main() -> int:
    args = parse_args()
    errors = validate_campaign(args.run_dir, args.allow_incomplete)
    if errors:
        print("Campaign validation failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(
        json.dumps(
            {
                "run_directory": str(args.run_dir.expanduser().resolve()),
                "status": "valid",
                "mode": "checkpoint" if args.allow_incomplete else "terminal",
                "scope": "protocol-and-artifact validation only; not mathematical truth",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
