#!/usr/bin/env python3
"""Initialize a collision-safe highest-reasoning research campaign record."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
from datetime import datetime, timedelta
from pathlib import Path


MINIMUM_HOURS = 8
RUNS_RELATIVE_PATH = Path("ResearchLog") / "highest-reasoning-runs"
CORE_RESEARCH_FILES = ("GOALS.md", "SOURCES.md", "FINDINGS.md", "NEXTSTEP.md")
REQUIRED_TEMPLATE_FILES = {
    "campaign.yaml",
    "problem-contract.md",
    "source-manifest.md",
    "approach-registry.md",
    "claim-ledger.md",
    "audit-log.md",
    "reproducibility.md",
    "final-report.md",
}
TEMPLATE_MARKER_RE = re.compile(r"\{\{[A-Z0-9_]+\}\}")


class CampaignInitError(RuntimeError):
    """Raised when a campaign cannot be initialized safely."""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create a scoped highest-reasoning campaign under ResearchLog."
    )
    parser.add_argument(
        "--root",
        required=True,
        type=Path,
        help="Invoking repository or research-directory root.",
    )
    parser.add_argument(
        "--slug",
        required=True,
        help="Short problem slug; normalized to lowercase hyphen-case.",
    )
    parser.add_argument(
        "--managed-agents",
        type=Path,
        help=(
            "Applicable AGENTS.md that explicitly declares "
            "research-repo-manager governance."
        ),
    )
    return parser.parse_args()


def normalize_slug(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.strip().lower()).strip("-")
    slug = re.sub(r"-{2,}", "-", slug)
    if not slug:
        raise CampaignInitError("The slug must contain at least one letter or digit.")
    return slug[:64].rstrip("-")


def ensure_safe_root(root: Path) -> Path:
    try:
        resolved = root.expanduser().resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise CampaignInitError(f"Repository root does not exist: {root}") from exc
    if not resolved.is_dir():
        raise CampaignInitError(f"Repository root is not a directory: {resolved}")
    if "RawSources" in resolved.parts:
        raise CampaignInitError(
            "Refusing to initialize a campaign inside immutable RawSources."
        )
    return resolved


def ensure_confined_existing_path(path: Path, root: Path, label: str) -> None:
    """Reject an existing or dangling path that could redirect later writes."""
    if not path.exists() and not path.is_symlink():
        return
    try:
        resolved = path.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise CampaignInitError(f"{label} is a dangling symlink: {path}") from exc
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise CampaignInitError(f"{label} resolves outside the repository") from exc
    if "RawSources" in resolved.parts:
        raise CampaignInitError(f"{label} resolves inside immutable RawSources")


def find_safe_core_research_files(root: Path) -> list[str]:
    present: list[str] = []
    for name in CORE_RESEARCH_FILES:
        path = root / name
        if not path.exists() and not path.is_symlink():
            continue
        try:
            resolved = path.resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise CampaignInitError(
                f"Core research path is a dangling symlink: {path}"
            ) from exc
        try:
            resolved.relative_to(root)
        except ValueError as exc:
            raise CampaignInitError(
                f"Core research path resolves outside the repository: {path}"
            ) from exc
        if "RawSources" in resolved.parts:
            raise CampaignInitError(
                f"Core research path resolves inside immutable RawSources: {path}"
            )
        if resolved.is_file():
            present.append(name)
    return present


def detect_managed_repository(
    root: Path, managed_agents: Path | None
) -> tuple[bool, str]:
    present = find_safe_core_research_files(root)
    if len(present) == len(CORE_RESEARCH_FILES):
        return True, "all_core_research_files"
    if managed_agents is not None:
        candidate = (
            managed_agents
            if managed_agents.is_absolute()
            else root / managed_agents
        )
        try:
            policy_file = candidate.expanduser().resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise CampaignInitError(
                f"Managed-repository AGENTS.md does not exist: {candidate}"
            ) from exc
        if not policy_file.is_file() or policy_file.name != "AGENTS.md":
            raise CampaignInitError(
                "--managed-agents must identify an applicable AGENTS.md file"
            )
        try:
            root.relative_to(policy_file.parent)
        except ValueError as exc:
            raise CampaignInitError(
                "--managed-agents is not in an ancestor directory of the root"
            ) from exc
        policy_text = policy_file.read_text(encoding="utf-8")
        if "research-repo-manager" not in policy_text:
            raise CampaignInitError(
                "The supplied AGENTS.md does not declare research-repo-manager"
            )
        return True, "applicable_AGENTS:" + str(policy_file)
    if present:
        return False, "partial_core_files:" + ",".join(present)
    return False, "none"


def reserve_run_directory(runs_root: Path, base_name: str) -> Path:
    """Atomically reserve a collision-free directory owned by this invocation."""
    candidates = [runs_root / base_name]
    candidates.extend(
        runs_root / f"{base_name}-{suffix:02d}" for suffix in range(2, 10_000)
    )
    for candidate in candidates:
        try:
            candidate.mkdir()
        except FileExistsError:
            continue
        return candidate
    raise CampaignInitError("Could not allocate a collision-free run directory.")


def render_template(source: Path, destination: Path, replacements: dict[str, str]) -> None:
    text = source.read_text(encoding="utf-8")
    markers = set(TEMPLATE_MARKER_RE.findall(text))
    unknown = sorted(markers - replacements.keys())
    if unknown:
        raise CampaignInitError(
            f"Unknown template markers in {source.name}: {', '.join(unknown)}"
        )
    rendered = TEMPLATE_MARKER_RE.sub(
        lambda match: replacements[match.group(0)],
        text,
    )
    destination.write_text(rendered, encoding="utf-8")


def initialize(
    root: Path,
    slug_input: str,
    managed_agents: Path | None = None,
) -> dict[str, object]:
    root = ensure_safe_root(root)
    slug = normalize_slug(slug_input)
    template_root = Path(__file__).resolve().parent.parent / "assets" / "run-template"
    if not template_root.is_dir():
        raise CampaignInitError(f"Run template directory is missing: {template_root}")
    available_templates = {
        path.name for path in template_root.iterdir() if path.is_file()
    }
    missing_templates = sorted(REQUIRED_TEMPLATE_FILES - available_templates)
    if missing_templates:
        raise CampaignInitError(
            "Run template is incomplete; missing: " + ", ".join(missing_templates)
        )
    managed, detection_basis = detect_managed_repository(root, managed_agents)

    now = datetime.now().astimezone().replace(microsecond=0)
    earliest = now + timedelta(hours=MINIMUM_HOURS)
    timestamp = now.strftime("%Y%m%dT%H%M%S%z")
    base_name = f"{timestamp}-{slug}"
    runs_root = root / RUNS_RELATIVE_PATH
    ensure_confined_existing_path(root / "ResearchLog", root, "ResearchLog")
    ensure_confined_existing_path(
        runs_root,
        root,
        "ResearchLog/highest-reasoning-runs",
    )
    if runs_root.exists() and not runs_root.is_dir():
        raise CampaignInitError(f"Campaign root is not a directory: {runs_root}")
    runs_root.mkdir(parents=True, exist_ok=True)
    resolved_runs_root = runs_root.resolve(strict=True)
    try:
        resolved_runs_root.relative_to(root)
    except ValueError as exc:
        raise CampaignInitError(
            "ResearchLog/highest-reasoning-runs resolves outside the repository root"
        ) from exc
    if "RawSources" in resolved_runs_root.parts:
        raise CampaignInitError(
            "Refusing a campaign root that resolves inside immutable RawSources"
        )

    run_directory = reserve_run_directory(resolved_runs_root, base_name)
    run_id = "hr-" + run_directory.name

    replacements = {
        "{{RUN_ID}}": run_id,
        "{{REPOSITORY_ROOT_JSON}}": json.dumps(str(root), ensure_ascii=False),
        "{{RUN_DIRECTORY_JSON}}": json.dumps(str(run_directory), ensure_ascii=False),
        "{{STARTED_AT}}": now.isoformat(),
        "{{EARLIEST_FINALIZATION_AT}}": earliest.isoformat(),
        "{{MANAGED_DETECTED}}": "true" if managed else "false",
        "{{MANAGED_DETECTION_BASIS_JSON}}": json.dumps(
            detection_basis, ensure_ascii=False
        ),
    }

    try:
        for template_name in sorted(REQUIRED_TEMPLATE_FILES):
            template = template_root / template_name
            render_template(template, run_directory / template.name, replacements)
        checkpoints = run_directory / "checkpoints"
        checkpoints.mkdir()
        (checkpoints / "0000-prepared.md").write_text(
            "\n".join(
                (
                    "# Prepared Campaign Checkpoint",
                    "",
                    f"- Run ID: `{run_id}`",
                    f"- Initialized at: `{now.isoformat()}`",
                    "- State: Campaign record created; capability and problem contract "
                    "must be populated before research begins.",
                    "",
                )
            ),
            encoding="utf-8",
        )
        (run_directory / "artifacts").mkdir()
        for log_name in (
            "work-intervals.jsonl",
            "agent-runs.jsonl",
            "rounds.jsonl",
            "audits.jsonl",
        ):
            (run_directory / log_name).write_text("", encoding="utf-8")
        expected = REQUIRED_TEMPLATE_FILES | {
            "work-intervals.jsonl",
            "agent-runs.jsonl",
            "rounds.jsonl",
            "audits.jsonl",
        }
        absent = sorted(
            name for name in expected if not (run_directory / name).is_file()
        )
        if absent:
            raise CampaignInitError(
                "Initialized campaign is incomplete; missing: " + ", ".join(absent)
            )
    except Exception:
        shutil.rmtree(run_directory, ignore_errors=True)
        raise

    return {
        "run_id": run_id,
        "run_directory": str(run_directory),
        "repository_root": str(root),
        "started_at": now.isoformat(),
        "earliest_finalization_at": earliest.isoformat(),
        "minimum_hours": MINIMUM_HOURS,
        "managed_repository": managed,
        "managed_detection_basis": detection_basis,
    }


def main() -> int:
    args = parse_args()
    try:
        result = initialize(args.root, args.slug, args.managed_agents)
    except (CampaignInitError, OSError, RuntimeError, UnicodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
