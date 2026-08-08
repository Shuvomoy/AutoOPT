#!/usr/bin/env python3
"""Create the standard applied-math research repository scaffold."""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path


FILES = (
    "AGENTS.md",
    "GOALS.md",
    "SOURCES.md",
    "OPTIONAL_GOALS.md",
    "FINDINGS.md",
    "NEXTSTEP.md",
    "EXPERIMENTS.md",
    "ARTIFACTS.md",
    "REPRODUCIBILITY.md",
)
DEFAULT_DIRECTORIES = ("RawSources", "ResearchLog", "Archive")
OPTIMIZATION_DIRECTORIES = (
    "models",
    "src",
    "experiments",
    "instances",
    "results",
    "figures",
    "paper",
)
TEMPLATE_DIR = Path(__file__).resolve().parents[1] / "assets" / "templates"


@dataclass(frozen=True)
class Action:
    kind: str
    path: Path
    detail: str = ""


def validate_target(target: Path, directories: tuple[str, ...]) -> None:
    if target.exists() and not target.is_dir():
        raise ValueError(f"target exists but is not a directory: {target}")

    for name in FILES:
        path = target / name
        if path.exists() and not path.is_file():
            raise ValueError(f"required file path exists with wrong type: {path}")

    for name in directories:
        path = target / name
        if path.exists() and not path.is_dir():
            raise ValueError(f"required directory path exists with wrong type: {path}")


def template_content(name: str, use_templates: bool) -> str:
    if not use_templates:
        return ""

    path = TEMPLATE_DIR / name
    if not path.is_file():
        raise ValueError(f"missing template file: {path}")
    return path.read_text(encoding="utf-8")


def plan_scaffold(
    target: Path,
    *,
    use_templates: bool,
    overwrite_empty_files: bool,
    optimization_layout: bool,
) -> tuple[list[Action], dict[str, str]]:
    directories = DEFAULT_DIRECTORIES + (
        OPTIMIZATION_DIRECTORIES if optimization_layout else ()
    )
    validate_target(target, directories)

    actions: list[Action] = []
    file_contents: dict[str, str] = {}

    if not target.exists():
        actions.append(Action("create-directory", target, "target root"))

    for name in directories:
        path = target / name
        if not path.exists():
            actions.append(Action("create-directory", path))

    for name in FILES:
        path = target / name
        content = template_content(name, use_templates)
        file_contents[name] = content

        if not path.exists():
            detail = "from template" if use_templates else "empty"
            actions.append(Action("create-file", path, detail))
            continue

        current = path.read_text(encoding="utf-8")
        if current.strip():
            actions.append(Action("preserve-file", path, "nonempty"))
        elif overwrite_empty_files:
            detail = "from template" if use_templates else "empty"
            actions.append(Action("overwrite-empty-file", path, detail))
        else:
            actions.append(Action("preserve-file", path, "empty"))

    return actions, file_contents


def create_scaffold(
    target: Path,
    *,
    use_templates: bool,
    overwrite_empty_files: bool,
    optimization_layout: bool,
    dry_run: bool,
) -> list[Action]:
    actions, file_contents = plan_scaffold(
        target,
        use_templates=use_templates,
        overwrite_empty_files=overwrite_empty_files,
        optimization_layout=optimization_layout,
    )

    if dry_run:
        return actions

    target.mkdir(parents=True, exist_ok=True)

    for action in actions:
        if action.kind == "create-directory":
            action.path.mkdir(parents=True, exist_ok=True)
        elif action.kind in {"create-file", "overwrite-empty-file"}:
            action.path.write_text(file_contents[action.path.name], encoding="utf-8")

    return actions


def print_actions(actions: list[Action], *, dry_run: bool) -> None:
    prefix = "DRY-RUN" if dry_run else "DONE"
    for action in actions:
        detail = f" ({action.detail})" if action.detail else ""
        print(f"{prefix}: {action.kind}: {action.path}{detail}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create an applied-math research repository scaffold without overwriting existing files.",
    )
    parser.add_argument(
        "target",
        nargs="?",
        default=".",
        help="Research repository directory to initialize. Defaults to the current directory.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print planned scaffold actions without writing files or directories.",
    )
    parser.add_argument(
        "--no-templates",
        action="store_true",
        help="Create absent planning files as empty files instead of copying bundled templates.",
    )
    parser.add_argument(
        "--overwrite-empty-files",
        action="store_true",
        help="Replace existing empty planning files with templates or empty files. Nonempty files are always preserved.",
    )
    parser.add_argument(
        "--optimization-layout",
        action="store_true",
        help="Also create optional optimization-project directories such as experiments/, results/, figures/, and paper/.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = Path(args.target).expanduser().resolve()

    try:
        actions = create_scaffold(
            target,
            use_templates=not args.no_templates,
            overwrite_empty_files=args.overwrite_empty_files,
            optimization_layout=args.optimization_layout,
            dry_run=args.dry_run,
        )
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print_actions(actions, dry_run=args.dry_run)
    if args.dry_run:
        print(f"Research repository scaffold dry run complete: {target}")
    else:
        print(f"Research repository scaffold is ready: {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
