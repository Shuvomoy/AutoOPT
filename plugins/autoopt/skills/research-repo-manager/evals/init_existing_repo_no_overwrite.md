# init_existing_repo_no_overwrite

## Setup

- Repository contains nonempty `GOALS.md` and empty `FINDINGS.md`.
- `RawSources/`, `ResearchLog/`, and `Archive/` may or may not exist.

## Prompt

Use `$research-repo-manager` to initialize this research repository.

## Must Pass

- Does not overwrite nonempty `GOALS.md`.
- Preserves empty `FINDINGS.md` unless `--overwrite-empty-files` is explicitly
  approved or requested.
- Creates missing standard directories.
- Creates missing planning files from templates.
- Does not write inside `RawSources/`.
