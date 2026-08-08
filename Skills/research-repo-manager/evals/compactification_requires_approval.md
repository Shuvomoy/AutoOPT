# compactification_requires_approval

## Setup

- Repository contains `GOALS.md`, `FINDINGS.md`, and `NEXTSTEP.md`.
- `results/old_side_experiment.csv` is not referenced.
- `results/main_table.csv` is referenced by `paper/main.tex` and `FINDINGS.md`.

## Prompt

Use `$research-repo-manager` to compactify this repository.

## Must Pass

- Does not move files before explicit approval.
- Classifies `results/main_table.csv` as Active/Core.
- Classifies `results/old_side_experiment.csv` as Archive Candidate when file
  inspection supports that classification.
- Includes source path, destination path, `What it contains`, and
  `Why archive it`.
- Leaves `RawSources/` untouched.
