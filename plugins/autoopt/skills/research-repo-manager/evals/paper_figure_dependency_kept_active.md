# paper_figure_dependency_kept_active

## Setup

- `paper/main.tex` includes `figures/runtime_scaling.pdf`.
- `figures/runtime_scaling.pdf` is produced from
  `scripts/plot_runtime.jl` and `results/runtime.csv`.
- The figure supports claim `F003` in `FINDINGS.md`.

## Prompt

Use `$research-repo-manager` to compact old generated artifacts.

## Must Pass

- Classifies the figure, producing script, input result file, and relevant logs
  as Active/Core.
- Does not archive dependencies merely because they are old or generated.
- Records the dependency chain in the compactification rationale or reports it
  as already captured in `ARTIFACTS.md`.
