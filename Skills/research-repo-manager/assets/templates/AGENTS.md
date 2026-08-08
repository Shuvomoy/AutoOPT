# Agent Instructions

## Research Standards

- Distinguish proven claims, checked derivations, computed evidence, literature
  claims, conjectures, refutations, and claims needing verification.
- Do not present computational evidence as a theorem.
- Do not present solver output as an exact certificate unless solver status,
  tolerances, gaps, and logs support that interpretation.
- Preserve `RawSources/` as immutable primary material. Read from it only.
- Important conclusions belong in `FINDINGS.md`, not only in chat.

## Computational Standards

- Prefer reproducible scripts over notebook-only workflows.
- Record commands, seeds, solver versions, termination statuses, tolerances, and
  relevant output artifacts.
- For Julia projects, prefer `julia --project=.` and preserve `Project.toml` and
  `Manifest.toml` when they define the active environment.
- For Mathematica notebooks, keep a text-exported `.wl` file or a summary note
  when possible.

## Compactification Standards

- Never archive files needed to reproduce current claims, figures, tables,
  theorem checks, or benchmark results.
- Before moving files, identify references from Markdown, LaTeX, scripts,
  notebooks, source code, and planning files.
- Use `git mv` for tracked files after an approved compactification plan.
