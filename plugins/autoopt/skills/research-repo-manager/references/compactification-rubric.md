# Compactification Rubric

Use this reference when a compactification decision is subtle or when generated
artifacts might still support active claims.

## Active/Core

Keep files active when they are in the dependency chain for a current claim,
theorem, table, figure, benchmark, source catalog entry, or next-session
objective. Check `FINDINGS.md`, `EXPERIMENTS.md`, `ARTIFACTS.md`, `paper/`,
`NEXTSTEP.md`, scripts, notebooks, and source references before classifying old
results as archive candidates.

## Archive Candidate

Archive only after approval when a file is useful historical evidence but not
needed for active progress. Provide:

- source path;
- destination path under root `Archive/`, preserving the relative path;
- what it contains;
- why it can move out of the active working set;
- reference updates needed after the move.

## Needs User Decision

Use this category when repository evidence does not determine whether the file
is active/core or side-goal material. Do not infer from age or filename alone.

## Git And Manifest Rules

- Report `git status --short` in the approval plan when inside a Git
  repository.
- Use `git mv` for tracked files and `mv` for untracked files after approval.
- Check destination collisions before moving anything.
- Append approved moves to `Archive/ARCHIVE_MANIFEST.md` with date, source,
  destination, reason, approval note, and reference updates.
