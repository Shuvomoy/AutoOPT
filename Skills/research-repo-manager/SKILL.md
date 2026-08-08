---
name: research-repo-manager
description: Initialize, refresh, compact, and audit applied-math/optimization research repositories. Use when managing immutable sources, research goals, claim/evidence ledgers, experiment/reproducibility logs, source drift, next sessions, or approval-gated archiving.
---

# Research Repo Manager

## Workflow

Choose the workflow mode from the user's request and the repository state.

Use Initialization Mode for a new or unscaffolded research folder. Use Status
Refresh Mode when the standard planning files already exist, or when the user
asks to summarize, refresh, update, or determine current goals, findings, open
gaps, or the next step. Use Research Session Mode when the user asks to work on,
resume, continue, or make progress in an existing research repository. Use
Experiment Audit Mode when the user asks to validate, reproduce, summarize,
compare, or audit computational experiments, solver outputs, generated
instances, benchmark tables, figures, or result artifacts. Use Compactification
Mode when the user asks to compact, declutter, archive, or reorganize non-core
artifacts in an existing research repository.

## Initialization Mode

1. Scaffold the current research folder first by resolving the helper script
   relative to this loaded `SKILL.md` file and running it against the current
   research repository root:

   ```bash
   python3 <path-to-this-skill>/scripts/init_research_repo.py .
   ```

   The scaffold creates `RawSources/`, `ResearchLog/`, and root-level
   `Archive/`, plus the standard planning, catalog, experiment, artifact, and
   reproducibility files. Do not use a user-specific absolute path for the
   script.

2. Treat `RawSources/` as immutable. Read from it only. Never modify, rename, move, delete, summarize into the same files, or normalize files in `RawSources/`.

3. Ask the user to populate `RawSources/` with papers, notes, PDFs, datasets, screenshots, or other primary material. After the user confirms, inspect `RawSources/` to infer the research area, source types, mathematical context, and evidentiary constraints.

4. Draft or update `SOURCES.md` from the inspected `RawSources/` material
   before finalizing planning files. Catalog each meaningful source file or
   source bundle with source ID, path, source type, immutability, hash when
   available, provenance/citation metadata when known, version/date, and notes
   on how it supports `GOALS.md`, `FINDINGS.md`, or `ARTIFACTS.md`. Mark
   unknown provenance explicitly rather than inventing metadata.

5. Ask whether existing research-log material should be placed in `ResearchLog/`. If the user provides or confirms log material, inspect `ResearchLog/` for prior attempts, partial arguments, computational evidence, unresolved questions, and decisions already made.

6. Elicit the research goal in Plan Mode until it is clear, unambiguous, and decomposable into concrete sessions, each scoped to one full research workday. Prefer one to three concise questions at a time. Resolve the main object of study, mathematical/computational deliverables, success criteria, constraints, and what would count as useful progress.

7. Draft proposed `GOALS.md` content and ask for explicit approval before writing it. Do not write `GOALS.md` until the user approves the proposed content.

8. Populate `AGENTS.md`, `OPTIONAL_GOALS.md`, `FINDINGS.md`,
   `EXPERIMENTS.md`, `ARTIFACTS.md`, `REPRODUCIBILITY.md`, and `NEXTSTEP.md`
   only after the goal and available materials are understood. Use
   `OPTIONAL_GOALS.md` for optional, deferred, paused, archived, or
   experimental goals that should not displace the single active session in
   `NEXTSTEP.md`. Preserve existing user-written content unless the user
   approves replacement. Active planning files should summarize conclusions
   from archived material rather than requiring routine consultation of
   archived process logs.

## Status Refresh Mode

1. Inspect the existing planning context before drawing conclusions:
   `AGENTS.md`, `GOALS.md`, `SOURCES.md`, `OPTIONAL_GOALS.md`, `FINDINGS.md`,
   `EXPERIMENTS.md`, `ARTIFACTS.md`, `REPRODUCIBILITY.md`, `NEXTSTEP.md`,
   `ResearchLog/`, and active artifacts referenced by those files.

2. Treat `RawSources/` as immutable. Read from it only when needed to ground a
   claim, resolve uncertainty, or check whether a finding is supported by
   primary material.

3. Check `SOURCES.md` and `sources.lock.json` against `RawSources/` and
   identify new, missing, renamed, hash-changed, or uncataloged source files or
   source bundles. If the user asks only to summarize, report catalog drift in
   chat. Update `SOURCES.md` or `sources.lock.json` only when the user
   explicitly asks to refresh or update files.

4. Produce a concise current-state summary:
   - active goal and current session objective;
   - reliable claims, their status, and the evidence supporting them;
   - open gaps, stale claims, or conflicts across planning files;
   - experiment, artifact, or reproducibility drift when relevant;
   - one concrete next research session scoped to one full research workday with objective,
     prerequisites, expected artifact, and stopping criterion.

5. If the user asks only to summarize, report the status in chat and do not edit
   files.

6. If the user explicitly asks to refresh or update planning files, make minimal
   targeted edits. Usually update `FINDINGS.md`, `EXPERIMENTS.md`,
   `ARTIFACTS.md`, `REPRODUCIBILITY.md`, and `NEXTSTEP.md` according to what
   changed. Edit `SOURCES.md` only when source-catalog drift exists or source
   metadata has changed. Edit `GOALS.md`, `OPTIONAL_GOALS.md`, or `AGENTS.md`
   only when the project goal, optional-goal set, or workflow policy has
   actually changed.

7. Preserve user-written content unless replacement is directly requested or is
   clearly necessary to remove stale, conflicting, or misleading planning
   context. When replacing content, keep the active conclusion traceable to
   `RawSources/`, `ResearchLog/`, computations, or clearly labeled conjecture.

## Research Session Mode

Use this mode when the user asks to work on the project, make progress,
continue, resume, or determine what to do next.

Start of session:

1. Read `GOALS.md`, `FINDINGS.md`, `NEXTSTEP.md`, `SOURCES.md`, and any
   relevant `EXPERIMENTS.md`, `ARTIFACTS.md`, `REPRODUCIBILITY.md`, and
   `ResearchLog/` entries.
2. State the active objective, expected artifact, stopping criterion, and any
   explicit out-of-scope items from `NEXTSTEP.md`.
3. Create or append to a dated research log entry only when the user asks to
   record the session or when files are being changed.

End of session:

1. Update `FINDINGS.md` with any reliable claim, negative result, conjecture,
   or stale/refuted claim. Do not leave important conclusions only in chat.
2. Update `EXPERIMENTS.md`, `ARTIFACTS.md`, or `REPRODUCIBILITY.md` if
   computations, generated outputs, commands, environments, or artifact
   dependencies changed.
3. Update `NEXTSTEP.md` with exactly one concrete next full-workday session.

## Experiment Audit Mode

Use this mode when the user asks to validate, reproduce, summarize, compare, or
audit computational experiments, solver outputs, generated instances, benchmark
tables, figures, or result artifacts.

1. Inspect relevant environment and artifact context when present:
   `Project.toml`, `Manifest.toml`, `pyproject.toml`, `requirements.txt`,
   `environment.yml`, `src/`, `scripts/`, `experiments/`, `instances/`,
   `results/`, `figures/`, `paper/`, `EXPERIMENTS.md`, `ARTIFACTS.md`, and
   `REPRODUCIBILITY.md`.
2. For solver-heavy work, record solver name and version when available,
   termination status, objective or bound information, primal-dual gap or MIPGap
   when relevant, feasibility tolerance, time limit, random seed, number of
   threads, and hardware information when material. Omit or redact
   license-sensitive configuration.
3. Classify evidence as reproduced, partial, failed, stale, or not attempted.
   Do not convert solver output into an exact mathematical certificate unless
   the status, tolerances, gap, and log evidence support that interpretation.
4. Update `EXPERIMENTS.md` only when the user asks to refresh files or when the
   active task requires recording changed computations. Otherwise report the
   audit in chat.

## Compactification Mode

Use this mode when asked to compact, declutter, archive, or reorganize a
research repository by moving files that are useful historical or side-goal
artifacts but are not directly needed for the active core research goals.

The default archive target is a root-level `Archive/` directory in the research
repository. Do not use `ResearchLog/Archive/` as the default archive location.
Repositories initialized with this skill may already contain an empty root-level
`Archive/`; reuse that directory when present.

### Core Rule

Plan first, then ask for explicit user approval before moving or editing files.
Do not move files immediately on the first pass unless the user has already
supplied an exact approved move list.

Compactification should reduce active-repo clutter without deleting evidence.
It should preserve useful historical artifacts in `Archive/` and keep active
research files easy to consult for the current goals.

### Required Context

Before proposing any move plan, inspect the repository context:

- `AGENTS.md`
- `GOALS.md`
- `SOURCES.md`
- `FINDINGS.md`
- `NEXTSTEP.md`
- `OPTIONAL_GOALS.md`
- `EXPERIMENTS.md`
- `ARTIFACTS.md`
- `REPRODUCIBILITY.md`
- `ResearchLog/`
- common artifact directories if present, such as `results/`,
  `experiments/`, `figures/`, `scripts/`, `src/`, `notebooks/`,
  `mathematica/`, `instances/`, `models/`, `paper/`, and `RawSources/`

Use `rg` and `find`/`rg --files` to inventory files and references. Prefer
repository evidence over filename intuition.

### Protected Files And Folders

Never archive, move, delete, or rename these as part of compactification unless
the user explicitly asks for that exact action. Planning files may be minimally
edited during compactification only after explicit approval of the
compactification plan, and only for path-reference updates or short
archival-status notes. Do not rewrite mathematical, computational, or strategic
claims during compactification.

- `RawSources/`
- `.git/`
- `.chatgpt_handoffs/`
- `AGENTS.md`
- `GOALS.md`
- `SOURCES.md`
- `FINDINGS.md`
- `NEXTSTEP.md`
- `OPTIONAL_GOALS.md`
- `EXPERIMENTS.md`
- `ARTIFACTS.md`
- `REPRODUCIBILITY.md`
- current active implementation files required by `NEXTSTEP.md`
- current baseline/source snapshots required by `GOALS.md` or `FINDINGS.md`

Treat `RawSources/` as immutable primary material. Read only.

### Classification

Classify repository files into exactly three groups before proposing a move
plan.

Active/Core: keep files active when they are directly needed to understand or
advance the current `GOALS.md`, `FINDINGS.md`, `EXPERIMENTS.md`,
`ARTIFACTS.md`, `REPRODUCIBILITY.md`, or `NEXTSTEP.md`. This includes current
mathematical formulations and baseline snapshots, current derivations or
implementation specifications, active source code/scripts/notebooks/data used
by the next session, current default choices and certificate evidence, and files
cited as current evidence in `FINDINGS.md`. A file is Active/Core if it is part
of a dependency chain for a current claim, theorem, table, figure, benchmark,
source catalog entry, or next-session objective. Do not classify result files,
generated instances, plotting scripts, or solver logs as archive candidates
merely because they are old; first check whether they support `FINDINGS.md`,
`ARTIFACTS.md`, `paper/`, or `NEXTSTEP.md`.

Archive Candidate: propose files for archive when they are useful historical
evidence but not needed for active progress. This can include superseded
Markdown notes, side-goal investigations, exploratory diagnostics, old
solver-result CSVs or logs, obsolete plots/reports/notebooks/figures, temporary
side-experiment scripts, and administrative handoff or approval notes whose
conclusions are already summarized in active files. Archive candidates are not
"bad" files; they are useful but no longer part of the active working set.
For each archive candidate or coherent file group, provide brief
evidence-grounded rationale fields: `What it contains` and `Why archive it`.
Ground these descriptions in inspected file contents, repository references,
or clear filename/context evidence. If the file's purpose or archival rationale
cannot be determined confidently, classify it as Needs User Decision instead of
guessing.

Needs User Decision: use this category when repository evidence does not
determine whether a file is active/core or side-goal material. Ask the user
before moving these files.

### Archive Layout

Preserve each archived file's repository-relative path inside root `Archive/`.

Examples:

- `ResearchLog/foo.md` -> `Archive/ResearchLog/foo.md`
- `results/side-run.csv` -> `Archive/results/side-run.csv`
- `scripts/side_experiment.jl` -> `Archive/scripts/side_experiment.jl`
- `ResearchLog/Archive/old.md` -> `Archive/ResearchLog/Archive/old.md`

If the repository already has a nested archive such as `ResearchLog/Archive/`,
propose migrating it into root `Archive/` while preserving path context. Do not
flatten archived files unless the user explicitly asks.

Before moving a file, check whether the destination path already exists. If it
exists, stop and ask the user how to handle the conflict.

### Git-Aware Moves

Before proposing moves, run:

```bash
git rev-parse --is-inside-work-tree
git status --short
```

If inside a Git repository, report dirty files in the approval plan and classify
approved move sources as tracked or untracked. After approval, use `git mv` for
tracked files and `mv` for untracked files. Do not compactify across a dirty
working tree without reporting the dirty files in the approval plan.

### Approval Plan

After inspection, present a compactification plan with:

- exact active/core files to keep;
- archive candidates in a table with source path, destination path,
  `What it contains`, and `Why archive it`;
- exact files needing user decision;
- references that must be updated;
- Git status and whether approved moves would use `git mv` or `mv`;
- files and folders intentionally left untouched.

Ask for explicit approval before making any moves or path edits.

### Implementation After Approval

After the user approves an exact move plan:

1. Create root `Archive/` if absent and create destination subdirectories.
2. Move only approved files, using `git mv` for tracked files and `mv` for
   untracked files when inside a Git repository.
3. Update path references in `FINDINGS.md`, `NEXTSTEP.md`, `GOALS.md`,
   `SOURCES.md`, `OPTIONAL_GOALS.md`, `EXPERIMENTS.md`, `ARTIFACTS.md`,
   `REPRODUCIBILITY.md`, remaining active `ResearchLog/` notes, and archived
   notes when they reference other archived files.
4. Append the approved move records to `Archive/ARCHIVE_MANIFEST.md` with date,
   source path, destination path, reason, approval note, and reference updates.
5. Do not rewrite mathematical claims except for path updates and short
   archival-status notes when necessary.
6. Do not delete archived files.

Use `apply_patch` for manual file edits. For moves, use non-destructive shell
commands such as `mkdir -p` and `mv` after approval.

### Verification

Run checks appropriate to the approved move plan. At minimum:

```bash
test -d Archive
find Archive -type f -print | sort
find . -path './Archive' -prune -o -type f -print | sort
```

Search for stale references to old locations and confirm references point to
archived locations where appropriate:

```bash
rg "old/path/or/filename"
rg "Archive/"
```

Confirm protected folders were not moved:

```bash
test -d RawSources
test -f GOALS.md
test -f SOURCES.md
test -f FINDINGS.md
test -f NEXTSTEP.md
test -f EXPERIMENTS.md
test -f ARTIFACTS.md
test -f REPRODUCIBILITY.md
```

If the repository has a current test or construction-check command that is
cheap and relevant, run it only when it helps confirm that active files were not
broken by path rewrites.

### Reporting

In the final response, report files moved to `Archive/`, active files left in
place, references updated, verification commands and outcomes, and any files
left in "needs user decision." Keep the report concise, group long move lists
by directory when possible, and preserve archive rationale where useful without
repeating large approval tables unnecessarily.

## File Roles

- `AGENTS.md`: repository conventions, file roles, `RawSources/` immutability, session workflow, reproducibility expectations, and update policy.
- `GOALS.md`: rigorous research goal, mathematical context, deliverables, success criteria, known constraints, and session-sized subgoals.
- `SOURCES.md`: root-level catalog of immutable/raw source files and source bundles, including source ID, description, relevance, hash when available, provenance or citation metadata, and links to findings, goals, or artifacts when useful.
- `OPTIONAL_GOALS.md`: optional, deferred, paused, archived, or experimental goals with status, motivation, activation conditions, and evidence links. This is a parking lot, not the active next session.
- `FINDINGS.md`: claim/evidence ledger for current findings, attempted approaches, proof status, computational evidence, literature support, conjectures, refutations, assumptions, dependencies, open gaps, and reliability notes.
- `EXPERIMENTS.md`: reproducible experiment ledger with research question, command, environment, solver/configuration, seeds, inputs, outputs, status, and supported claim IDs.
- `ARTIFACTS.md`: map from paper figures, tables, generated outputs, benchmark files, and other research artifacts to producing commands, inputs, and supported claims.
- `REPRODUCIBILITY.md`: environment, setup, dependency, solver, hardware, data-handling, and rerun instructions needed to reproduce current computational evidence.
- `NEXTSTEP.md`: exactly one concrete next research session scoped to one full research workday, including objective, prerequisites, steps, expected artifact, and stopping criterion.
- `RawSources/`: immutable primary input material. Read only.
- `ResearchLog/`: user-provided or session-generated research notes, dated logs, computations, and derivation records.
- `Archive/`: root-level home for useful historical, side-goal, superseded, exploratory, or otherwise non-core artifacts preserved by relative path. This is not a replacement for `OPTIONAL_GOALS.md`; active optional directions stay in `OPTIONAL_GOALS.md`.

## Writing Policy

- Keep mathematical claims traceable to `RawSources/`, `ResearchLog/`,
  computations, literature citations, proof notes, or clearly labeled
  conjecture.
- Distinguish proven claims, checked derivations, computed evidence,
  literature claims, conjectures, refutations, and claims needing verification.
- Do not present computational evidence as a theorem. Do not present solver
  output as an exact certificate unless solver status, tolerances, gaps, and
  logs support that interpretation.
- Mark uncertainty explicitly, especially when evidence is partial, computational, heuristic, or source-dependent.
- Keep session plans small enough that a researcher can complete or falsify them in one full research workday.
- Treat a full research workday as a focused workday, not an around-the-clock calendar-day window.
- Keep `NEXTSTEP.md` focused on one active session. Put optional or speculative follow-ups in `OPTIONAL_GOALS.md` with explicit activation conditions.
- When artifacts are archived, keep the active conclusion or decision in `FINDINGS.md`, `GOALS.md`, `NEXTSTEP.md`, or `OPTIONAL_GOALS.md` as appropriate, and point to `Archive/` only when historical detail is needed.
- During status refresh, prefer summarizing in chat unless the user explicitly asks to update files.
- Prefer clean, literate research exposition with reproducible computational instructions where relevant.

## Source Catalog Policy

- Keep `SOURCES.md` as the root-level index of `RawSources/`; do not move,
  rename, normalize, or edit files inside `RawSources/` while cataloging them.
- Prefer one catalog entry per meaningful source file or source bundle rather
  than one entry per incidental generated file.
- Each entry should include source ID, path, source type, immutability, hash
  when available, role or relevance, provenance/citation metadata when known,
  version/date when known, and notes on how it supports `GOALS.md`,
  `FINDINGS.md`, or `ARTIFACTS.md`.
- Mark unknown provenance, uncertain citation data, or unclear relevance
  explicitly. Do not invent bibliographic metadata or source claims.
- During status refresh, report uncataloged, missing, or renamed sources before
  editing `SOURCES.md`; update the catalog only when the user explicitly asks
  to refresh or update files.

## Claim And Evidence Policy

Use the detailed schema in `references/claim-evidence-protocol.md` when
initializing or substantially refreshing `FINDINGS.md`.

- Treat a claim, not a file, as the unit of truth.
- Give stable IDs to important claims, assumptions, theorems, counterexamples,
  experiments, sources, and artifacts when they are referenced across files.
- Label each finding with one of: `Proven`, `Derivation checked`, `Computed`,
  `Literature`, `Conjectured`, `Refuted`, or `Needs check`.
- Keep negative results and counterexamples visible. They are research findings,
  not clutter.

## Reproducibility Policy

Use `references/reproducibility-protocol.md` when initializing or refreshing
`EXPERIMENTS.md`, `ARTIFACTS.md`, or `REPRODUCIBILITY.md`.

- Prefer reproducible scripts over notebook-only workflows.
- Record commands, seeds, solver versions, termination statuses, relevant
  tolerances, time limits, threads, and output artifacts.
- For Julia projects, prefer `julia --project=.` and preserve `Project.toml`
  and `Manifest.toml` when they define the active environment.
- For Mathematica notebooks, keep a text-exported `.wl` file or summary note
  when possible.

## Bundled Resources

- `scripts/init_research_repo.py`: scaffold a research repository from bundled
  templates without overwriting nonempty files.
- `scripts/audit_sources.py`: audit `RawSources/` hashes against
  `sources.lock.json` and report catalog drift without mutating `RawSources/`.
- `assets/templates/`: default templates for planning, claim/evidence,
  experiment, artifact, and reproducibility files.
- `references/claim-evidence-protocol.md`: detailed claim, assumption,
  theorem, and negative-result ledger guidance.
- `references/reproducibility-protocol.md`: experiment, artifact, solver, and
  environment audit guidance.
- `references/compactification-rubric.md`: detailed compactification and
  archive-manifest guidance.
