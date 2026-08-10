# Lean Build Loop

Use this reference while creating or repairing a Lean project.

## Project Setup

- Use the existing `lean-toolchain` and Lake files when present.
- If no project exists, create a minimal Lean 4/Lake project and pin the
  toolchain.
- Prefer narrow imports once the proof stabilizes, but broad `Mathlib` imports
  are acceptable during early scaffolding.
- Keep generated or repaired Lean files in the active project or run folder,
  not in immutable source material.

## Blueprint And Generated-File Intake

When starting from a model blueprint or generated Lean files:

- preserve the original blueprint, archive, or raw generated files before
  editing;
- keep `Blueprint_Prompt.md` unchanged unless a derived copy is documented;
- inspect the project root before building and locate `lean-toolchain`,
  `lakefile.lean` or `lakefile.toml`, theorem files, and summaries;
- compare the generated theorem statements and definitions against the
  blueprint and source proof before repair;
- reject silent theorem weakening, missing side conditions, changed index
  ranges, or unexplained normalization changes before repair;
- run `scripts/check_lean_project.py <project-root> --no-build` before the
  first full build;
- treat `.lake/` as a local rebuild cache, not a durable artifact or commit
  target.

## Repair Loop

Work in small increments:

1. State the theorem and the next small lemma.
2. Run `lake build` or `lake env lean path/to/file.lean`.
3. Read the first relevant Lean error.
4. Repair the local lemma or statement.
5. Rebuild before moving to the next lemma group.

Do not add `sorry`, `axiom`, `admit`, or `unsafe`. Do not hide a failed proof
behind a weaker theorem statement. If the statement must change, record the
mathematical reason.

## Validation

Before closeout, run from the project root:

```bash
lake build
```

Then run:

```bash
python3 path/to/lean-verify/scripts/check_lean_project.py .
```

For a static-only audit of an already-generated project, use:

```bash
python3 path/to/lean-verify/scripts/check_lean_project.py . --no-build
```

Record:

- Lean and Lake versions;
- toolchain file contents;
- command and exit status;
- theorem files checked;
- exact theorem names;
- permitted axioms or explicit confirmation that none were added beyond the
  accepted kernel/library baseline;
- warnings that may matter;
- confirmation that no forbidden proof placeholders or unsafe declarations are
  present;
- elapsed formalization time when available;
- artifact paths for build logs, hygiene output, and closeout notes.

## Comparator Closeout

Comparator replay is the default closeout layer when the project has, or can
reasonably expose, a comparator-compatible theorem surface. It comes after the
Lean build and hygiene checks; it does not replace them.

Load `comparator-platforms.md` and validate one supported platform route before
preparing the command.

Before running comparator:

- prepare or inspect `Challenge.lean`, `Solution.lean`, and `config.json`;
- verify that the theorem names and permitted axioms match the intended paper
  claim;
- show the human researcher the wrapper paths, theorem names, permitted axioms,
  host and execution platforms, sandbox backend, tool revisions, and exact
  comparator command;
- on native macOS, disclose that the required official `fake-landrun.sh` route
  is unsandboxed and obtain explicit approval of that execution mode;
- wait for explicit approval of the wrapper/config surface.

After approval, run the recorded command and save its output, platform route,
and sandbox metadata. Claim `Lean+comparator verified` only if replay succeeds
through a route supported by `comparator-platforms.md`. If wrappers are
missing, platform preflight fails, the toolchain is unavailable, the
researcher does not approve the surface, or the replay fails, record the
blocker or non-applicability note and keep the claim at
`Lean build+hygiene verified` or `blocked/stubbed`, as appropriate.

## Stopping Rules

Mark the Lean build+hygiene layer complete only when the target theorem builds
cleanly and the hygiene check passes. Mark the comparator layer complete only
when the approved `Challenge.lean`, `Solution.lean`, and `config.json` replay
successfully.

Mark it blocked, rather than weakening the theorem, when:

- the formalization manifest is mathematically incomplete;
- a required side condition is false or absent;
- the Lean statement no longer matches the paper claim;
- the same proof obligation remains unresolved after two focused repair
  attempts and needs a mathematical decision.
- the comparator wrapper/config surface cannot be made faithful without a
  mathematical decision or unapproved theorem change.
