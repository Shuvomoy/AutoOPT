# ChatGPT Pro Blueprint To Agentic Lean

Use this reference for Assisted Source-To-Lean Mode: an optimization theorem,
proof, or certificate target with detailed LaTeX/Markdown sources, but no local
Lean project that already verifies the target theorem. For PEP upper-bound or
symbolic dual-feasibility certificates, also use
`pep-certificate-formalization.md`.

## Stage 1: Source Grounding And Manifest

Before using external tools, identify or prepare a formalization manifest. The
manifest should state:

- source files and the claims drawn from each source;
- formalization scope, target theorem names, and excluded claims;
- normalized or parameter-explicit mathematical setting;
- domains, definitions, notation, coercions, and library background expected in
  Lean;
- finite index ranges and horizon assumptions when present;
- proof structure, including main lemmas, induction or recurrence arguments,
  algebraic identities, inequalities, and theorem-specific side conditions;
- definitions of stepsizes, recurrences, multipliers, scalar variables, slack
  matrices, interpolation residuals, algorithm iterates, and PSD witnesses when
  the target is certificate-shaped;
- nonnegativity, equality, recurrence, coefficient-cancellation, interpolation,
  and PSD/slack obligations when applicable;
- final performance measure and theorem statement;
- validation commands, including build, hygiene, axiom-audit, comparator, or
  project-specific checker commands when relevant;
- comparator-facing wrapper targets (`Challenge.lean`, `Solution.lean`,
  `config.json`), theorem names, and permitted axioms when comparator replay is
  feasible.

If the LaTeX sources have notation conflicts, missing side conditions, or
possible source typos, stop and ask for a mathematical decision before
packaging context.

## Stage 2: ChatGPT Pro Blueprint

Use `chatgpt-pro-session` or `chatgpt-pro-handoff` only after the user approves
the outgoing context. Read the selected consultation skill before acting. Use
directed context, not a broad workspace upload, unless the user explicitly
requests broad context. This exact-manifest approval controls when the
consultation is invoked through Lean Verify, even if direct invocation of the
selected consultation skill carries standing upload consent.

The outgoing context should normally include:

- the formalization manifest;
- the detailed LaTeX/Markdown proof;
- source proof sections and internal derivations needed to audit notation;
- relevant macros or notation files;
- this skill's project-pattern references, plus certificate references when the
  target is certificate-shaped.

Inspect the outgoing manifest before upload. Continue only if the file list is
exactly the intended context and contains no unexpected sensitive or irrelevant
material.

Ask the consultant for a blueprint for a Lean-capable coding agent that will
implement and repair the project locally. Require:

- theorem inventory and paper-to-Lean statement mapping;
- source-to-claim map with excluded claims;
- Lean-friendly definitions and index conventions;
- proposed Lake/module graph;
- declaration names and theorem wrappers;
- lemma dependency graph;
- theorem-specific proof obligations, including nonnegativity, equality,
  recurrence, interpolation, and PSD/slack obligations when applicable;
- assumptions that must not be silently strengthened;
- validation plan and evidence-status boundaries;
- proposed comparator-wrapper surface and permitted axioms when the project
  should close with comparator replay;
- explicit uncertainty flags;
- a clearly delimited block:

```text
BEGIN_LEAN_BLUEPRINT
...
END_LEAN_BLUEPRINT
```

Archive the full consultation transcript. Extract only the delimited blueprint
into `Blueprint_Prompt.md` or another clearly named run artifact. Do not treat
the blueprint as proof.

## Stage 3: Blueprint Intake

Before writing Lean, compare the blueprint against the manifest and source
proof:

- reject theorem statements that weaken the paper claim without an explicit
  mathematical reason;
- reject missing side conditions, changed index ranges, or unexplained
  normalization changes;
- mark unsupported claims as out of scope or `Needs check`;
- keep continuous-time, lower-bound, tightness, numerical, and figure-only
  material out of the Lean target unless the user explicitly selects it;
- convert the blueprint into a local implementation plan with module order,
  declaration names, and validation commands.

If the blueprint is incomplete but the mathematical target is clear, repair the
plan locally. If the target is not clear, ask for a mathematical decision or
run a narrower consultation.

## Stage 4: Local Agentic Lean Implementation

The host agent creates and repairs the Lean project locally:

- create or reuse the Lake project and pin the toolchain;
- write `Solution.lean` or other theorem-facing wrappers early, so the final
  theorem surface is fixed before proof details drift; when comparator replay
  is feasible, keep `Challenge.lean`, `Solution.lean`, and `config.json`
  synchronized as the human-approved comparator surface;
- add internal modules in dependency order: definitions, domain facts,
  theorem-specific lemmas, algebraic identities, certificate feasibility when
  applicable, algorithm semantics when applicable, interpolation or
  function-model bridge when needed, convergence, and closeout wrappers;
- build after each coherent lemma group;
- do not add `sorry`, `axiom`, `admit`, `unsafe`, or theorem weakening to make
  progress appear successful.

Generated files are not trusted until local Lean/Lake validation succeeds.

## Stage 5: Local Verification

Run the static hygiene scan before a full build:

```bash
python3 path/to/lean-verify/scripts/check_lean_project.py path/to/project --no-build
```

Then run `lake build` from the project root when the project shape is clear.
The build may recreate `.lake/`; treat `.lake/` as a local rebuild cache, not a
durable artifact or commit target.

Claim `Lean build+hygiene verified` only after:

- `lake build` succeeds for the target project;
- the hygiene checker finds no `sorry`, `axiom`, `admit`, or `unsafe`;
- theorem statements are audited against the blueprint and source proof;
- requested axiom-audit or independent checker commands succeed;
- theorem names, toolchain, commands, artifact paths, permitted axioms,
  warnings, and elapsed formalization time when available are recorded.

When comparator replay is feasible, use it as the default closeout layer after
the Lean build and hygiene layer:

1. prepare or inspect `Challenge.lean`, `Solution.lean`, and `config.json`;
2. show the human researcher the wrapper paths, theorem names, permitted
   axioms, and exact comparator command;
3. run comparator only after explicit approval of that surface;
4. record the comparator command and output.

Claim `Lean+comparator verified` only when the approved comparator replay
succeeds. If the project lacks compatible wrappers, the comparator toolchain is
unavailable, or the user does not approve the wrapper surface, record a
justified comparator blocker/non-applicability note and keep the evidence label
at `Lean build+hygiene verified`.

If the proof does not build, switch to Direct Lean Repair Mode. Do not weaken
the theorem or add placeholders to make the project compile.
