---
name: lean-verify
description: Formalize and verify optimization theorem, proof, and certificate targets in Lean/Lake using ChatGPT Pro blueprints only as proof-planning aids and local agentic Lean implementation as the execution path. Use for AutoOPT Stage 3, or standalone optimization-theorem verification, when Codex needs to turn detailed LaTeX/Markdown theorem proofs, symbolic fitting output, optimization certificate data, or an existing Lean/Lake project into checked Lean artifacts, repair proof scripts, build source-to-Lean project module graphs, and certify only what `lake build` verifies without `sorry`, `axiom`, `admit`, or `unsafe`; when feasible, close out with human-approved `Challenge.lean`/`Solution.lean`/`config.json` wrappers and comparator replay as additional evidence, including platform-specific closeout on Linux, native macOS, and Windows 11 WSL2.
---

# Lean Verify

## Core Rule

Use this skill for Lean formalization of optimization-related theorem, proof,
and certificate targets. Suitable targets include paper theorems, convergence
proofs, algebraic optimization lemmas, recurrence or stepsize arguments,
performance bounds, PEP upper-bound certificates, and symbolic dual-certificate
proofs, provided the user supplies a detailed mathematical statement and proof
source. The verifier is Lean/Lake, not the model or host agent that wrote the
proof script. Do not record a Lean claim unless the target theorem checks with
the project's Lean toolchain and the project has no `sorry`, `axiom`, `admit`,
or `unsafe` in its Lean source. When the project has a comparator-facing theorem
surface, treat comparator replay as the default closeout path after successful
build and hygiene, but claim comparator evidence only after the user approves
the `Challenge.lean`, `Solution.lean`, and `config.json` surface and the replay
actually succeeds.

This skill is intentionally scoped to optimization theorem verification. It is
not a general theorem-proving skill, and it does not discover theorems, proofs,
or certificates. It formalizes a target supplied by the paper proof,
Markdown/LaTeX proof notes, symbolic-fitting stage, existing Lean project, or an
approved proof-planning consultation.

## Modes

Choose one mode before acting.

### Assisted Source-To-Lean Mode

Use this as the default for a new optimization theorem, proof, or certificate
target when no local Lean project already verifies the target. Load
`references/chatgpt-pro-blueprint-to-agentic-lean.md`. When the target is a PEP
upper-bound or symbolic dual-feasibility certificate, also load
`references/pep-certificate-formalization.md`.

The standard path is:

1. identify the LaTeX/Markdown sources and prepare a formalization manifest;
2. send only approved directed context to ChatGPT Pro when a proof-planning
   blueprint is needed;
3. extract a self-contained Lean blueprint delimited by
   `BEGIN_LEAN_BLUEPRINT` and `END_LEAN_BLUEPRINT`;
4. audit the blueprint against the LaTeX sources and reject silent theorem
   weakening, missing side conditions, or unmarked uncertainty;
5. have Codex, Claude Code, or another Lean-capable host agent create the
   Lean/Lake project, module graph, theorem wrappers, comparator-facing files
   when feasible, and proof files locally;
6. run local Lean/Lake and hygiene validation before making any verification
   claim;
7. when comparator replay is feasible, prepare `Challenge.lean`,
   `Solution.lean`, and `config.json`, ask the human researcher to approve
   their theorem surface and permitted axioms, select the supported platform
   route in `references/comparator-platforms.md`, then run comparator replay
   and record the command/output.

### Direct Lean Repair Mode

Use this when a Lean/Lake project is already present, or when the user
explicitly asks the host agent to repair Lean files directly. Load
`references/lean-build-loop.md` and work lemma by lemma without changing the
mathematical target.

## Model Roles

- **ChatGPT Pro** may produce proof-planning blueprints, theorem inventory
  suggestions, lemma dependency graphs, and uncertainty flags. It is a
  consultant, never a verifier.
- **Codex, Claude Code, or another Lean-capable coding agent** owns blueprint
  intake, theorem-statement audit, Lean/Lake project creation, Lean file
  generation, proof repair, build-loop validation, and comparator-wrapper
  preparation.
- **Lean/Lake** is the final verifier. Required checks are `lake build`, no
  `sorry`, no user-declared `axiom`, no `admit`, and no `unsafe`.
- **Human researcher** approves the final theorem surface before a comparator
  replay is used as evidence: `Challenge.lean`, `Solution.lean`, `config.json`,
  theorem names, and permitted axioms.
- **Comparator** is an optional additional checker used by default when the
  project has a comparator-compatible wrapper pair. It is not a substitute for
  `lake build` and hygiene.

## Comparator Platform Policy

Load `references/comparator-platforms.md` before preparing or approving a
Comparator command. Use exactly one supported route:

- On Linux, use real Landrun and the ordinary Comparator instructions.
- On native macOS, use the official upstream `scripts/fake-landrun.sh`.
  Disclose that this route is unsandboxed before approval. A successful,
  human-approved replay through that official shim qualifies for
  `Lean+comparator verified`.
- On Windows 11, run Comparator entirely inside WSL2. Verify WSL2, systemd,
  Landlock, and real Landrun first, then follow the ordinary Linux instructions
  verbatim inside WSL2. A successful replay qualifies for
  `Lean+comparator verified`.

Do not use native Windows, WSL1, or an unofficial no-op shim as a qualifying
route. Across all supported routes, record the host and execution operating
systems, sandbox backend, tool revisions and hashes, approved command, exit
status, and output. The evidence label records successful Comparator replay;
the evidence record separately states whether execution was sandboxed.

## Required Inputs

Before writing Lean, identify:

- the paper theorem, optimization proof, or certificate claim to formalize;
- the detailed LaTeX/Markdown proof or proof notes to use as the source;
- the mathematical setting, domains, definitions, notation, and library
  background expected in Lean;
- the intended theorem statement, allowed assumptions, excluded claims, and
  correspondence to the paper-facing claim;
- the proof structure: key lemmas, induction or recurrence arguments,
  algebraic identities, nonnegativity facts, monotonicity facts, convexity or
  smoothness facts, and any finite-sum or telescoping steps;
- for certificate targets, the symbolic stepsizes, multipliers, potentials,
  dual variables, finite index sets, recurrence definitions, PEP inequalities
  being combined, and certificate-feasibility identities;
- the comparator theorem surface, wrapper paths, permitted axioms, host and
  execution operating systems, sandbox backend, tool paths and revisions, and
  comparator command when comparator replay is feasible;
- the artifact location where build logs and closeout notes will be recorded.

If these inputs are not explicit, stop and prepare a proof-planning request
instead of guessing the theorem.

## Workflow

1. **Ground the target.** Read the LaTeX/Markdown proof, paper proof,
   symbolic-fitting output, existing Lean project, and available theorem or
   certificate data. Load
   `references/pep-certificate-formalization.md` when the proof is a PEP
   upper-bound or inner-dual certificate.
2. **Choose the mode.** For a new source-to-Lean formalization, use Assisted
   Source-To-Lean Mode. For an existing Lean/Lake project, use Direct Lean
   Repair Mode.
3. **Prepare the manifest.** Record the theorem inventory, source-to-claim
   map, formalization scope, excluded claims, definitions, side conditions,
   proof obligations, algebraic identities, target declarations, and validation
   commands.
4. **Plan the project architecture.** Split the proof into modules for
   definitions, domain lemmas, theorem-specific supporting lemmas, recurrence or
   finite-sum identities, optimization-model facts, certificate feasibility when
   applicable, algorithm semantics when applicable, and final theorem wrappers.
   Load
   `references/source-to-lean-project-patterns.md` for multi-file case-study
   patterns.
5. **Use an external blueprint only when needed.** Follow
   `references/chatgpt-pro-blueprint-to-agentic-lean.md` for approve-before-send
   packaging, blueprint extraction, transcript archival, and blueprint intake.
   Use `references/chatgpt-pro-consultation-protocol.md` for smaller planning
   gaps.
6. **Create or inspect the Lake project.** Use an existing `lean-toolchain`,
   `lakefile.lean`, or `lakefile.toml` when present. Otherwise create the
   smallest Lean 4/Lake project needed for the proof.
7. **Formalize lemma by lemma.** Write the theorem statement first, then prove
   supporting lemmas in small increments. Do not weaken assumptions, change the
   mathematical target, or add axioms to make the proof compile.
8. **Run the build loop.** Load `references/lean-build-loop.md`. Build after
   each coherent lemma group, repair from Lean errors, and record substantive
   theorem-statement changes.
9. **Validate the Lean layer.** Run `lake build` and
   `scripts/check_lean_project.py <project-root>`. Run axiom audits when the
   project requires them. Record the toolchain, command, build result, theorem
   names, permitted axioms, elapsed formalization time when available, and any
   warnings. At this point the strongest justified label is `Lean
   build+hygiene verified`.
10. **Close out the comparator layer when feasible.** Prepare or inspect
    `Challenge.lean`, `Solution.lean`, and `config.json`; load
    `references/comparator-platforms.md`; validate the selected platform route;
    show the theorem names, wrapper paths, permitted axioms, platform, sandbox
    backend, tool revisions, and comparator command to the human researcher;
    and wait for explicit approval before comparator replay. On native macOS,
    the approval must explicitly acknowledge that official `fake-landrun.sh`
    provides no sandbox. If replay succeeds through a supported route, record
    the command/output and classify the result as `Lean+comparator verified`.
    If replay is infeasible, blocked, or not run, record the blocker or
    non-applicability note without claiming comparator evidence.

## Claim Discipline

- `Lean build+hygiene verified` requires successful Lean/Lake output, no
  forbidden placeholders, and recorded artifact paths.
- `Lean+comparator verified` additionally requires human-approved
  `Challenge.lean`, `Solution.lean`, and `config.json`, followed by successful
  comparator replay through a supported platform route with recorded
  command/output and platform/sandbox metadata. Successful native macOS replay
  through the official unsandboxed `fake-landrun.sh` qualifies, as does
  successful Windows 11 WSL2 replay through real Landrun after the required
  preflight.
- A blueprint, model transcript, or passing informal review is `Conjectured` or
  `Needs check`, not proof.
- Solver output, symbolic fitting output, and informal proof-planning output are
  evidence for the theorem or certificate target, not Lean verification.
- If the formal theorem differs from the paper theorem, record the difference
  explicitly before claiming success.

## Resources

- `references/chatgpt-pro-blueprint-to-agentic-lean.md`: assisted
  source-to-Lean workflow from LaTeX proof sources to ChatGPT Pro blueprint,
  local agentic Lean project creation, and local Lean verification.
- `references/source-to-lean-project-patterns.md`: reusable module patterns for
  multi-file optimization case studies, including general theorem targets,
  gradient-rate results, and function-value certificate projects.
- `references/pep-certificate-formalization.md`: PEP upper-bound certificate
  structure and Lean obligation template.
- `references/chatgpt-pro-consultation-protocol.md`: how to use ChatGPT Pro for
  small proof-planning gaps without trusting it as a verifier.
- `references/lean-build-loop.md`: Lean project setup, blueprint intake, repair
  loop, validation, and stopping rules.
- `references/comparator-platforms.md`: qualifying Linux, native macOS, and
  Windows 11 WSL2 Comparator routes, preflights, approval disclosures, and
  evidence requirements.
- `scripts/check_lean_project.py`: static Lean-source hygiene checker with an
  optional `lake build` run capped at 60 minutes.
