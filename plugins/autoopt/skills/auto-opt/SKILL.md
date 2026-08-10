---
name: auto-opt
description: Run, resume, or coordinate a human-gated AutoOPT pipeline session for optimization-research automation inside a versioned research repository. Stages delegate to existing skills by name; Stage 0 repository grounding via research-repo-manager, Stage 1 numerical algorithm design via bnb-pep-skill, Stage 2 symbolic fitting of candidate formulas and proofs via frontier-llm-consult, which routes to the default external chatgpt-pro-session or an explicitly invoked native solve-with-highest-reasoning campaign with archived evidence, and Stage 3 Lean verification via lean-verify when available. Use when a researcher asks to orchestrate, chain, or gate these stages end-to-end, prepare a stage handoff, or close out a pipeline session with ledger updates. Every stage boundary requires explicit human approval; the skill automates the glue between stages, never the approvals; model outputs are candidates, never proofs.
---

# AutoOPT Orchestrator

## Core Rule

AutoOPT names a human-gated pipeline discipline, not a software system and not
an autonomous agent. This skill is a thin pipeline controller: it automates the
glue between stages and never automates the approvals. Stop at every stage
boundary, present a gate brief, and wait for the user's explicit approval.
Treat every model-produced Stage 2 output as a candidate mathematical object,
never as a proof. Do not weaken, skip, or batch the gates, and do not present
this orchestrator as removing human judgment from the pipeline.

## Architecture

Each stage delegates to an existing skill by name and stores its artifacts in
the target research repository. The persistent state of a pipeline run
therefore lives in the repository's versioned ledgers and run folders, never in
this skill and never in any host agent's internal memory. The pipeline is
host-agnostic: any agent harness that loads skills can operate it.

| This skill | Pipeline stage | Delegated to |
|---|---|---|
| Stage 0: repository grounding | precondition | `research-repo-manager` |
| Stage 1: numerical algorithm design | numerical method design | `bnb-pep-skill` |
| Stage 2: symbolic fitting | symbolic fitting of candidate formulas and proofs | `frontier-llm-consult`, which routes to default external `chatgpt-pro-session` or explicitly invoked native `solve-with-highest-reasoning` |
| Stage 3: Lean verification | Lean/Lake formalization, hygiene checks, and comparator replay when feasible | `lean-verify` when available; otherwise stub |
| Session closeout | human interpretation | the researcher, with `research-repo-manager` ledger conventions |

Terminology guard: pipeline stage numbers (Stage 0-3 above) are distinct from
the BnB-PEP Algorithm's internal stage numbers. Inside pipeline Stage 1, the
delegated `bnb-pep-skill` runs only the BnB-PEP Algorithm's Stage 1/2 local
workflows; the BnB-PEP Algorithm's Stage 3 (spatial branch-and-bound) is a
different object from pipeline Stage 3 (Lean formalization) and stays out of
scope. Qualify the word "Stage" whenever both senses could be read.

## Required Companion Skills

`research-repo-manager` and `bnb-pep-skill` must be installed for Stages 0 and
1. Stage 2 requires `frontier-llm-consult` and the selected route:
`chatgpt-pro-session` for external ChatGPT Pro consultations, or
`solve-with-highest-reasoning` for an explicitly invoked native Codex
campaign. ChatGPT Pro is the sole external route and the default for ordinary,
ambiguous, persistent, and bounded one-shot work. A bounded one-shot external
review is one approved turn in a new ChatGPT Pro session, not a separate
backend. The native route is not an external backend or an independent
second-model opinion. Recommend the native route only for one
exceptionally difficult, sharply defined target when repository exploration or
local tools materially help, the user explicitly invokes
`$solve-with-highest-reasoning`, and the user accepts its Goal mode, equivalent
persistent mechanism, or disclosed checkpointed fallback when neither is
available, plus its user-confirmed minimum-duration and 180-minute
per-code-or-solver-execution contracts. The duration defaults to eight elapsed
wall-clock hours and 28,800 logged active-work seconds; a custom `h` hours
requires both `h` elapsed wall-clock hours and `h * 3600` logged active-work
seconds. Exclude the native route when provider diversity or an independent
second-model review is required. In an AutoOPT run, the native skill's
standalone explicit-invocation authorization is necessary but does not replace
this orchestrator's Stage 2 route gate.

Requests for another provider, API or multi-provider routing, or provider
diversity are unsupported by Stage 2. Stop rather than substituting a route.
ChatGPT Pro may provide an external second-model review; the native route
cannot satisfy provider diversity or independence from the current Codex host.

`lean-verify` is required only when a run proceeds to Stage 3 Lean verification.
Before starting a run, confirm that each skill the run will need resolves. If
`frontier-llm-consult` or the selected route is unavailable, stop and report
which stage is blocked. If ChatGPT Pro is selected but unavailable, do not
switch automatically to the native route. If the native route is selected but
its invocation, persistence, capability resolution, or required tools are
unavailable, do not fall back to ChatGPT Pro. Never silently downgrade or
substitute another route.

Do not duplicate companion-skill content here: this skill defines only stage
boundaries, gates, and artifact handoffs.

## Run Artifacts

Each gated run stores its stage artifacts in the target repository under one
run folder, created lazily at the first stage that produces output:

```text
ResearchLog/auto-opt-runs/<YYYY-MM-DD>-<slug>/stage0 ... stage3/
```

For a native Stage 2 route, the authoritative campaign record remains under
`ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/`. The AutoOPT
`stage2/` folder stores compact approval, reference, and candidate artifacts
rather than copying or symlinking that campaign tree.

Load `references/stage-handoff-protocol.md` for the per-stage input/output
contracts, branch-specific gate templates, and evidence-archiving rules.

## Staged Workflow

1. **Stage 0 - repository grounding.**
   - Invoke `research-repo-manager`: Initialization Mode for a new or
     unscaffolded folder; Status Refresh or Research Session Mode for an
     existing repository.
   - Outcome: planning ledgers exist and are current, and immutable raw-source
     material remains read-only.
   - Present the Stage 0 gate brief and wait for explicit approval.

2. **Stage 1 - numerical algorithm design.**
   - Invoke `bnb-pep-skill` inside the repository on the user-specified
     instance. Its internal rules stay fully intact, including its
     derivation-before-Julia approval gate and its BnB-PEP Stage 1/2
     local-workflow-only boundary (no spatial branch-and-bound, no global
     solver paths).
   - Store the derivation Markdown, generated Julia files, and any smoke-test
     output under `stage1/` in the run folder.
   - Present the Stage 1 gate brief and wait for explicit approval.

3. **Stage 2 - symbolic fitting.**
   - Give `frontier-llm-consult` the exact symbolic-fitting target, the relevant
     Stage 1 seed artifacts, the structural constraints, and the requested
     output type. Let it recommend one of two routes:
     `chatgpt-pro-session` for external consultation, or explicitly invoked
     `solve-with-highest-reasoning` for a qualifying native campaign.
     Ambiguous ordinary AutoOPT Stage 2 work defaults to
     `chatgpt-pro-session`. For bounded one-shot external work, use one
     approved turn in a new ChatGPT Pro session.
   - For `chatgpt-pro-session`, assemble one task prompt plus the smallest file
     set that carries the numerical data and structural constraints. Show the
     session configuration, exact outgoing file list or context manifest,
     ChatGPT Pro selection and manifest preview, secrets check, and archive
     destination. Send or upload nothing until the user approves. This outer
     gate remains controlling for the delegated session even if direct
     invocation of its leaf skill would otherwise provide standing upload
     consent.
   - For `solve-with-highest-reasoning`, create no upload package. Require the
     user's explicit skill invocation. Before Goal setup, repository grounding,
     campaign initialization, or clock start, let the native skill resolve and
     freeze the user-confirmed duration. A valid duration in the invocation is
     acknowledged without another question; when no duration is supplied, the
     skill presents its eight-hour and 28,800-second default and waits for the
     user to select it or provide `h` hours. Require approval of the exact
     target, admissible output, repository root, Stage 1 seeds, repository
     discovery and source boundaries, immutable and excluded paths, local-write
     scope, relevant local tools, resolved strongest Codex model and highest
     supported reasoning setting with no downgrade, the confirmed duration
     source and floors, persistence mode, 180-minute code-or-solver-execution
     ceiling, restricted public-search policy, and both archive destinations.
     Repository-local exploration may identify and use additional relevant
     files within that approved scope without another gate. A different target
     or repository root, a widened source boundary, or any external transfer
     requires renewed approval. Preserve and do not weaken the frozen duration.
   - Execute only the approved route through `frontier-llm-consult`. For the
     native route, load and follow `solve-with-highest-reasoning` without
     weakening its frozen duration, persistence, capability, audit, source,
     computation, or stopping rules. Do not let the native campaign invoke
     `frontier-llm-consult`, ChatGPT, or another external model unless
     the user separately approves that workflow under its own transfer gate.
   - Archive durable external-route evidence under `stage2/`: ChatGPT Pro
     session metadata, prompt/context manifest, imported response, and turn
     artifacts. For the native route, keep the authoritative campaign under
     `ResearchLog/highest-reasoning-runs/` and store `route-approval.md`,
     `native-campaign-reference.md`, and `candidate.md` under `stage2/`, using
     repository-relative paths and SHA-256 hashes rather than copying or
     symlinking the campaign.
   - Map native campaign status before declaring the stage outcome:
     `prepared`, `running`, or `paused` leaves Stage 2 incomplete and
     resumable; `complete` permits candidate inspection at the Stage 2 gate;
     `incomplete` archives the exact-gap report and leaves partial candidates
     gated; `user_stopped` or `environment_blocked` records Stage 2 as
     interrupted or blocked.
   - Verify-on-return: the researcher checks each returned candidate formula,
     candidate identity, or candidate proof skeleton against the available
     numerical and structural data. Model re-examination is not verification.
     A computer-algebra or other local-tool check carries only the evidence
     status supported by its archived command and output; it does not
     automatically prove the candidate. If a candidate fails these checks,
     record the failure in the ledgers (typically `Refuted`, with the failing
     check) and do not carry it forward.
   - Present the Stage 2 gate brief and wait for explicit approval.

4. **Stage 3 - Lean verification.**
   - Invoke `lean-verify` only after the Stage 2 candidates have been inspected
     and the user approves carrying a specific optimization theorem, proof, or
     certificate target into formalization.
   - The main paper-facing Stage 3 proof class is PEP upper-bound and symbolic
     dual-certificate verification, but the workflow may also formalize other
     detailed optimization theorem/proof targets when the user supplies an
     explicit statement, proof source, assumptions, and scope.
   - If `lean-verify` is unavailable, or if no optimization theorem/certificate
     target is explicit enough to formalize, stop and record the Stage 3 stub
     outcome.
   - No Lean claim is valid until Lean source files, a successful `lake build`,
     and the no-`sorry`/no-`axiom`/no-`admit`/no-`unsafe` hygiene checks are
     recorded.
   - When the Lean project has a comparator-compatible theorem surface,
     comparator replay is the default closeout layer after `lake build` and
     hygiene. The `Challenge.lean`, `Solution.lean`, and `config.json` wrapper
     surface must be approved by the user before replay, and `Lean+comparator
     verified` may be recorded only when the replay actually succeeds.

5. **Session closeout.**
   - Follow `research-repo-manager` end-of-session conventions: route
     conclusions into the claim ledger, record commands and artifacts, and set
     exactly one concrete next session.
   - Human interpretation and write-up remain the researcher's work outside
     this skill.

## Gate Protocol

At every stage boundary, present a gate brief containing: the stage completed;
the artifacts produced, with paths; the evidence status of every claim touched;
the proposed next stage and the inputs it will consume; residual risks; and the
exact approval being requested. For Stage 2, the brief must additionally name
`frontier-llm-consult`, the recommended or selected route, its rationale, and
the applicable branch-specific fields. An external-route brief names the
provider/model or session mode, exact outgoing file list or context manifest,
preview evidence, secrets check, and archive destination. A native-route brief
names the exact target and admissible output, explicit invocation, persistence
mode, resolved model and reasoning setting, duration confirmation, minimum
wall-clock and active-work floors, the code/solver execution ceiling,
repository roots and discovery scope, seed artifacts, immutable/excluded paths,
local-write scope, authorized tools, source and public-search boundary, the
absence of external-model transfer, and both archive destinations. For
Stage 3, the brief must additionally name the theorem
targets, Lean/Lake commands, hygiene output, permitted axioms, any
`Challenge.lean`/`Solution.lean`/`config.json` wrapper paths, comparator
command and status when relevant, host and execution platform, sandbox
backend, strength, and engagement evidence, tool revisions and hashes for Lean,
Lake, mathlib, Comparator, exporter, checker, and Landrun or the official shim,
required unsandboxed-execution disclosure, and whether the user approved the
exact comparator surface and command. Use the template in
`references/stage-handoff-protocol.md`.
Never proceed on silence, and never treat approval at one boundary as approval
for a later boundary.

## Claim Discipline

- Label every recorded claim with exactly one status: `Proven`, `Derivation
  checked`, `Computed`, `Literature`, `Conjectured`, `Refuted`, or `Needs
  check`.
- Prefix every model-produced Stage 2 output with "candidate". Candidates enter the
  ledgers as `Conjectured` or `Needs check` until they pass Lean formalization
  or ordinary mathematical proof.
- Native campaign duration, subagent agreement, campaign-record validation,
  and model self-review do not promote a candidate. A native-route candidate
  remains `Conjectured` or `Needs check` until independently accepted ordinary
  proof or formal verification supports a stronger status.
- Do not present computational evidence as a theorem. Do not present solver
  output as an exact certificate unless solver status, tolerances, gaps, and
  logs support that interpretation.
- No Lean claim is valid until Lean source files, successful checker output,
  and proof-hygiene checks are recorded. Distinguish `Lean build+hygiene
  verified`, `Lean+comparator verified`, and `blocked/stubbed`; do not record
  comparator evidence without approved wrappers/config and a successful replay.
- Route important conclusions into the repository ledgers; never leave them
  only in chat.

## Hard Constraints

- Never edit, rename, move, or delete immutable raw-source material in the
  target repository.
- Never trigger the BnB-PEP Algorithm's Stage 3, spatial branch-and-bound,
  global nonconvex optimization, or any Gurobi global-solver path through
  `bnb-pep-skill`.
- Never send or upload an external consultation bundle without the
  approve-before-send gate, and never attach secrets.
- Never route Stage 2 to another provider, API or multi-provider backend, or a
  provider-diversity panel.
- Never invoke `solve-with-highest-reasoning` implicitly, weaken its selected
  and frozen duration contract, silently downgrade its model or reasoning
  setting, or replace an unavailable selected route with another route.
- Never let the native route transfer repository context to an external model
  without a separate `frontier-llm-consult` approval workflow.
- Never skip durable Stage 2 archiving. Record the route choice and either the
  `chatgpt-pro-session` session metadata, prompts, manifests, imported
  responses, and turn artifacts, or the native route's approval, hashed
  campaign reference, and candidate artifacts.
- Never report a stage as complete without its artifacts stored in the run
  folder.
