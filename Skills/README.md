# AutoOPT Pipeline Skills

Portable agent skills for **AutoOPT**, a human-gated workflow for automating
optimization research. This folder accompanies a research paper in
preparation on end-to-end automation of optimization research: numerical
algorithm design via performance estimation, LLM-assisted symbolic discovery,
Lean-based formal verification, and human interpretation.

AutoOPT is a workflow discipline, not a software system or an autonomous
agent: each stage is packaged as a portable agent skill, a human researcher
approves every stage boundary, and the persistent state of a research project
lives in versioned repository ledgers rather than in any agent's internal
memory. Any agent harness that loads skills (Claude Code, Codex, and similar)
can host the workflow.

## The pipeline at a glance

![Block diagram of the AutoOPT pipeline: four stages, numerical algorithm design (agentic BnB-PEP), symbolic fitting through an approved frontier-model route, Lean formalization, and human interpretation. The stages are connected left to right, with a human approval gate at every boundary and a research-folder bar beneath that every stage reads from and writes to](assets/autoopt-pipeline.png)

| Stage | What it does | Skill |
|---|---|---|
| 0. Repository grounding | Initialize or refresh the research repository and its planning ledgers | `research-repo-manager` (this folder) |
| 1. Numerical algorithm design | Pose method design as a BnB-PEP instance; derive and implement Stage 1/2 local workflows | `bnb-pep-skill` (this folder) |
| 2. Symbolic fitting | Choose an approved route: an external ChatGPT Pro consultation or an explicitly invoked native Codex highest-reasoning campaign; archive route-specific evidence; treat outputs as candidates | `frontier-llm-consult` (this folder), routing to `chatgpt-pro-session` or `solve-with-highest-reasoning` |
| 3. Lean verification | Formally verify surviving optimization theorem, proof, or certificate candidates in Lean/Lake, then run comparator replay when feasible after wrapper approval | `lean-verify` (this folder) |
| Orchestration | Chain the stages with a human approval gate at every boundary | `auto-opt` (this folder) |

Human interpretation and write-up remain the researcher's work outside the
skills.

## What is in this folder

- **`auto-opt/`**: the thin pipeline-controller skill. It delegates each
  stage to the skill that owns it, stores per-run artifacts in the target
  repository, presents a decision brief at every stage boundary, and never
  proceeds without explicit user approval. Requires the companion skills
  below to be installed.
- **`bnb-pep-skill/`**: formalize, derive, and locally implement
  Branch-and-Bound Performance Estimation Programming (BnB-PEP) instances
  from math or plain English, producing a Markdown derivation and Julia/JuMP
  code for the primal SDP, dual SDP, and Stage 1/2 local workflows.
  Self-contained; start with `bnb-pep-skill/references/onboarding.md`.
- **`frontier-llm-consult/`**: choose between two Stage 2 execution routes.
  It recommends `chatgpt-pro-session` for external ChatGPT Pro Extended
  consultation, including a single bounded turn in a new session, or
  `solve-with-highest-reasoning` for an explicitly invoked native Codex
  campaign whose difficult, sharply defined target benefits from repository
  exploration or local tools. `chatgpt-pro-session` is the default for
  ambiguous or ordinary AutoOPT Stage 2 symbolic-fitting requests. The router
  owns the route-choice gate and candidate-not-proof boundary; each delegated
  skill owns its mechanics. Requests for another provider, provider diversity,
  or multi-provider routing are unsupported and stop at the route gate.
- **`chatgpt-pro-handoff/`**: attended ChatGPT Pro packaging/import helper
  for directed or full-workspace handoffs through Chrome. The persistent
  ChatGPT Pro session skill reuses its packager/importer.
- **`chatgpt-pro-session/`**: maintain a reusable ChatGPT Pro consultation
  session for Stage 2 or other directed reviews when persistent context and Pro
  thinking effort set to Extended are useful. It records session metadata,
  prompts, manifests, uploaded context bundles, and imported responses; local
  implementation of any recommendation remains opt-in.
- **`solve-with-highest-reasoning/`**: run an explicitly invoked native Codex
  campaign on one exceptionally difficult, sharply defined research target.
  The campaign works directly from approved repository roots and seed
  artifacts, may use authorized local mathematical and computational tools,
  and creates no external consultation upload package. It requires the
  strongest available Codex GPT at its highest supported reasoning setting,
  Goal-mode persistence, an equivalent persistent mechanism, or the skill's
  disclosed checkpointed fallback when neither is available, a user-confirmed
  minimum duration, and a 180-minute code-or-solver-execution ceiling. The
  duration defaults to eight elapsed wall-clock hours and 28,800 logged
  active-work seconds; a custom `h` hours requires both `h` elapsed wall-clock
  hours and `h * 3600` logged active-work seconds. The skill resolves and
  freezes this duration before campaign setup, acknowledges a valid duration
  supplied in the invocation without asking again, and otherwise waits for the
  user to accept the default or provide a custom duration. Its authoritative
  record lives under
  `ResearchLog/highest-reasoning-runs/`. This route is not an independent
  second-model review. Public search is restricted to ordinary background and
  standard named theorems, never the exact target; any external-model route
  requires its own approval workflow.
- **`research-repo-manager/`**: initialize, refresh, audit, and compact the
  versioned research repository that holds the pipeline's persistent state:
  ledger scaffolding and templates, source-hash auditing, claim/evidence and
  reproducibility protocols, and approval-gated archiving. Used by `auto-opt`
  for Stage 0 and for session closeout; also useful standalone for any
  applied-math research repository.
- **`lean-verify/`**: formalize and verify optimization theorem, proof, and
  certificate targets in Lean/Lake. PEP upper-bound and symbolic
  dual-certificate proofs are the main paper-facing certificate path. ChatGPT
  Pro may be used for proof-planning blueprints, but Codex owns the Lean
  project and Lean/Lake is the mandatory verifier. When feasible, closeout also
  uses human-approved
  `Challenge.lean`/`Solution.lean`/`config.json` wrappers and comparator
  replay as additional evidence. Qualifying platform routes are real Landrun on
  Linux; the official upstream unsandboxed `fake-landrun.sh` on native macOS
  after explicit disclosure and approval; and real Landrun inside Windows 11
  WSL2 after the required systemd and Landlock preflight. Sandbox strength is
  recorded separately from replay success.

## Quick start

1. Copy or symlink the desired skill folder(s) into a location scanned by your
   agent:
   - **Codex:** use `$HOME/.agents/skills/` for skills available in every
     repository, or `<repository-root>/.agents/skills/` for repository-scoped
     skills. Keep each skill as a direct child of that directory, with its
     `SKILL.md` and bundled resources intact. Codex follows symlinked skill
     folders and detects changes automatically. In Codex CLI or the IDE
     extension, run `/skills` to confirm discovery; invoke a skill as
     `$skill-name`. Restart Codex if an installed skill does not appear.
   - **Claude Code:** use `~/.claude/skills/` for user-wide installation.
2. For PEP/algorithm-design work alone, `bnb-pep-skill` is self-contained:
   ask your agent to use it and follow the onboarding reference for the Julia
   environment and smoke tests.
3. For the full orchestrated workflow, install all companion skills delegated
   to by `auto-opt`: `research-repo-manager`, `bnb-pep-skill`,
   `frontier-llm-consult`, at least one Stage 2 route, and `lean-verify`.
   The external route requires `chatgpt-pro-session` together with
   `chatgpt-pro-handoff` plus Chrome/ChatGPT Web access. The native route
   requires `solve-with-highest-reasoning` and a Codex host that can meet its
   explicit-invocation, persistence, capability, duration, subagent, and local
   tool requirements without silently downgrading. Install
   `chatgpt-pro-session` for the default ordinary AutoOPT Stage 2 route.
   Lean/Lake is required for Stage 3 verification.
4. Ask your agent to run an AutoOPT pipeline session with `auto-opt`. It will
   stop for your approval at every stage boundary.

## Evidence discipline

These skills enforce a uniform standard:

- A human approves every stage boundary; the orchestrator automates the glue
  between stages, never the approvals.
- Every model-produced Stage 2 output is a **candidate** (candidate formula,
  candidate identity, candidate proof skeleton), never a proof. Candidates
  must later pass formal verification or ordinary mathematical proof.
- Solver output is never an exact certificate unless solver status,
  tolerances, gaps, and logs support that interpretation.
- No Lean verification is claimed until Lean source files, successful
  `lake build`, and no-`sorry`/no-`axiom`/no-`admit`/no-`unsafe` checks are
  recorded.
- Comparator evidence is claimed only after the human researcher approves the
  `Challenge.lean`/`Solution.lean`/`config.json` theorem surface and comparator
  replay succeeds.
- For ChatGPT Pro sessions, the session metadata, manifest, prompts, imported
  response, and turn artifacts are the consultation evidence, including for a
  bounded single-turn session.
- For a native highest-reasoning route, the authoritative campaign remains
  under `ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/`. AutoOPT
  stores compact `route-approval.md`, `native-campaign-reference.md`, and
  `candidate.md` artifacts under its Stage 2 folder, using repository-relative
  references and SHA-256 hashes instead of copying or symlinking the campaign.
- Native campaign duration, subagent agreement, or successful record
  validation does not prove a mathematical claim. A native result remains
  `Conjectured` or `Needs check` unless ordinary proof or formal verification
  independently supports promotion.

## Status

- `bnb-pep-skill` defaults to the BnB-PEP Algorithm's Stage 1/2 local
  workflows, with no global solver requirement. Its BnB-PEP Stage 3 spatial
  branch-and-bound guidance is explicitly opt-in and solver-evidence only.
- `lean-verify` is the Stage 3 skill for optimization theorem/proof/certificate
  Lean verification. PEP upper-bound and symbolic dual-certificate checks remain
  its primary paper-case specialization. ChatGPT Pro blueprints are planning
  inputs only; the host agent builds and repairs the Lean/Lake project locally,
  and Lean/Lake is the mandatory verifier. Comparator replay is the default
  closeout layer when compatible wrappers are available and approved.
  The skill has been dogfooded on OGM, and paper-case Lean projects for ITEM-f
  and lemniscate are present under `Lean-Related/` in the research repository.
- AutoOPT Stage 2 invokes `frontier-llm-consult`, which selects between one
  external consultation route and one native Codex route. It recommends
  `chatgpt-pro-session` for ordinary or ambiguous work, including bounded
  single-turn reviews, and `solve-with-highest-reasoning` only after explicit
  invocation for a target that warrants its complete user-confirmed duration
  contract. AutoOPT and its router preserve the selected floor and never
  weaken it. ChatGPT Pro can supply an external second-model review. Provider
  diversity or another provider is unsupported, and the native route never
  substitutes for that requirement.
- The native route reads approved repository context directly and may discover
  additional in-scope files without another gate. A different target,
  repository root, source boundary, or any external transfer requires renewed
  approval. Campaign states `prepared`, `running`, and `paused` leave Stage 2
  incomplete and resumable; `complete` permits candidates to reach the
  researcher gate; `incomplete` preserves an exact-gap report and only partial
  candidates; `user_stopped` and `environment_blocked` record an interrupted
  or blocked Stage 2.
- `chatgpt-pro-handoff` is bundled here for the ChatGPT Pro package/import
  mechanics used by `chatgpt-pro-session`. Before public release, replace any
  installed-skill absolute path examples in the ChatGPT Pro skills with
  skill-local script paths.
- No end-to-end demonstration run is bundled here yet; an external
  human-gated run has been reported and intentionally left outside this folder
  for now.

## Licensing

The eight author-written skills (`auto-opt`, `bnb-pep-skill`,
`chatgpt-pro-handoff`, `chatgpt-pro-session`, `frontier-llm-consult`,
`research-repo-manager`, `lean-verify`, and
`solve-with-highest-reasoning`) are licensed under the Apache License 2.0.
