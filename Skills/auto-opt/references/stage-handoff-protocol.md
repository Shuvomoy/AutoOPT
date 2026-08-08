# Stage Handoff Protocol

This protocol defines the run-folder convention, the per-stage input/output
contracts, the gate-brief template, and the route-specific evidence-archiving
rules for AutoOPT pipeline runs. The gate rule itself lives in `SKILL.md` and is binding
without this file; this file standardizes the artifacts and the brief format.

## Run Folder Convention

- One folder per gated run, in the target repository:
  `ResearchLog/auto-opt-runs/<YYYY-MM-DD>-<slug>/`.
- `<slug>` is 2-5 lowercase hyphenated words naming the instance, for example
  `smooth-scvx-gradient`. The orchestrator proposes the slug in the
  first gate brief of the run; the user may adjust it there.
- Stage subfolders `stage0/` through `stage3/` are created lazily: the
  orchestrator creates the run folder and a stage subfolder at the moment the
  first artifact of that stage is written. Repository-grounding stages that
  change only the planning ledgers may leave `stage0/` empty or absent; the
  gate brief then lists the ledger files touched instead.
- The run folder is not created by repository scaffolding; the orchestrator
  creates it at run time.

## Per-Stage Contracts

### Stage 0 - repository grounding

- Inputs: the target repository root; the user's research goal or refresh
  request.
- Delegate: `research-repo-manager` (Initialization Mode, Status Refresh Mode,
  or Research Session Mode, chosen from the repository state).
- Outputs: current planning ledgers (goals, sources, claim/evidence,
  experiments, artifacts, reproducibility, next step); a stated active
  objective for the run.
- Gate brief asks: approve proceeding to numerical algorithm design with the
  stated instance.

### Stage 1 - numerical algorithm design

- Inputs: the formalized problem instance request (function class, method
  family, performance measure, initial condition, iteration budget).
- Delegate: `bnb-pep-skill`, run inside the repository. Its internal
  derivation-before-Julia approval gate and BnB-PEP Stage 1/2-only boundary
  stay intact; this protocol adds no shortcut around them.
- Outputs, stored under `stage1/`: the derivation Markdown; generated Julia
  files; smoke-test or environment-check output when produced. Record exact
  commands and solver status lines in the repository's experiment ledger when
  anything was executed.
- Gate brief asks: approve carrying the named numerical artifacts into the
  selected Stage 2 route. An external route will build a minimal consultation
  package; the native route will use them as repository-local seed artifacts.

### Stage 2 - symbolic fitting

- Inputs: Stage 1 artifacts (candidate method, parameter values, dual
  information, structural constraints); the exact symbolic-fitting target and
  admissible output; the target repository root and source boundary.
- Delegate: `frontier-llm-consult`, which selects between one external
  consultation route and one native Codex route after human approval:
  - `chatgpt-pro-session` for ChatGPT Pro consultation, including one approved
    turn in a new session for bounded one-shot work;
  - explicitly invoked `solve-with-highest-reasoning` for one exceptionally
    difficult, sharply defined target that benefits materially from repository
    discovery or local tools.
- For ordinary AutoOPT Stage 2 runs with no strong user preference, recommend
  `chatgpt-pro-session` by default. Do not recommend the native route when an
  independent second-model opinion or provider diversity is required.
- Requests for another provider, API or multi-provider routing, or provider
  diversity are unsupported. Stop rather than substituting a route. ChatGPT Pro
  can provide an external second-model review; the native route cannot satisfy
  provider diversity or independence from the current Codex host.
- For the external route, build one task prompt plus the smallest file set that
  carries the data and run the consultation only after the
  approve-before-send gate clears. This outer gate remains controlling even if
  direct invocation of the delegated session skill would otherwise provide
  standing upload consent.
- For the native route, create no outgoing context or upload package. Pass the
  exact target, repository root, Stage 1 seed artifacts, and approved discovery
  and source boundaries to `solve-with-highest-reasoning`. It may discover and
  use additional repository files inside that scope without another gate. A
  different target or root, a widened source boundary, or any external transfer
  requires renewed approval. Require explicit `$solve-with-highest-reasoning`
  invocation and preserve its active Goal mode, equivalent persistent
  mechanism, or disclosed checkpointed fallback when neither is available;
  strongest-model and highest-reasoning resolution with no downgrade;
  eight-hour wall-clock and 28,800-active-work-second floors; 180-minute
  code-or-solver-execution ceiling; local-tool rules; audit requirements; and
  stopping rules.
  Never silently fall back to another route. If ChatGPT Pro is selected but
  unavailable, block without automatically switching to native. If native is
  selected but its invocation, persistence, capability resolution, or required
  tools are unavailable, block without falling back to ChatGPT Pro.
- External-route outputs, stored under `stage2/`: the consultation skill; the
  approved route and rationale; outgoing prompt; outgoing file list or context
  manifest; ChatGPT Pro selection and manifest summary; archived consultation
  evidence; and the candidate output with its assumptions and derivation trail.
- Native-route outputs use two linked evidence locations. The authoritative
  campaign remains under
  `ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/`. Store these compact
  artifacts under the AutoOPT `stage2/` folder:
  - `route-approval.md`, recording the approved route and native gate;
  - `native-campaign-reference.md`, recording repository-relative campaign
    paths, campaign status, model/reasoning capability evidence, SHA-256
    hashes, validation status, and audit summary;
  - `candidate.md`, recording exact candidates, assumptions, provenance,
    evidence status, and any proposed Stage 3 target.
  Do not copy or symlink the complete native campaign into `stage2/`.
- Map native status as follows:
  - `prepared`, `running`, or `paused`: Stage 2 is incomplete and resumable;
  - `complete`: candidates may advance to researcher inspection at the Stage 2
    gate;
  - `incomplete`: archive the exact-gap report and keep partial candidates
    gated;
  - `user_stopped` or `environment_blocked`: record Stage 2 as interrupted or
    blocked.
- Gate brief asks: for a completed route, approve recording the candidates as
  `Conjectured` or `Needs check` and either carrying a named target to Stage 3,
  closing the run at the Stage 3 stub, or ending the session. For a nonterminal,
  incomplete, interrupted, or blocked native campaign, ask only for the
  appropriate resume or closeout decision; do not report Stage 2 complete.

### Stage 3 - Lean verification

- Inputs: one inspected Stage 2 candidate optimization theorem, proof, or
  symbolic certificate; its paper proof or proof blueprint; the relevant Stage 1
  numerical/symbolic artifacts when applicable; and the exact claim status to
  upgrade.
- Delegate: `lean-verify` when available. Its scope is optimization theorem,
  proof, and certificate formalization, with PEP upper-bound and symbolic
  dual-certificate checks as the main paper case. Codex owns the Lean files and
  Lean/Lake is the only verifier.
- Outputs, stored under `stage3/`: formalization manifest or theorem target,
  Lean project files or patch notes, build logs, hygiene-check output,
  permitted-axiom audit when relevant, comparator wrapper/config files
  (`Challenge.lean`, `Solution.lean`, `config.json`) when feasible, comparator
  command/output when run, elapsed formalization time when available, and a
  closeout note stating exactly which theorem was verified.
- Gate brief asks: approve recording one of `Lean build+hygiene verified`,
  `Lean+comparator verified`, or `blocked/stubbed`. If comparator replay is
  feasible, the brief must ask for explicit approval of the
  `Challenge.lean`/`Solution.lean`/`config.json` surface before replay.
- No Lean claim is valid until Lean source files, successful `lake build`, and
  no-`sorry`/no-`axiom`/no-`admit`/no-`unsafe` checks are recorded.
  Comparator evidence is valid only when the approved wrapper/config replay
  actually succeeds.

## Gate-Brief Template

Use this shape at every stage boundary:

```text
Gate: Stage <k> (<name>) -> Stage <k+1> (<name>)
Run: ResearchLog/auto-opt-runs/<date>-<slug>/
Completed: <what Stage k did, one or two sentences>
Artifacts: <paths created or updated>
Evidence status: <each claim touched, with its status label>
Proposed next stage: <what it will do and which inputs it consumes>
Residual risk: <what remains uncertain>
Exact ask: <the specific approval requested>
```

Additional common fields for every Stage 2 route gate:

```text
Routing skill: frontier-llm-consult
Recommended or selected route: <chatgpt-pro-session | solve-with-highest-reasoning>
Recommendation rationale: <default-pro-session | persistent-context | external-review | native-local-tools | user-override>
Route class: <external consultation | native same-host Codex campaign, not an independent second-model review>
Archive destination: <AutoOPT stage2 path and, for native, canonical campaign path>
Exact ask: approve this route and its branch-specific context boundary
```

For `chatgpt-pro-session`, also show these fields before anything leaves the
machine:

```text
Provider/model or session mode: <actual ChatGPT Pro session configuration>
Outgoing files or context manifest: <exact file list or manifest summary>
Preview evidence: <ChatGPT Pro selection and manifest review>
Secrets check: <confirmation that no secrets or private material is attached>
```

For `solve-with-highest-reasoning`, show these fields before campaign
initialization. There is no outgoing upload package:

```text
Exact target and admissible output: <frozen Stage 2 target and accepted resolution forms>
Explicit invocation: <$solve-with-highest-reasoning invocation evidence>
Persistence mode: <active Goal mode | equivalent persistent mechanism | disclosed checkpointed manual fallback when no native or equivalent mechanism exists>
Capability selection: <strongest Codex model, highest supported reasoning setting, and resolution evidence>
Duration contract: <eight wall-clock hours and 28,800 active-work seconds>
Code/solver execution ceiling: <180 minutes per execution>
Repository and seed artifacts: <repository root and exact Stage 1 seed paths>
Discovery and source boundary: <approved repository scope and restricted public-search policy>
Immutable/excluded paths and local-write scope: <exact paths or policies>
Authorized local tools: <relevant installed tools permitted for this target>
External transfer: <none; separate approval required for any external-model workflow>
Canonical campaign archive: <ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/>
AutoOPT reference archive: <ResearchLog/auto-opt-runs/<date>-<slug>/stage2/>
No-downgrade check: <confirmed or blocker>
```

Additional required fields for Stage 3 closeout and comparator gates:

```text
Theorem targets: <exact Lean declaration names and paper claims>
Lean commands: <lake build / hygiene / axiom-audit commands and status>
Wrapper/config paths: <Challenge.lean, Solution.lean, config.json, or blocker>
Permitted axioms: <exact list or policy>
Host and execution platform: <operating systems, versions, architecture, or blocker>
Sandbox backend, strength, and engagement: <real Landrun plus denial probe/output | official fake-Landrun unsandboxed | blocker>
Tool provenance: <Lean, Lake, mathlib, Comparator, exporter, checker, real Landrun or official fake-Landrun shim, Lake wrapper if used, Challenge/Solution/config revisions and hashes>
Required disclosure: <unsandboxed native macOS disclosure, or not applicable>
Comparator command/status: <command and output path, or not run with reason>
Exact surface and command approval: <approved / not approved / not applicable, with date/context>
Evidence label requested: <Lean build+hygiene verified | Lean+comparator verified | blocked/stubbed>
```

## Stage 2 Evidence Archiving

- `frontier-llm-consult` records the selected route and recommendation
  rationale in the Stage 2 evidence folder before or during closeout.
- Archive durable evidence for every route that ran, including failed, partial,
  interrupted, or blocked work. Missing required durable evidence leaves Stage
  2 incomplete.

### ChatGPT Pro session

- `chatgpt-pro-session` consultations store session metadata and turn artifacts
  under `.chatgpt_handoffs/<timestamp>/`, including `session.json`,
  `manifest.json`, `prompt.md`, the uploaded context archive, and imported
  turn responses under `turns/<id>/`. Copy or link the relevant session
  metadata, manifest, prompt, imported response, and any extracted artifacts
  into `stage2/`, or record their stable repository-relative paths if the
  target repository already keeps `.chatgpt_handoffs/` as an active evidence
  folder. For bounded one-shot work, archive the single approved turn and its
  new-session metadata.

### Native highest-reasoning campaign

- Keep the complete campaign record only in its canonical
  `ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/` directory.
- Write `route-approval.md`, `native-campaign-reference.md`, and `candidate.md`
  under the AutoOPT `stage2/` directory. Use repository-relative paths and
  SHA-256 hashes to bind the reference and candidate artifacts to the
  authoritative campaign. Do not use absolute machine paths, copy the campaign
  tree, or symlink it into the AutoOPT run.
- In `native-campaign-reference.md`, record the native status, capability
  evidence artifact and hash, final or exact-gap report and hash when present,
  campaign validation command/status, and the two required independent-audit
  outcomes when a complete candidate is claimed. Campaign-record validation
  checks protocol structure only and is not mathematical verification.
- In `candidate.md`, prefix each model-produced object with `candidate` and give
  it exactly one claim status. Eight hours elapsed, subagent agreement, model
  self-review, and a passing campaign-record validator do not upgrade the
  mathematical status.
- Do not allow the native campaign to invoke Frontier, ChatGPT, or another
  external-model route recursively. Any such transfer is a distinct
  consultation requiring a separate recommendation and approve-before-send
  gate.
