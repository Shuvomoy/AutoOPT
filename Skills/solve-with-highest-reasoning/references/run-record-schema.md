# Run-Record Schema

## Contents

- [Required artifacts](#required-artifacts)
- [`campaign.yaml`](#campaignyaml)
- [Machine-readable evidence logs](#machine-readable-evidence-logs)
- [Claim and approach records](#claim-and-approach-records)
- [Conditional repository handoff](#conditional-repository-handoff)

Store each campaign under:

```text
ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/
```

Preserve stable identifiers and repository-relative links throughout the run.
Use timestamps with time zone information.

## Required artifacts

| Artifact | Meaning |
|---|---|
| `campaign.yaml` | Machine-readable capability, timing, policy, checkpoint, and final-status record. |
| `problem-contract.md` | Authoritative target, assumptions, quantifiers, certificates, and completion obligations. |
| `source-manifest.md` | Local and permitted public sources, provenance, versions, and claim roles. |
| `approach-registry.md` | Distinct approach families, artifacts, traction, blockers, and reopening conditions. |
| `claim-ledger.md` | Stable claim IDs, dependencies, evidence status, and verification gates. |
| `audit-log.md` | Fresh-auditor assignments, findings, repairs, and reaudit outcomes. |
| `reproducibility.md` | Commands, environments, inputs, settings, outputs, and exactness limits. |
| `final-report.md` | Complete certificate or strongest verified progress with the exact remaining gap. |
| `work-intervals.jsonl` | Checkpointed active and excluded time intervals from which active-work time is recomputed. |
| `agent-runs.jsonl` | Per-agent and per-wave actual model, reasoning, provenance, freshness, timing, and concurrency evidence. |
| `rounds.jsonl` | Ordered research, rediversification, audit, and repair rounds used to verify productive continuation and terminal-obstruction suffixes. |
| `audits.jsonl` | Machine-checkable fresh-audit identities, candidate/contract hashes, repair ordering, and outcomes. |
| `checkpoints/` | Dated resumable state summaries; never use them as substitutes for ledgers. |
| `artifacts/` | Run-scoped proofs, code, solver logs, counterexamples, and generated evidence. |

## `campaign.yaml`

Write new campaigns with `schema_version: 2` and record these fields:

```yaml
schema_version:
run_id:
repository_root:
run_directory:
target_id:
started_at:
earliest_finalization_at:
last_checkpoint_at:
capability:
  requested_policy:
  available_models:
  resolved_strongest_model:
  selected_model:
  available_reasoning_for_selected_model:
  resolved_highest_reasoning:
  selected_reasoning:
  capability_source:
  model_selection_basis:
  reasoning_selection_basis:
  evidence_artifact:
  evidence_sha256:
  verified:
  available_concurrency:
  peak_concurrency:
  downgrade:
policies:
  public_search:
  local_sources:
  external_consultation:
  max_execution_minutes:
timing:
  duration_source:
  minimum_hours:
  minimum_active_seconds:
  active_work_seconds:
  paused_seconds:
  last_resumed_at:
  productive_rounds_after_minimum:
  terminal_obstruction_rounds:
status:
  value:
  terminal_at:
  stopping_reason:
  exact_remaining_gap:
  terminal_obstruction_id:
  no_defensible_next_step:
  interruption_kind:
  interruption_evidence_artifact:
completion:
  candidate_version:
  candidate_artifact:
  candidate_sha256:
  contract_version:
  contract_sha256:
  last_material_repair_at:
audits:
  required_fresh:
  completed_fresh:
managed_repository:
  detected:
  detection_basis:
  handoff_completed:
```

For schema version 2, set `timing.duration_source` to `default` only after the
user explicitly accepts the offered eight-hour default; set it to
`user_override` whenever `--minimum-hours` is supplied. Store
`timing.minimum_hours` as a canonical base-10 decimal string and
`timing.minimum_active_seconds` as the exact positive integer obtained by
multiplying those hours by 3,600. The canonical decimal has no sign,
exponent, redundant leading zeros, or redundant fractional trailing zeros.
Require `"8"` and 28,800 seconds when the source is `default`. A
`user_override` may explicitly select the same duration. Reject a value rather
than rounding it when the product is not a whole number of seconds or its
finalization timestamp cannot be represented. Once `started_at` is recorded,
treat all three duration fields and `earliest_finalization_at` as immutable.
The initializer copies the run ID, start time, duration tuple, and earliest
finalization timestamp into `checkpoints/0000-prepared.md`. Preserve that
checkpoint unchanged; the validator cross-checks it against `campaign.yaml`
so a later duration edit is rejected.

Continue to validate legacy `schema_version: 1` campaign records under their
original fixed semantics: `timing.minimum_hours` is 8,
`earliest_finalization_at` is exactly eight hours after `started_at`, and a
voluntary terminal close requires at least 28,800 active-work seconds. Version
1 has no `duration_source` or `minimum_active_seconds`; do not rewrite
historical records merely to add them. All newly initialized records use
version 2.

Set `requested_policy` to “strongest available Codex GPT and that model's
highest supported reasoning setting.” Resolve the setting from current
capability metadata. Never assume that a literal setting named `max` is
highest; the top setting may be `ultra` or another runtime-defined label.
Record the host-resolved strongest model and highest reasoning value separately
from the selected values, and require equality. Preserve the capability
snapshot, user selection, or host-control evidence in `evidence_artifact`;
pin it with `evidence_sha256`, and explain both selection bases rather than
inferring order from literal labels.

Use a JSON capability-evidence artifact with this shape:

```json
{
  "schema_version": 1,
  "verification_mode": "runtime_verified or user_selected",
  "available_models": ["runtime-observed labels"],
  "resolved_strongest_model": "host-resolved label",
  "selected_model": "same label",
  "available_reasoning_for_selected_model": ["runtime-observed labels"],
  "resolved_highest_reasoning": "host-resolved label",
  "selected_reasoning": "same label",
  "capability_source": "control, metadata, or explicit selection source",
  "model_selection_basis": "why this is host-designated strongest",
  "reasoning_selection_basis": "why this is the model's highest setting",
  "captured_at": "time-zone-aware timestamp",
  "selection_evidence": "substantive host/runtime or user evidence naming both selected labels"
}
```

The artifact fields must match `campaign.yaml`, explicitly name the selected
model and reasoning labels, identify runtime/host or user provenance as
appropriate, and be captured no later than campaign start. This is a
reproducible evidence record, not a cryptographic attestation by the host.
Set `verified` to `runtime_verified` or `user_selected`; no other or empty value
may start a strict campaign. Record `downgrade: none`; stop for direction
instead of silently lowering capability. Record observed peak concurrency and
require it not to exceed the available capacity.

Keep the three source/consultation policy strings equal to the initialized
canonical values. Set `max_execution_minutes: 180`; every code and solver
execution must use that maximum and must not be manually terminated earlier
unless it exits, the user asks, or the platform ends it.

For every permitted public retrieval in `source-manifest.md`, use a
run-namespaced retrieval ID and exactly one boundary class:
`ordinary_background` or `standard_named_theorem`. Record the exact,
unsanitized query or URL, purpose, background/theorem claim, and the source
actually checked. Set the structured `Checked` cell to `true` and give a
nonempty source citation. The validator rejects any other checked value,
empty rows, and explicit
exact-target, solution, or open-status language. Because target-specificity
cannot be inferred perfectly from arbitrary URLs, the root solver and final
auditors must still inspect every row semantically; structural validation is
not permission to retrieve.

For version 2, set `earliest_finalization_at` exactly
`timing.minimum_active_seconds` seconds after `started_at`. Maintain
checkpointed active-work intervals, cumulative `active_work_seconds`, paused
time, and the last resume time. Exclude user waits, permission waits, and idle
waiting. A voluntary terminal close requires both the recorded wall-clock
floor and at least `timing.minimum_active_seconds` active-work seconds. Record
`status.terminal_at` when terminal and validate the floor against that
immutable timestamp, not against a later validation time. Every recorded
interval, agent run, round, and audit must lie between campaign start and
terminal time (or the present for a checkpoint).
Permit an earlier terminal close only for an explicit user stop or an
unavoidable permission, credential, capability, environment, or required-tool
blocker. Record its structured `interruption_kind` and a repository-local
evidence artifact. Define the post-minimum boundary as the later of
`earliest_finalization_at` and the timestamp at which cumulative countable
active work first reaches `timing.minimum_active_seconds`. After that boundary,
record each materially productive continuation round. For an incomplete
terminal close, require all active routes to be explicitly refuted or blocked,
a run-namespaced obstruction ID, the same terminal obstruction to survive
three consecutive post-minimum rediversification or audit rounds, and
`no_defensible_next_step: true`.

Use nonterminal `status.value` values `prepared`, `running`, or `paused`. Use
terminal values `complete`, `incomplete`, `user_stopped`, or
`environment_blocked`. Reserve `incomplete` for a voluntary post-floor
closeout. Never use `open` as a status or stopping reason.

## Machine-readable evidence logs

Write one JSON object per line. Namespace IDs with `run_id` before promotion to
repository ledgers.

For `work-intervals.jsonl`, record interval ID, start, end, duration, kind, and
checkpoint path. Count only kinds `research`, `verification`, and
`computation`. Exclude `idle`, `user_wait`, and `permission_wait`. Reject
overlapping, negative, or timestamp-inconsistent intervals, and require their
countable duration sum to equal `timing.active_work_seconds`. Use
`<run_id>:...` IDs, keep checkpoint paths inside `checkpoints/`, and do not
count overlapping parallel workers as additive campaign hours.

For `agent-runs.jsonl`, record agent ID, context ID, wave ID, role, actual
model, actual reasoning setting, capability provenance, verification mode,
fresh-context flag, start, and end. Namespace agent, context, and wave IDs with
`run_id`. Record the root orchestrator as well as campaign subagents at
voluntary closeout. Require every actual configuration and verification mode
to match the campaign selection, and recompute peak concurrency from the
intervals.

For `rounds.jsonl`, record a namespaced round ID, consecutive integer sequence,
kind (`research`, `rediversification`, `audit`, or `repair`), start, end,
`materially_productive`, `terminal_obstruction_survived`, namespaced
obstruction ID when applicable, `defensible_next_step`, a concrete material
result, and a confined evidence-artifact path. Rounds are chronological and
nonoverlapping. Count a record as post-minimum only when it starts at or after
the later of the wall-clock and cumulative-active-work boundaries. Recompute
`productive_rounds_after_minimum` from those post-minimum productive records.
Recompute `terminal_obstruction_rounds` from the final consecutive suffix of
post-minimum, nonproductive rediversification/audit records that preserve the
same obstruction and expose no defensible next step.

For `audits.jsonl`, record audit ID, auditor ID, context ID, authoring
involvement, candidate artifact/version/SHA-256, contract version/SHA-256,
audit-artifact path, audit scope, outcome, completion timestamp, and
last-material-repair timestamp. Use exactly the scopes
`dependency_quantifier_edge_case` and
`adversarial_counterexample_circularity` for the two required attacks. A
complete status requires at least two distinct auditors in distinct fresh
contexts, both scopes, `authoring_involvement: false`, `outcome: pass`,
matching final candidate and contract hashes, and auditor contexts started
after the final candidate freeze or last material repair. If there was no
repair, use the final candidate-freeze time for
`last_material_repair_at`. Audit counts alone are insufficient.

## Claim and approach records

Give important claims, assumptions, theorems, counterexamples, experiments,
sources, and artifacts stable IDs. Label each claim with exactly one
`research-repo-manager` status:

- `Proven`
- `Derivation checked`
- `Computed`
- `Literature`
- `Conjectured`
- `Refuted`
- `Needs check`

Record dependencies, evidence links, assumptions, boundary coverage, audit
results, and the smallest exact blocker. For each approach family, record its
distinguishing mechanism, concrete outputs, current state, failed claims, and
the evidence required to reopen it.

## Conditional repository handoff

Detect a managed repository only when all of `GOALS.md`, `SOURCES.md`,
`FINDINGS.md`, and `NEXTSTEP.md` exist, or an applicable `AGENTS.md` explicitly
declares the policy. When relying on the latter, initialize with
`--managed-agents <applicable-AGENTS.md>` so the policy file is checked and its
absolute path is recorded as the detection basis. If detected, follow
`research-repo-manager` Research Session Mode: preserve `RawSources/`, keep
detailed process evidence in this run directory, promote namespaced reliable
claims and negative results to `FINDINGS.md`, update `EXPERIMENTS.md`,
`ARTIFACTS.md`, or `REPRODUCIBILITY.md` when their evidence changed, and leave
exactly one full-workday session in `NEXTSTEP.md`. Treat those minimal closeout
updates as part of explicit invocation. Do not change `SOURCES.md` without a
separate source-catalog refresh request.

If the repository is not managed, create only the scoped `ResearchLog/` run.
Do not initialize or restructure the broader repository without explicit user
approval.
