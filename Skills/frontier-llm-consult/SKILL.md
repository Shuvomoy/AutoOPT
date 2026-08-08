---
name: frontier-llm-consult
description: Human-gated frontier-model research router for AutoOPT Stage 2 symbolic fitting, candidate formula/proof discovery, proof planning, and independent model review. Use when Codex must choose between an external chatgpt-pro-session consultation and an explicitly invoked native solve-with-highest-reasoning campaign, preview external outgoing context or approve native repository scope, delegate to the selected route skill, archive durable evidence, and treat model outputs as candidate mathematical objects rather than proofs.
---

# Frontier LLM Consult

## Core Rule

Route difficult research work through one of two execution routes without
weakening its approval gate:

- `chatgpt-pro-session`, the sole external consultation route and the default;
- `solve-with-highest-reasoning`, a native same-host Codex campaign.

The native route is not an external consultation, an independent second-model
opinion, or a source of provider diversity. This skill chooses and coordinates
the route; it does not replace or duplicate any route skill. Load and follow
the selected route skill before execution.

For an external route, never send, upload, or submit consultation context
before the user approves the route and outgoing context. For the native route,
never initialize or run a campaign unless the user explicitly invokes
`$solve-with-highest-reasoning` and approves the native route gate below. Treat
every model-produced formula, identity, closed form, proof skeleton, blueprint,
proof, construction, counterexample, or algorithm as a candidate until its
required independent verification succeeds.

## Inputs

For AutoOPT Stage 2, start from the Stage 1 artifacts:

- BnB-PEP derivation Markdown;
- numerical method parameters, stepsizes, or recurrence data;
- dual variables, certificate structure, or solver summaries when available;
- structural constraints and desired analytical form;
- the requested output type: formula, identity, proof skeleton, or
  proof-planning blueprint.

For standalone routed work, collect the same information at the appropriate
level of detail: task, context files, constraints, desired output, evidence
standard, and what should be archived.

## Route Selection

Recommend `chatgpt-pro-session` for external consultation:

- the user explicitly asks for ChatGPT Pro, a persistent session, or reuse of
  an existing ChatGPT conversation;
- the consultation is likely to require multiple turns, corrections, or
  follow-up symbolic fitting;
- the context is broad, reusable, or expensive to re-upload;
- the task is ordinary or underspecified AutoOPT Stage 2 symbolic fitting;
- the user wants a bounded one-shot external review. In that case, start a new
  ChatGPT Pro session, submit one approved turn, archive it, and do not create
  a separate one-shot backend.

Select `solve-with-highest-reasoning` only when all of these conditions hold:

- the user explicitly invokes `$solve-with-highest-reasoning` in the current
  workflow;
- the target is one exceptionally difficult, sharply defined research problem;
- direct repository exploration or installed local tools materially benefit
  the work;
- the user accepts active Goal mode, an equivalent persistent mechanism, or the
  skill's disclosed checkpointed fallback when neither is available, plus a
  minimum of eight wall-clock hours and 28,800 logged active-work seconds
  before voluntary finalization and a 180-minute ceiling for each code or
  solver execution.

Explicit invocation makes the native route eligible; it does not waive the
native route approval gate. Exclude the native route when the requested purpose
requires provider diversity, an independent second-model review, or a bounded
consultation. Do not infer explicit invocation from a router recommendation or
from approval of another route. In a routed workflow, this gate is an
additional AutoOPT authorization boundary; it does not change the native
skill's standalone explicit-invocation contract.

Default to recommending `chatgpt-pro-session` for AutoOPT Stage 2 when the
user's preference is ambiguous and the native route has not been explicitly
invoked. This is only a recommendation before the approval gate; it is not
permission to upload.

Requests for another provider, API or multi-provider routing, or provider
diversity are unsupported by this router. Stop and report the unmet
requirement rather than substituting either route. ChatGPT Pro can provide an
external second-model review; the native route cannot satisfy provider
diversity or independence from the current Codex host.

Assess availability and eligibility route by route. A resolvable native skill
is not eligible without explicit invocation and acceptance of its full
campaign contract. If the selected native route lacks Goal mode, an equivalent
persistent mechanism, or the permitted checkpointed fallback, reliable
capability resolution, or a required local tool, stop and report the exact
blocker. Never silently downgrade its model, reasoning effort, or route. If
ChatGPT Pro is selected but unavailable, stop without automatically switching
to the native route. A user may choose the native route only through a separate
explicit invocation and full native gate. If the selected route is unusable,
report Stage 2 as blocked rather than improvising a replacement.

## Context Preparation

For `chatgpt-pro-session`, build the smallest outgoing package that carries the
truth:

- a self-contained task prompt;
- a short project or mathematical briefing;
- exact files or artifacts to include;
- desired output markers or artifact format when a structured response is
  needed;
- explicit constraints, including "candidate, not proof";
- archive destination, usually
  `ResearchLog/auto-opt-runs/<date>-<slug>/stage2/` for AutoOPT.

Do not attach secrets, credentials, browser state, API keys, private tokens, or
irrelevant generated output. Prefer fewer files plus a precise prompt over a
large dump.

For `solve-with-highest-reasoning`, create no upload package. Pass the exact
Stage 2 target, repository root, Stage 1 seed artifacts, admissible output, and
approved discovery boundaries to the native skill. Let that skill inspect the
repository and build its local problem contract and source manifest. It may
identify and read additional files within the approved repository and source
scope without another route gate. Require renewed approval before changing the
target, using another repository root, widening the source boundary, or making
any external transfer.

## External Route Approval Gate

Before a ChatGPT Pro send/upload action, present:

```text
Consultation skill: frontier-llm-consult
Recommended route: chatgpt-pro-session
Route class: external consultation backend
Recommendation rationale: <default-pro-session | persistent-context | external-review | user-override>
Provider/model or session mode: <ChatGPT Pro session configuration>
Outgoing files or context manifest: <exact file list or manifest summary>
Preview evidence: <ChatGPT Pro selection and manifest review>
Secrets check: <confirmed no secrets / issue found>
Archive destination: <stage2 path or evidence folder>
Exact ask: approve this consultation route and outgoing context
```

Proceed only after explicit approval. If the actual backend manifest later
differs materially from the approved file list or context summary, pause and
ask for approval again. This outer gate remains controlling when
`chatgpt-pro-session` is delegated through Frontier or AutoOPT, even if a
direct, explicitly invoked session workflow would otherwise treat invocation
as standing upload consent.

## Native Route Approval Gate

Before initializing or running a native campaign, present:

```text
Routing skill: frontier-llm-consult
Selected route: solve-with-highest-reasoning
Route class: native same-host Codex campaign, not an independent second-model review
Recommendation rationale: <exceptional difficulty, repository access, and/or local tools>
Exact target and admissible output: <problem statement and accepted certificate types>
Explicit invocation: <confirmed current user invocation of $solve-with-highest-reasoning>
Persistence: <active Goal mode | equivalent persistent mechanism | disclosed checkpointed fallback when neither native nor equivalent persistence is available>
Capability: <strongest available Codex GPT and its highest supported reasoning setting>
Downgrade policy: no silent downgrade
Duration contract: at least 8 wall-clock hours and 28,800 logged active-work seconds
Execution ceiling: 180 minutes per code or solver execution
Repository root and Stage 1 seeds: <root plus exact initial artifact paths>
Discovery boundary: <approved repository and source scope>
Immutable or excluded paths: <paths and restrictions>
Local write scope: <approved destinations>
Local tools: <available, relevant, and authorized tools>
External-model transfer: none authorized
Public-search boundary: ordinary background and standard named theorems only, per the native skill
Authoritative campaign archive: ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/
AutoOPT Stage 2 archive: ResearchLog/auto-opt-runs/<date>-<slug>/stage2/
Exact ask: approve this native route, target, scope, tools, persistence, and duration contract
```

Resolve and name the strongest model and highest supported reasoning setting
when the host exposes them. If they cannot be determined, stop before campaign
initialization and obtain the user selection or required capability instead of
assuming or downgrading. Approval of the native gate authorizes only the
approved local campaign scope. It does not authorize external model transfer,
destructive actions, purchases, or material scope expansion.

## Delegation

For the `chatgpt-pro-session` route:

1. Load the `chatgpt-pro-session` skill.
2. Use directed context when the Stage 1 artifacts are known; use broad context
   only when a narrow selection would omit necessary information.
3. For bounded one-shot work, start a new session, use one approved turn, and
   archive that turn as the external consultation evidence.
4. If continuing an existing session, check whether the uploaded context is
   still fresh enough for the requested follow-up.
5. Archive or reference the session metadata, manifest, prompt, imported
   response, and turn artifacts under the Stage 2 evidence folder.

For the `solve-with-highest-reasoning` route:

1. Confirm that the user explicitly invoked `$solve-with-highest-reasoning`;
   route recommendation or generic approval is insufficient.
2. Load the `solve-with-highest-reasoning` skill and follow its persistence,
   capability, repository-grounding, campaign-record, source-boundary,
   computation, audit, and stopping rules.
3. Hand it the approved target, repository root, Stage 1 seed artifacts,
   discovery boundaries, admissible output, tools, write scope, and archive
   destinations.
4. Permit local repository exploration and use of installed tools only within
   those approved boundaries.
5. Do not let the native campaign recursively invoke `frontier-llm-consult`,
   ChatGPT Web, or another external-model backend. Any such use requires a
   separately authorized workflow under its own approval and outgoing-context
   rules.

Each route skill is authoritative for its own mechanics. Do not copy its
command syntax, browser-control rules, session-state rules, campaign protocol,
or failure handling into this skill.

## Native Route Evidence and Status

Keep the authoritative native campaign under:

```text
ResearchLog/highest-reasoning-runs/<timestamp>-<slug>/
```

For AutoOPT, store these compact handoff artifacts under the run's `stage2/`
folder:

- `route-approval.md`, recording the approved target, route configuration,
  discovery and write boundaries, tools, duration contract, and both archive
  destinations;
- `native-campaign-reference.md`, recording repository-relative campaign and
  evidence paths, campaign status, model and reasoning evidence, SHA-256
  hashes, record-validation status, and audit summary;
- `candidate.md`, recording exact candidates, assumptions, provenance,
  evidence status, and any proposed Stage 3 theorem or certificate target.

Use repository-relative paths and SHA-256 hashes. Do not copy or symlink the
complete campaign into `stage2/`.

Map native campaign states into the AutoOPT Stage 2 gate as follows:

- `prepared`, `running`, or `paused`: Stage 2 remains incomplete and
  resumable;
- `complete`: archived candidates may proceed to the Stage 2 researcher gate;
- `incomplete`: archive the exact-gap report, and keep partial candidates
  gated;
- `user_stopped` or `environment_blocked`: record Stage 2 as interrupted or
  blocked, respectively.

## Return Check

After an external consultation returns:

- save the durable transcript or imported response before summarizing it;
- extract the candidate formula, identity, closed form, proof skeleton, or
  blueprint;
- compare the candidate against the available numerical and structural data at
  a basic sanity-check level;
- label the result as `Conjectured` or `Needs check` unless independent proof
  or Lean verification has already been completed;
- record failures as useful evidence when a candidate does not match the data.

After a native campaign reaches a terminal state, preserve its authoritative
record first, then write or refresh the compact Stage 2 artifacts above before
summarizing it. Check each candidate against the available numerical and
structural data and present the applicable Stage 2 researcher gate.

Do not promote a claim because eight hours elapsed, subagents agreed, audits
were recorded, or the campaign record validator passed. A native-route
candidate remains `Conjectured` or `Needs check` unless an independently
accepted ordinary proof or formal verification supports promotion.

Do not ask the model to re-check itself and then report that as verification.
Model re-examination is only another candidate-generating step.
