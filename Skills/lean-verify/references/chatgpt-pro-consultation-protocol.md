# ChatGPT Pro Consultation Protocol

Use ChatGPT Pro to obtain proof-planning blueprints without treating model
output as proof.

In Assisted Source-To-Lean Mode for optimization theorem, proof, or certificate
targets, load `chatgpt-pro-blueprint-to-agentic-lean.md` for the full workflow.

In Direct Lean Repair Mode, use ChatGPT Pro only when the mathematical
decomposition is missing or unclear. The consultation output is a blueprint
for the host agent to inspect and formalize locally, not a proof.

## When To Consult

Consult for:

- decomposing a paper proof into formal lemmas;
- identifying missing side conditions, proof obligations, certificate
  identities, or sign lemmas;
- checking whether a proposed Lean theorem statement matches the paper claim;
- suggesting a proof order for difficult algebraic, finite-sum, recurrence, or
  certificate obligations;
- producing a Lean implementation blueprint when Assisted Source-To-Lean Mode
  is active.

Do not consult merely to bypass reading the certificate, and do not ask the
consultant to certify correctness.

## Approve-Before-Send Gate

Before sending any files externally, show the user:

- ChatGPT Pro session and model configuration;
- exact outgoing file list;
- token or size preview when available;
- the precise question being asked;
- confirmation that no secrets or irrelevant private material are attached.

Proceed only after explicit approval.

When this protocol is invoked through Lean Verify, this exact-manifest gate
controls even if a selected consultation skill treats direct invocation as
standing consent.

## Prompt Shape

The prompt should ask for:

- a theorem-statement proposal;
- a lemma dependency graph;
- all domain and nonnegativity side conditions;
- the algebraic identities and theorem-specific obligations needed for the
  proof, including certificate feasibility obligations when applicable;
- a minimal Lean-friendly proof order;
- a source-to-claim map and explicit excluded claims;
- a proposed module graph and theorem-wrapper surface;
- a proposed comparator-wrapper surface (`Challenge.lean`, `Solution.lean`,
  `config.json`), theorem names, and permitted axioms when comparator replay
  is feasible;
- a list of assumptions that must not be silently strengthened.

For source-to-Lean blueprints, also require a clearly delimited
`BEGIN_LEAN_BLUEPRINT` / `END_LEAN_BLUEPRINT` section. Ask the consultant to
label uncertain steps and to avoid claiming Lean verification or comparator
success.

## Return Handling

On return:

- archive the transcript or output in the project run folder;
- compare the blueprint against the paper proof, theorem target, and symbolic
  certificate when applicable;
- reject silent theorem weakening, missing side conditions, or changed index
  ranges before writing Lean;
- label blueprint claims as `Conjectured` or `Needs check`;
- carry only inspected, explicit obligations into Lean;
- use any proposed `Challenge.lean`/`Solution.lean`/`config.json` surface only
  as a draft until the local build+hygiene layer passes and the human
  researcher approves the wrapper/config surface;
- do not treat a second model's agreement as verification.
