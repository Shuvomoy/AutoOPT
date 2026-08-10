# Verification Profiles

Select every profile used by the admissible certificate. Apply the common gates
and then the profile-specific gates. Record evidence in `claim-ledger.md` and
failures or repairs in `audit-log.md`.

## Common gates

Before marking a resolution complete:

- Match the normalized target, quantifier order, assumptions, and parameter domains.
- Trace every dependency to proof, checked derivation, computation, literature, or an explicitly unresolved claim.
- Test boundary, degenerate, singular, equality, and empty cases.
- Reject circular reasoning, irreversible implications, and hidden regularity assumptions.
- Distinguish exact, symbolic, interval-certified, floating-point, and heuristic evidence.
- Require two fresh independent audits of the complete candidate.
- Give fresh auditors the problem contract and raw candidate without priming them with suspected flaws.
- Repair the smallest failed dependency and rerun every affected audit.
- Treat consensus, confidence, repetition, and model agreement as neither proof nor certification.
- Claim formal or machine verification only when an actual checker accepts the artifact.

## Proof

Require an end-to-end derivation with no omitted claim carrying substantive
proof burden. Verify every invoked theorem's hypotheses, each change of
quantifier or limit, and every case split. Reconstruct decisive steps
independently and search for counterexamples to intermediate lemmas.

Pass only when the proof establishes the target exactly. Label a plausible
argument with a missing lemma `Needs check`, not `Proven`.

## Disproof

Require an explicit counterexample in the target's admissible domain. Verify
its construction exactly when feasible, confirm every premise, and compute the
precise failed conclusion. Audit minimal or boundary cases and rule out an
artifact of numerical tolerance or ambiguous interpretation.

Pass only when one valid instance contradicts the correctly normalized
universal or existential claim as logically appropriate.

## Construction

Require an explicit object or reproducible generation rule. Prove existence,
well-definedness, domain membership, and every claimed property. Verify that
the construction does not depend on unavailable choices, circular selections,
or a hidden compactness or choice argument.

Pass only when the produced object and all interfaces satisfy the contract.

## Algorithm

Require precise input, output, preconditions, and pseudocode or executable
implementation. Prove correctness and termination. Prove any stated
complexity, approximation, convergence, stability, or oracle guarantee under
the recorded model of computation.

Test representative, adversarial, boundary, and malformed inputs. Treat passing
tests as evidence, not as a correctness proof.

## Computational

Record the exact command, working directory, source snapshot, environment,
language and package versions, seeds, threads, solver and version, tolerances,
time limits, termination status, bounds or gaps, inputs, and outputs. Preserve
logs needed to reproduce the claim.

Set a maximum allowed runtime of 180 minutes for every code or solver
execution. Do not manually terminate it earlier unless it exits, the user
explicitly asks, or the platform ends it. Split longer work into checkpointable
executions.

Classify the result as exact, interval-certified, symbolic, floating-point, or
heuristic. Do not convert numerical evidence into a theorem without a rigorous
bridge. Do not call solver output an exact certificate unless status,
tolerances, gaps, and logs justify that claim.

## Literature-supported

Use repository-provided literature even when it concerns the exact target.
For public sources, restrict lookup to ordinary mathematical background and
standard named theorems; never search the exact problem, a solution, or its
open/closed status.

Record citation or provenance, exact theorem statement, version, and every
hypothesis used. Verify that notation, domains, regularity, and conclusions
match the target. Treat a secondary summary as a lead, not as final authority,
when a primary or authoritative source is available.

## Audit outcomes

Record each fresh audit as `pass`, `fail`, or `inconclusive`, with the auditor's
independent artifact and exact affected claim IDs. Two passes do not replace
the certificate; they establish only that two independent attacks found no
unrepaired defect. A complete candidate must cover both machine-readable audit
scopes: `dependency_quantifier_edge_case` and
`adversarial_counterexample_circularity`.

For an incomplete campaign, preserve the strongest verified claims and name
the smallest unresolved dependency. State that the campaign did not establish
a complete resolution; do not answer merely that the problem is open. Do not
voluntarily close before both the frozen wall-clock and active-work floors in
`campaign.yaml`. If a candidate appears early, continue independent
reconstruction and adversarial auditing. After both floors hold, continue while
a round materially advances, refutes, or decisively tests an important
dependency.
