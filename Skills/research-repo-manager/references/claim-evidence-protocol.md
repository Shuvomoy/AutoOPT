# Claim Evidence Protocol

Use this reference when initializing or substantially refreshing `FINDINGS.md`.
The goal is to make each research claim traceable to the evidence that justifies
its current status.

## Claim Statuses

- `Proven`: a complete proof is recorded or cited.
- `Derivation checked`: algebraic, variational, or algorithmic derivation has
  been checked, but is not yet packaged as a formal theorem.
- `Computed`: supported by a reproducible computation with command,
  environment, seed when relevant, solver status, and output artifact.
- `Literature`: supported by a cited theorem, proposition, experiment, or
  statement in `SOURCES.md`.
- `Conjectured`: plausible but not proved or experimentally certified.
- `Refuted`: a counterexample, failed condition, or invalid dependency is
  recorded.
- `Needs check`: useful but not reliable enough to cite as an active finding.

## Recommended Ledgers

Use stable IDs when an item is referenced across files.

```markdown
## Claim Ledger

| ID | Claim | Status | Assumptions | Evidence | Dependencies | Last checked |
|---|---|---|---|---|---|---|
| F001 |  | Proven / Derivation checked / Computed / Literature / Conjectured / Refuted / Needs check |  | Source/log/experiment/artifact IDs |  |  |

## Theorems, Lemmas, and Conjectures

| ID | Label | Statement | Assumptions | Status | Proof location | Dependencies | Failure modes |
|---|---|---|---|---|---|---|---|
| T001 |  |  |  | proved / partial / false / conjecture |  |  |  |

## Assumptions

| ID | Assumption | Used in | Source / justification | Can it be weakened? |
|---|---|---|---|---|
| A001 |  |  |  |  |

## Negative Results and Counterexamples

| ID | Statement tested | Counterexample / failure mode | Evidence | Consequence |
|---|---|---|---|---|
| N001 |  |  |  |  |
```

## Rules

- Do not collapse proof evidence, solver evidence, literature evidence, and
  conjecture into one undifferentiated "finding" category.
- Do not present computational evidence as a theorem.
- Do not present a solver status as an exact certificate unless the solver log,
  tolerances, gap, and termination status justify that statement.
- Keep failed attempts and counterexamples visible when they affect the active
  research direction.
