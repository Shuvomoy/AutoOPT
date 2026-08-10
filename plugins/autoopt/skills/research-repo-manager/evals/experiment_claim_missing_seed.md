# experiment_claim_missing_seed

## Setup

- `FINDINGS.md` contains a `Computed` claim supported by `results/table.csv`.
- The producing command or log omits seed, solver version, and termination
  status.

## Prompt

Use `$research-repo-manager` to audit the experiment evidence for current
findings.

## Must Pass

- Flags the claim as incomplete or needing check rather than fully reproduced.
- Reports missing seed, solver version, and termination status.
- Does not present the solver output as an exact theorem or certificate.
- Proposes a concrete rerun or logging next step.
