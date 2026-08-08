# PEP Certificate Formalization

Use this reference when the target proof is a PEP upper bound or a symbolic
dual-certificate feasibility proof.

## Certificate Shape

A PEP upper-bound proof usually has the following structure:

1. State interpolation, oracle, algorithmic, and initial-condition inequalities.
2. Provide symbolic stepsizes, potentials, or method parameters.
3. Provide nonnegative symbolic multipliers for the inequalities.
4. Combine the inequalities linearly.
5. Prove the coefficient identities that make all unwanted terms cancel.
6. Prove the remaining expression implies the desired performance upper bound.

In Lean, formalize this as certificate feasibility, not as solver execution.
The proof should show that the symbolic multipliers and identities imply the
bound under the stated assumptions.

## Manifest

Create or identify a short certificate manifest before writing Lean. It should
contain:

- target theorem statement;
- variables and index ranges;
- definitions of iterates, gradients, function values, potentials, stepsizes,
  and multipliers;
- assumptions and inequalities that may be used;
- positivity or nonnegativity obligations;
- algebraic cancellation identities;
- final bound and performance measure;
- source paths for the paper proof, symbolic fit, and numeric evidence.

Do not ask Lean to reconstruct an unstated certificate. If the manifest is
missing a multiplier, sign condition, recurrence, or target expression, stop
and request a mathematical decision or a ChatGPT Pro blueprint.

## Lean Obligation Pattern

Prefer this order:

1. **Data definitions.** Define finite indices, coefficients, recurrences, and
   certificate variables in the simplest useful form.
2. **Domain lemmas.** Prove denominators are nonzero, indices are valid, and
   parameters lie in the required domain.
3. **Nonnegativity lemmas.** Prove all multipliers and weights are nonnegative.
4. **Identity lemmas.** Prove recurrence and coefficient-cancellation
   identities separately.
5. **Certificate combination lemma.** Show the weighted sum of PEP assumptions
   yields the certificate inequality.
6. **Final theorem.** Convert the certificate inequality into the paper-facing
   upper bound.

The final theorem should read as close as possible to the paper theorem, but it
may expose formal assumptions directly when that makes the certificate exact.
Record any mismatch.

## Useful Design Choices

- Use finite-dimensional real algebra when possible before importing analytic
  function-space machinery.
- Prefer explicit finite sums and recurrence identities for certificate proofs.
- Keep solver names out of Lean statements. Lean verifies symbolic feasibility,
  not solver optimality.
- Isolate long algebraic identities into named lemmas so repair can happen
  locally.
- Keep generated theorem names stable enough for downstream manuscript and
  ledger references.

## Boundaries

This skill does not prove that a solver found the certificate. It proves that a
given symbolic certificate is feasible and implies the stated bound. If the
certificate was obtained numerically, record that separately as computational
evidence.
