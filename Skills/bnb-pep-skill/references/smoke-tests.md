# Smoke Tests

Smoke tests must be small and local. Use `N = 1,2,3,4,5`.

If the user's instance has an intrinsically fixed horizon (for example a
one-step method with `N = 1`), do not silently invent a generalization: when
the method family extends naturally to `N` steps (per-step parameters),
parameterize the generated code by the horizon and state in the derivation
that horizons above the user's `N` exist only for smoke testing; otherwise run
the user's horizon and report the remaining horizons as not applicable.

## What to Test

1. **Formalization completeness**
   - Every required schema field is filled.
   - Ambiguous assumptions are resolved by user answers, not guesses.

2. **Markdown derivation**
   - All required derivation sections are present.
   - The Stage 2 local problem section cites Lemma `Lem:quadratic-characterization-psd-1`.
   - The derivation includes the approval gate before Julia generation.

3. **Julia environment**
   - Run `julia scripts/check_julia_environment.jl` from the skill directory.
   - Require `JuMP`, `OffsetArrays`, `Clarabel`, and `Ipopt`.
   - Report recommended packages `MosekTools`, `Mosek`, and `KNITRO` when unavailable, but do not fail only because they are missing.
   - Do not install packages unless the user explicitly asks.

4. **Generated Julia**
   - Run `python3 scripts/validate_generated_instance.py --derivation derivation.md --julia generated.jl` as static lint.
   - Confirm no Stage 3/global branch-and-bound path is present.
   - If the solver environment is available, run `N = 1,2,3,4,5` routines:
     - primal SDP for fixed parameters;
     - dual SDP for fixed parameters;
     - local Stage 1/2 solve.
   - If any horizon cannot finish within the runtime budget or solver environment,
     report the blocker explicitly and do not claim full computational validation.

5. **Explicit opt-in Stage 3 static lint**
   - Use only when the user explicitly asks for BnB-PEP Stage 3 spatial
     branch-and-bound.
   - Stage 3 default horizon is `N = 1`; do not run `N = 1,2,3,4,5` for
     Stage 3 unless the user explicitly overrides the horizon.
   - Run `python3 scripts/validate_generated_instance.py --julia generated.jl --allow-stage3-global`.
   - The same artifact must still fail default static lint without
     `--allow-stage3-global`.
   - Static lint is not solver validation; do not claim a global certificate
     without solver logs, bounds, gaps, tolerances, and status.

## Missing Dependencies

If Julia or solvers are missing, report the exact issue. Example:

```text
Julia is available, but Clarabel is not installed in this environment.
Run the generated smoke tests after activating an environment with JuMP, OffsetArrays, Clarabel, and Ipopt. MosekTools, Mosek, and KNITRO are recommended when available but not required.
```

Do not claim computational validation when only static lint was possible.
