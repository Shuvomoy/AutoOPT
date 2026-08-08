# Explicit Opt-In BnB-PEP Stage 3

Load this reference only when the user explicitly asks for BnB-PEP Stage 3,
spatial branch-and-bound, or global nonconvex search for a BnB-PEP-QCQP.
Do not load it for ordinary Stage 1/2 derivations, Julia generation, smoke
tests, or AutoOPT Stage 3 Lean formalization.

## Boundary

BnB-PEP Stage 3 is the global-search stage of the BnB-PEP Algorithm. It
warm-starts the nonconvex BnB-PEP-QCQP from the Stage 2 local solution and
uses a spatial branch-and-bound solver to seek a solver-backed global-search
certificate for the outer design problem.

Default skill behavior remains Stage 1/2 only:

- Stage 1 fixes method parameters and solves the convex dual SDP.
- Stage 2 warm-starts a local nonlinear solve.
- Stage 1/2 smoke tests use `N = 1,2,3,4,5`.
- Stage 3 is never suggested or included unless the user explicitly asks.

When Stage 3 is explicitly requested, the Stage 3 default horizon is `N = 1`.
Do not inherit the Stage 1/2 smoke-test horizon set. Larger Stage 3 horizons
require an explicit user override.

## Solver Policy

The source BnB-PEP implementations use Gurobi's nonconvex spatial
branch-and-bound machinery for Stage 3. Treat Gurobi as an opt-in Stage 3
solver only. Do not make Gurobi a dependency of ordinary generated workflows.

Before any Stage 3 solver execution, require explicit user approval for:

- solver and version;
- horizon, with default `N = 1`;
- time limit;
- feasibility and optimality tolerances;
- MIPGap or absolute-gap target;
- thread count and random seed when material;
- log file path and output artifact path;
- whether a Stage 2 incumbent or global lower bound is supplied.

If no licensed global solver is available, stop with a missing-dependency
report. Do not emulate global certification with a local solver.

## Generated Artifact Shape

For docs-and-lint support, a Stage 3 artifact may include a separate opt-in
entry point that is not called by the default smoke tests. The generated file
must make the opt-in explicit, for example by requiring an
`explicit_stage3_request` keyword or a similarly clear gate before building
the global model.

The Stage 3 code path must state:

- `stage3_default_N = 1` or an equivalent `N = 1` default;
- larger horizons require an explicit override;
- solver output is solver evidence only;
- solver output is not a theorem, proof, or Lean verification;
- evidence fields are recorded before any global-search claim is made.

Use `python3 scripts/validate_generated_instance.py --julia path/to/file.jl
--allow-stage3-global` for static lint of an explicitly opt-in Stage 3 artifact.
Without `--allow-stage3-global`, the validator must reject Stage 3 and Gurobi
patterns.

## Evidence Checklist

A Stage 3 global-search claim is supported only when the run artifact records:

- solver name and version;
- termination status;
- incumbent objective value;
- best bound or global lower bound;
- absolute and relative gap, including MIPGap when relevant;
- feasibility tolerance;
- optimality tolerance;
- time limit and elapsed time;
- branching status or node-count summary when available;
- random seed and number of threads when material;
- log path;
- input artifact path and output artifact path;
- any license-sensitive settings redacted.

Solver status `OPTIMAL` with a recorded gap and tolerances may support a
solver-backed global-search certificate. It is still not a mathematical theorem
and not a Lean proof. If status is time-limited, infeasible, numerically
unstable, locally solved, or otherwise non-global, report the result as partial
or failed solver evidence.

## Status Language

Use precise language:

- "Stage 3 solver evidence supports global optimality up to the recorded
  solver tolerances and gap."
- "The Stage 3 run did not produce a solver-backed global-search certificate."
- "This remains computational evidence, not theorem-level proof."

Do not write:

- "proved globally optimal" unless a separate mathematical proof is supplied;
- "Lean verified" unless Lean files and successful checker output exist;
- "exact certificate" unless solver status, tolerances, gaps, and logs support
  that interpretation.
