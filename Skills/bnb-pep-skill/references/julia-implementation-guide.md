# Julia Implementation Guide

Use this guide only after the user approves the Markdown derivation.

## Required Outputs

Generate one Julia file for the formalized instance. Include:

- a data generator;
- a primal SDP model for fixed method parameters;
- a dual SDP model for fixed method parameters;
- a Stage 2 local nonlinear model using `Z = P * P'`;
- smoke-test routines for `N = 1,2,3,4,5`.

## Style

Follow the organization and naming style of the BnB-PEP example code:

- small utilities such as `e_i` and symmetric outer-product helpers like `⊙`; cardinality/rank helpers and Cholesky zero-pattern helpers are optional, not required;
- direct JuMP-indexed dual variables when natural, such as `@variable(model, λ[i = -1:N, j = -1:N; i != j] >= 0)`; explicit index-constructor functions are optional;
- data generator functions that return coefficient vectors, matrices, and functions needed by the models;
- `OffsetArrays` when it keeps Julia indices close to the mathematical index sets, such as `-1:N` for `\{\star,0,\ldots,N\}` or `1:N, 0:N-1` for triangular method coefficients;
- Function names should be `solve_primal_pep` for solving primal PEP in maximization form, `solve_dual_pep` for solving the dual PEP in minimization form, and `solve_bnb_pep` for solving the stepsize optimization problem.

Use clear Julia functions rather than notebook-style global scripts. Keep constants and tolerances as keyword arguments.

## Composite and Proximal Models

When an instance has \(F(x)=\sum_{\ell=1}^m a_\ell f_\ell(x)\), keep separate arrays or dictionaries for each component's scalar values and gradient coefficient vectors. Build interpolation constraints and dual multipliers per component, but assemble objective, initial-condition, and performance expressions from the component values.

For composite stationarity at \(x_\star\), enforce \(\sum_\ell a_\ell g_{\ell,\star}=0\). In generated code, prefer defining one component gradient coefficient vector from the others when this is simpler than adding vector equality constraints.

For exact proximal maps of proper closed convex functions, express the output point as an affine vector relation. For example, encode \(x=\mathbf{prox}_{\gamma f}(u)\) as:

```julia
x_vec = u_vec - gamma * grad_f_x_vec
```

If \(u\) is itself an affine expression, expand it before storing the coefficient vector. Do not introduce a separate black-box proximal operator in generated Julia.

For double-function composite/proximal FSFOMs, build one shared vector basis for the initial point, smooth gradients, proximal subgradients, and any other vector witnesses. Store separate scalar-value arrays for the smooth component and the proper-closed-convex component. Encode \(x_i\), \(y_i\), and pre-prox \(\tilde y_i\) as coefficient vectors; the prox graph relation should be reflected by the coefficient identity

```julia
y_vec = y_tilde_vec - gamma * h_subgrad_vec
```

before interpolation constraints are assembled. Do not call a proximal routine inside the generated SDP or Stage 2 model.

## Weakly Convex Bounded-Subgradient Rows

For the Rubbens-Hendrickx weakly convex row with \(\rho>0\), introduce a vector witness coefficient `C[j, i]` for each ordered interpolation pair using the row. Add `C[j, i]` to the Gramian basis or define it as a coefficient vector in the existing basis if the derivation provides such a representation.

For each ordered pair, generate the scalar interpolation inequality and the two quadratic bounds:

```text
f[i] - f[j] >= dot(g[j], x[i] - x[j])
                 - rho / 2 * norm2(x[i] - x[j])
                 + rho / 2 * norm2(x[i] - C[j, i])
norm2(g[j] + rho * (x[j] - C[j, i])) <= B^2
norm2(g[j]) <= B^2
```

Express each dot product and squared norm through the Gramian. Use this row only with a declared regular-subgradient convention and \(B\)-bounded subgradients. For \(\rho=0\), use the Lipschitz convex row instead of creating `C[j, i]` witnesses.

## Solver Policy

- Use `JuMP`.
- Hard package requirements are `JuMP`, `OffsetArrays`, `Clarabel`, and `Ipopt`.
- For SDP models, prefer `MosekTools`/`Mosek` when installed; fall back to `Clarabel` when Mosek is unavailable.
- For Stage 2 local nonlinear solves, prefer `KNITRO` when installed; fall back to `Ipopt` when KNITRO is unavailable.
- Treat `MosekTools`, `Mosek`, and `KNITRO` as recommended packages, not hard requirements.
- Generated code should select available solvers gracefully and report missing solver packages instead of failing silently.
- In default Stage 1/2 workflows, do not require Gurobi.
- In default Stage 1/2 workflows, do not set `solution_type = :find_globally_optimal`.
- In default Stage 1/2 workflows, do not include Gurobi attributes such as `NonConvex`, `MIPGap`, or global branch-and-bound callbacks.

## Explicit Opt-In BnB-PEP Stage 3

Use `references/stage3-global-optimization.md` only when the user explicitly
asks for BnB-PEP Stage 3 spatial branch-and-bound or global nonconvex search.
Do not add Stage 3 code to ordinary generated artifacts.

For an explicitly requested Stage 3 artifact:

- keep the Stage 3 entry point separate from `run_stage1_stage2_smoke_tests`;
- set the Stage 3 default horizon to `N = 1`;
- require an explicit override for larger Stage 3 horizons;
- require a clear opt-in gate before constructing a Gurobi/global model;
- record solver-evidence fields before making a global-search claim;
- state that Stage 3 output is solver evidence only, not theorem-level proof.

Run static lint with:

```bash
python3 scripts/validate_generated_instance.py --julia path/to/generated.jl --allow-stage3-global
```

The default validator mode must still reject the same artifact.

## Stage 1

Implement Stage 1 by fixing method parameters to a reasonable initialization and solving the convex dual SDP. Return:

- objective value;
- dual variables;
- slack matrix `Z`;
- Cholesky or pivoted Cholesky factor when computable;
- a warm-start `NamedTuple` for Stage 2.

Use a self-contained mathematically justified initialization. For the canonical smooth strongly convex fixed-step example, a simple gradient-descent initialization with incremental coefficients `h_{i,i-1} = 1` and `h_{i,j} = 0` for `j < i-1` is acceptable. Otherwise require the user to supply or approve the initialization before Stage 1.

## Stage 2

Implement Stage 2 by building the local nonlinear design model, replacing PSD constraints by Cholesky constraints:

```julia
@variable(model, Z[1:dim_Z, 1:dim_Z], Symmetric)
@variable(model, P[1:dim_Z, 1:dim_Z])
@constraint(model, [i=1:dim_Z, j=i+1:dim_Z], P[i, j] == 0)
@constraint(model, [i=1:dim_Z], P[i, i] >= 0)
@constraint(model, vectorize(Z - P * P', SymmetricMatrixShape(dim_Z)) .== 0)
```

Adapt the exact indexing to the instance. Warm-start all variables available from the Stage 1 `NamedTuple` using dot access when fields are available.

## Nonlinear Terms

If the derivation contains cubic or trilinear terms, generated Julia may either model them directly with a compatible local nonlinear solver, such as KNITRO or Ipopt, or introduce auxiliary variables so every nonlinear constraint is quadratic or bilinear. Call the direct formulation a local NLP, and reserve QCQP terminology for the quadratic or bilinear auxiliary formulation. In either case, document the choice and map every nonlinear Julia expression or auxiliary variable back to the mathematical derivation.

## Smoke Tests

Include a smoke-test entry point that:

- uses `N = 1,2,3,4,5`;
- tests primal SDP with fixed parameters;
- tests dual SDP with fixed parameters;
- tests the local Stage 1/2 path;
- skips tests gracefully if required solver packages are missing.

Required solver packages for computational smoke tests are `Clarabel` for SDPs and `Ipopt` for local nonlinear solves. Use Mosek/MosekTools and KNITRO when available, but do not require them.

## Generated Artifact Static Lint

Run:

```bash
python3 scripts/validate_generated_instance.py --derivation path/to/derivation.md --julia path/to/generated.jl
julia scripts/check_julia_environment.jl
```

The Python validator is static lint, not computational validation. If Julia or solvers are unavailable, report missing dependencies and exact manual commands rather than claiming the smoke tests ran.
