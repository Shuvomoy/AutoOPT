# Formalization Schema

Before deriving or coding, formalize the user-provided instance. If any required entry is unknown, ask a targeted clarification question and stop.

## Required Instance Fields

- **Function class**: name `\mathcal{F}`, domain, differentiability/subdifferentiability assumptions, convexity or nonconvexity, smoothness/weak convexity constants, and any boundedness assumptions.
- **Composite structure**: when applicable, component functions \(f_\ell\), signed weights \(a_\ell\), shared point samples, per-component gradients and values, composite values, and composite or difference-of-convex stationarity equations. Consult `references/composite-primitives.md`.
- **Interpolation or non-exact inequalities**: exact interpolation inequalities, explicitly labeled necessary/sufficient conditions, index ranges, constants, and any auxiliary witness variables required by the row. If a retained function class is named but the inequalities are not supplied, consult `references/interpolation-conditions.md`.
- **Certificate status**: whether each retained condition is exact, necessary-only, sufficient-only, or user-supplied. For a necessary-only condition in a worst-case maximization, record that the finite PEP is a relaxation giving an upper-bound model for the original class.
- **Sample objects**: points `x_i`, gradients or subgradients `g_i`, function values `f_i`, optimal point `x_\star` if used, and any auxiliary oracle outputs, witness points such as weakly convex \(C_{j,i}\), or accuracy scalars.
- **Index sets**: iteration set, interpolation-pair set, performance-measure set, initial-condition set, and any extra index sets for potentials or auxiliary variables. The performance-measure set and initial-condition set are the index sets over which \(\mathcal{E}\) and \(\mathcal{C}\) are evaluated, for example \(\{N\}\) for a terminal measure and \(\{(0,\star)\}\) for a distance initial condition.
- **Method class**: FSFOM update equations and all method variables, such as `h_{i,j}`, `\alpha_{i,j}`, or single-step parameters.
- **Primitive graph relations**: exact Euclidean proximal-map equations for proper closed convex functions, projection equations induced by indicator functions, double-function prox-generated point equations when present, and any other user-supplied graph equations. Do not infer unsupported primitive rules; exact proximal maps for proper closed convex functions are covered in `references/composite-primitives.md`.
- **Fixed/default parameters**: Stage 1 starting method parameters, default stepsizes, signs/nonnegativity constraints, normalization choices, and whether parameters are optimized.
- **Performance measure**: exact scalar objective `\mathcal{E}` to maximize in the inner problem and minimize in the outer problem.
- **Initial condition**: exact constraint `\mathcal{C}`, such as distance, function gap, gradient bound, or potential bound.
- **Constants**: `L`, `\mu`, `R`, `\rho`, `M`, condition numbers, scaling assumptions, and units.
- **Iteration budget**: `N`, including how to run smoke tests for `N = 1,2,3,4,5`.
- **Dimension assumption**: large-scale assumption needed for the Gramian SDP: `d >= m`, where `m` is the exact number of columns of the Gramian basis `H` for the specific instance, counted from the declared samples, witnesses, and auxiliary vectors. Do not assume a category default: `m` varies from setup to setup. For retained setups without per-pair witnesses, `m` is affine in the horizon, `m = aN + b` with setup-dependent nonnegative integers `a` and `b`; for instance, the canonical single-function example of `references/bnb-pep-methodology.md` happens to have `m = N+2`, and the usual double-function composite pattern has `m = 2N+3` or `2N+4` depending on the declared samples. Rows that introduce per-pair witnesses, such as the weakly convex \(C_{j,i}\) row, add witness columns beyond this affine count. Record an instance-specific alternative if the user supplies one.
- **Strong-duality posture**: whether the derivation assumes strong duality, cites genericity, or uses a formulation that avoids relying on equality of two optimal values.

## Clarification Policy

Ask follow-up questions when:

- The function class is named without its interpolation/oracle inequality.
- A weakly convex row is used without its weak-convexity constant, subgradient bound, regular-subgradient convention, and auxiliary \(C_{j,i}\) witness variables.
- A nonconvex or non-exact user-supplied row is used without its certificate status and regularity assumptions.
- The method is described informally without update equations.
- A composite objective is named without specifying its components, weights, and stationarity relation.
- A proximal map is named without specifying the function, input point, stepsize, and whether the built-in proper-closed-convex prox graph applies.
- A user-supplied primitive is named without specifying the graph relation, input samples, output samples, auxiliary variables, scalar/vector constraints, dual multipliers, and exactness or relaxation status.
- The performance measure or initial condition omits normalization constants.
- The user gives a finite-dimensional example but not the intended large-scale Gramian assumption.
- It is unclear whether the task optimizes method parameters or evaluates fixed parameters.
- The instance would require Stage 3/global certification. Default workflows
  support only Stage 1/2 local implementation; if the user explicitly asks for
  BnB-PEP Stage 3, use `stage3-global-optimization.md` and treat outputs as
  solver evidence only.

## Interpolation Lookup

Use `references/interpolation-conditions.md` as a compact lookup table for retained function-class conditions. The retained table consists of exact finite interpolation rows under their stated assumptions. If a future user-supplied row is labeled necessary-only, it is not a full finite interpolation condition and must not be described as exact interpolation; in a worst-case maximization it enlarges the feasible set and gives an upper-bound relaxation of the original worst-case value.

For the retained weakly convex bounded-subgradient row, introduce the \(C_{j,i}\) witness for each ordered pair that uses the row and include both quadratic bound constraints. Do not replace it by the weaker first-order relaxation unless the user explicitly asks for a relaxation and labels the consequence.

The current retained table has no active LMI-valued rows. LMI conditions are future user-supplied extensions governed by the self-extension protocol, including PSD multipliers and an explicit Stage 2 factorization or fixed-SDP-only boundary.

If the requested class is not covered by the table, do not derive from analogy. Ask the user for the finite interpolation or oracle condition, including variables, index ranges, constants, necessity/sufficiency/exactness status, and proof/source provenance. If the condition is added to the skill, label the entry as `user-supplied`, `literature-supported`, `proved in-session`, or `conjectural/needs check`.

## Composite and Proximal Lookup

Use `references/composite-primitives.md` when the instance contains finite or signed sums, component-wise objective values, composite stationary points, difference-of-convex stationarity, exact proximal maps for proper closed convex functions, or double-function composite/proximal FSFOMs. Keep component interpolation blocks separate while sharing one Gramian basis for all sampled vectors. Do not impose interpolation constraints directly on a signed composite unless the supplied instance provides a valid class condition for that composite.

## New Primitive Requests

If the requested primitive is not covered, ask the user for its graph relation, introduced samples, scalar/vector constraints, auxiliary variables, dual multipliers, and exactness or relaxation status before adding it to the skill. Do not generate Julia for an unsupported primitive until this formalization is complete.

## Normalization

Use normalizations such as `x_\star = 0` and `f(x_\star)=0` only when justified by the BnB-PEP methodology for the supplied class and initial condition. State the justification in the derivation. A standard justification template: (i) the function class is closed under translations \(x\mapsto x+c\) and under adding constants to each component separately; (ii) the method is translation-covariant; (iii) the performance measure and initial condition depend only on differences of points and on value differences within each component block. For composite instances, state each item per component. If a minimizer may not exist, do not introduce `x_\star` unless the user supplies an assumption or the formulation uses it only as a formal reference with caveats.

## Completion Criteria

The instance is ready for derivation only when another researcher could write every constraint of the infinite-dimensional inner problem and identify every decision variable without making additional choices.
