# Derivation Template

Generate a Markdown file for the specific BnB-PEP instance. Use this section order and include equations under each heading.

## 1. Formalized Instance

State the function class, retained interpolation or explicitly labeled non-exact inequalities, method equations, constants, performance measure, initial condition, normalization, index sets, auxiliary witnesses, and iteration budget. If the instance is composite, state all component functions, weights, component samples, composite values, and composite stationarity equations.

## 2. Outer Design Problem

State the problem of choosing method parameters to minimize the worst-case performance for the formalized `( \mathcal{E}, \mathcal{F}, \mathcal{C} )` setup.

## 3. Inner Worst-Case Problem for Fixed Parameters

Fix the method parameters and write the worst-case maximization problem.

## 4. Infinite-Dimensional Inner Problem

Write the optimization over functions and generated iterates. If `x_\star` and `f(x_\star)` are normalized, state why.

## 5. Interpolation Or Non-Exact Reduction

State the exact interpolation inequalities and any explicitly labeled necessary-only or sufficient-only constraints. Explain how they replace or relax the infinite-dimensional function variable by sampled points, gradients/subgradients, function values, and auxiliary witnesses. For composite objectives, state the interpolation block for each component separately and the linear equations assembling composite values and stationarity.

Include a certificate-status paragraph:

- exact rows give an exact finite PEP subject to rank and duality assumptions;
- necessary-only rows give a relaxed feasible set and an upper-bound model for the original worst-case value in a maximization PEP;
- sufficient-only rows give an inner or model-specific certificate unless a separate argument justifies the original-class claim.

If the weakly convex bounded-subgradient row is used, state proper lower-semicontinuity, \(\rho>0\), \(B\)-bounded regular subgradients, the \(C_{j,i}\) witness constraints, and that this row is an exact finite interpolation condition under those assumptions. For \(\rho=0\), use the Lipschitz convex row instead.

## 6. Finite-Dimensional Maximization

Write the finite-dimensional problem before Gramian lifting. Make every index set explicit.

If exact proximal maps appear, first state that the prox function is proper closed convex, then include the graph equations explicitly, for example
\[
x=\mathbf{prox}_{\gamma f}(u)
\quad\Longleftrightarrow\quad
x=u-\gamma g_f(x),\qquad g_f(x)\in\partial f(x).
\]

For double-function composite/proximal methods, define the smooth-component
sample set, the nonsmooth-component prox-output sample set, the pre-prox points,
and the shared Gramian basis before writing the finite maximization.

## 7. Gramian Formulation and Primal SDP

Define the Gramian matrix or matrices. Express all inner products as Gramian entries. State the large-scale assumption. Write the primal SDP in maximization form for fixed method parameters.

## 8. Dual SDP

Derive the dual SDP. Identify dual variables analogous to `\lambda`, `\nu`, `Z`, and any instance-specific variables. State sign restrictions and equality/PSD constraints.

## 9. Strong Duality

State the regularity or feasibility assumptions under which strong duality is used. If relying on the generic strong-duality posture of `references/bnb-pep-methodology.md` (Section 6), say so explicitly and mark it as an assumption.

## 10. Stage 2 Local Nonlinear Design Problem

Combine the outer problem with the dual SDP. Replace `Z \succeq 0` using Lemma `Lem:quadratic-characterization-psd-1`:

```text
Z = P P^T, where P is lower triangular and has nonnegative diagonal entries.
```

Write the resulting local nonlinear design problem explicitly. If all nonlinearities are quadratic or bilinear after introducing any needed auxiliary variables, call the formulation a QCQP. If cubic or trilinear expressions are modeled directly, call it a direct local NLP and document the solver compatibility assumptions. Map every chosen nonlinear expression or auxiliary variable to the derivation.

## 11. Stage 1/2 Implementation Plan

Describe:

- Stage 1: fix method parameters and solve the convex dual SDP for a feasible point.
- Stage 2: warm-start the local nonlinear design problem and solve locally with Ipopt or KNITRO.

Do not include BnB-PEP Stage 3 implementation steps unless the user explicitly
asks for BnB-PEP Stage 3 spatial branch-and-bound. In that opt-in case, load
`stage3-global-optimization.md` and keep the Stage 3 section separate from the
ordinary Stage 1/2 implementation plan.

## 12. Derivation-to-Julia Mapping Checklist

Map every mathematical object to a Julia object:

- constants and dimensions;
- index constructors;
- data generator outputs;
- component functions, component values, composite values, and proximal-map graph relations when present;
- weakly convex \(C_{j,i}\) witnesses and their quadratic constraints when present;
- double-function smooth/proximal sample blocks and pre-prox affine vectors when present;
- primal SDP variables and constraints;
- dual SDP variables and constraints;
- Cholesky variables and local nonlinear constraints;
- warm-start data from Stage 1 to Stage 2;
- smoke-test inputs for `N = 1,2,3,4,5`.

## Approval Gate

End with a request for explicit user approval before Julia generation. Do not generate Julia in the same response unless the user has already approved this exact derivation.
