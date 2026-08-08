# Supported Setups

This reference describes setup families currently covered by the skill. It is
portable by design: it does not depend on local papers, logs, manuscript files,
or project-specific case identifiers.

Citation hints are background only. Useful anchors include classical PEP
formulations, finite interpolation conditions for smooth convex classes,
Branch-and-Bound Performance Estimation Programming, and composite/proximal PEP
work. These hints do not replace the user's supplied problem statement,
mathematical assumptions, or proof/source provenance for any new condition.

## Core BnB-PEP Pattern

The skill supports BnB-PEP derivations that fit this pattern:

- a finite set of sampled points, gradients/subgradients, and scalar function
  values;
- a fixed-step first-order method or fixed-parameter method class encoded by
  affine update equations in the sampled vectors;
- interpolation, graph, or stationarity constraints expressible as scalar
  affine constraints or quadratic Gramian constraints;
- an inner worst-case problem reduced to a finite Gramian SDP;
- a fixed-parameter dual SDP and a Cholesky-parameterized local nonlinear model;
- Stage 1/2 local computation by default: solve a convex dual SDP for an
  initial feasible point, then warm-start a local nonlinear solve.

The skill does not implement Stage 3, global spatial branch-and-bound, Gurobi
global-solver paths, or global-optimality certification by default. An
explicitly requested BnB-PEP Stage 3 path is governed by
`stage3-global-optimization.md`, defaults to `N = 1`, and provides solver
evidence only.

## Interpolation Families

Use `references/interpolation-conditions.md` for the retained row formulas. The
currently covered families include:

- smooth convex finite interpolation and smooth strongly convex finite
  interpolation, including common specializations such as convex, strongly
  convex, smooth, and smooth convex rows;
- smooth finite interpolation for differentiable \(L\)-smooth functions;
- exact weakly convex finite interpolation for proper lower-semicontinuous
  \(\rho\)-weakly convex functions with \(B\)-bounded regular subgradients,
  using the Rubbens-Hendrickx auxiliary \(C_{j,i}\) witness conditions;
- Lipschitz convex and smooth Lipschitz convex systems when the required radius
  or diameter constants are supplied;
- closed convex indicator and convex support-function rows when the
  corresponding samples and domain constants are supplied.

The current retained table has no active LMI-valued rows. LMI conditions are
future user-supplied extensions governed by the controlled extension protocol.

## Smooth Nonconvex Gradient-Reduction Setup

The compact skill supports the Stage 1/2 formulation of smooth nonconvex
gradient-reduction PEPs when the user supplies an \(L\)-smooth differentiable
function with a global minimizer \(x_\star\), fixed-step gradient-style update
rules, a function-gap initial condition, and a gradient-norm performance
measure. The finite model should include:

- the \(L\)-smooth nonconvex interpolation row from
  `references/interpolation-conditions.md` on samples
  \(\{\star,0,\ldots,N\}\);
- \(g_\star=0\) and \(f_\star\le f_i-\|g_i\|^2/(2L)\) for all sampled iterates;
- an epigraph variable for \(\min_i\|g_i\|^2\), with constraints
  \(\tau\le \|g_i\|^2\);
- explicit large-scale rank assumptions before dropping any Gramian rank
  constraint.

Certificate status: the pairwise \(L\)-smooth row together with
\(g_\star=0\) and \(f_\star\le f_i-\|g_i\|^2/(2L)\) is an exact finite
description of \(L\)-smooth functions with a global minimizer \(x_\star\)
(literature-supported: Drori and Shamir 2020, Theorem 7, in the form of
Taylor, Hendrickx, and Glineur 2017, Theorem 3.10). State this status in
generated derivations.

This setup supports local Stage 1/2 computation and derivation of fixed-parameter
dual certificates. It does not certify global optimality of the outer design
problem without separate evidence.

## Method-Design Families

The skill supports fixed-step first-order method design through PEP when the
method class is described by explicit affine update rules, for example:

- fixed-step gradient or subgradient-style methods with coefficient variables;
- fixed-parameter evaluations of a proposed method;
- performance measures such as function-value gap, gradient norm, stationarity
  residual, potential value, or other scalar Gramian/value expressions;
- initial conditions such as distance, function gap, gradient bound, potential
  bound, or a user-supplied scalar normalization.

The user must specify whether method parameters are optimized or fixed. If a
method uses an unsupported oracle or primitive graph relation, apply the
extension protocol before deriving.

## Composite And Proximal Families

Use `references/composite-primitives.md` for exact rules. The currently covered
families include:

- finite or signed sums represented by separate component interpolation blocks
  and shared point samples;
- composite stationarity and difference-of-convex stationarity assembled from
  component gradients or subgradients;
- exact Euclidean proximal-map graph relations for proper closed convex
  functions whose interpolation rows are already covered by the table;
- generic OptISTA-style double-function composite/proximal FSFOMs with separate smooth
  component and proper-closed-convex component interpolation blocks, affine
  update equations for both \(x_i\) and prox-generated \(y_i\), and shared
  Gramian coefficient vectors.
Do not impose interpolation conditions directly on a signed composite objective
unless the user supplies a valid class condition for that composite.

## Controlled Extension Protocol

Apply this protocol only when the user explicitly supplies a new interpolation
condition, oracle condition, or primitive step. The agent may organize,
formalize, and add the supplied setup to the skill, but must not invent missing
mathematics.

Each new entry must carry one provenance label:

- `user-supplied`: the user supplied the condition or primitive, but independent
  proof or literature provenance has not been checked in-session.
- `literature-supported`: the entry is backed by a named paper, book, or
  technical source supplied by the user or verified in-session.
- `proved in-session`: the session produced a proof that is recorded with the
  entry or in a linked local artifact.
- `conjectural/needs check`: the entry is plausible or proposed, but not yet
  verified enough for claims beyond exploratory computation.

Each new entry must also state its mathematical status:

- exact finite interpolation;
- necessary-only condition;
- sufficient-only condition;
- exact graph relation;
- relaxation of an exact graph relation;
- conjectural relation.

### New Interpolation Or Oracle Conditions

Before adding a row to `references/interpolation-conditions.md`, check and
record:

- function class and all assumptions;
- sample variables and scalar values;
- admissible index ranges and excluded diagonal cases;
- constants, signs, domains, and normalization conventions;
- inequality, equality, or LMI form;
- whether the condition is necessary, sufficient, exact, or conjectural;
- dual multiplier type and sign/PSD constraints;
- proof/source provenance and provenance label;
- any limitations on dimension, closedness, attainment, smoothness, or
  differentiability.

Do not silently infer nearby classes. For example, a supplied smooth convex row
does not automatically authorize smooth strongly convex, weakly convex, or
composite variants.

If a future user supplies an LMI condition
\(M_r(G,q;\theta)\preceq0\), record the PSD multiplier
\(Y_r\succeq0\), the dual contribution
\(\langle Y_r,M_r(G,q;\theta)\rangle\), and either the Stage 2
factorization \(Y_r=Q_rQ_r^\top\) or an explicit fixed-SDP-only boundary until
a Stage 2 representation is supplied.

### New Primitive Steps

Before adding a primitive entry to the minimal retained reference file, check
and record:

- graph relation defining the primitive;
- input, output, witness, and auxiliary samples introduced by the primitive;
- scalar constraints and vector equations;
- dual multipliers and their sign or PSD domains;
- exactness versus relaxation status;
- how the primitive interacts with existing interpolation blocks;
- any implementation implications for primal SDP, dual SDP, and Stage 1/2 local
  nonlinear generation.

If the primitive introduces nontrivial JuMP modeling choices, add a concise
section to `references/julia-implementation-guide.md` mapping its variables,
constraints, and multipliers to generated code.

### Extension Acceptance Checks

After any skill extension:

- re-read the affected reference file and confirm the new entry is scoped only
  to the supplied assumptions;
- run the generated-instance static linter self-test;
- run the Julia environment checker when Julia generation remains in scope;
- confirm the default Stage 1/2 boundary and default no-Gurobi boundary still
  hold;
- ask the user to review the new mathematical entry before relying on it for a
  manuscript or a claim of exactness.

## Solver Expectations

Generated Stage 1/2 workflows must work with `JuMP`, `OffsetArrays`,
`Clarabel`, and `Ipopt`. Prefer `MosekTools` and `Mosek` for convex SDP models
when installed, and prefer `KNITRO` for Stage 2 local nonlinear solves when
installed.
Treat these commercial or recommended solvers as helpful accelerators, not hard
requirements.

Do not require, invoke, or generate a global branch-and-bound solver path in
default workflows. If the user explicitly asks for BnB-PEP Stage 3, load
`stage3-global-optimization.md`; Gurobi is then an opt-in Stage 3 solver, not a
default dependency.
