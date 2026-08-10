# Source-To-Lean Project Patterns

Use this reference when a mathematical working note spans multiple LaTeX files
and the output should be a full Lean/Lake verification folder rather than a
single theorem file.

## General Pattern

Start with a source manifest and build a theorem-oriented module graph. Avoid
line-by-line translation. The Lean project should expose a small theorem
surface and hide long algebraic, recurrence, interpolation, or certificate
details in named internal modules.

Recommended layers:

1. **Setting and parameters.** Define domains, spaces, functions, horizons,
   recurrences, stepsizes, admissibility assumptions, and theorem-specific
   parameters.
2. **Target data.** Define certificate data when present, or otherwise define
   the sequences, maps, potentials, residuals, Lyapunov functions, or auxiliary
   quantities used by the proof.
3. **Supporting lemmas.** Prove domain facts, nonnegativity, monotonicity,
   recurrence identities, coefficient cancellation, telescoping, convexity or
   smoothness consequences, and PSD or SOS identities as needed.
4. **Model bridge.** Connect finite algebra or certificate data to
   interpolation, smooth-convex inequalities, function-model semantics, or
   algorithm trajectories when the theorem requires it.
5. **Algorithm or construction layer.** Define the executable recurrence,
   memory-efficient form, certificate trajectory, or mathematical construction
   and prove equivalence with the theorem-facing object.
6. **Final theorem layer.** State the paper-facing theorem using stable
   theorem names.
7. **Comparator or audit layer.** Add `Solution.lean`, `Challenge.lean`,
   `config.json`, `AxiomAudit.lean`, or project-specific checker files. When a
   comparator-compatible theorem surface is feasible, comparator replay is the
   default closeout layer after `lake build` and static hygiene.

## General Optimization Theorem Pattern

Use this pattern when the target is a detailed optimization theorem or proof
that is not primarily a PEP dual certificate.

Typical source material:

- theorem statement with explicit quantifiers and assumptions;
- definitions of the optimization model, algorithm, recurrence, potential, or
  variational object;
- proof broken into inequalities, recurrence steps, induction steps,
  telescoping steps, limiting arguments selected for formalization, or named
  supporting lemmas;
- final performance, convergence, feasibility, monotonicity, or equivalence
  claim.

Typical Lean modules:

- theorem-facing declarations and notation;
- domain and side-condition lemmas;
- algebraic or order-theoretic lemmas;
- recurrence, induction, finite-sum, or telescoping lemmas when present;
- convexity, smoothness, or model-specific bridge lemmas when needed;
- final theorem wrappers and comparator-facing files when feasible.

Default exclusions:

- informal motivation, numerical evidence, diagrams, and historical discussion;
- theorem variants whose assumptions differ from the selected target;
- asymptotic, limiting, or infinite-dimensional strengthening unless explicitly
  selected and supported by the source proof.

## Gradient-Rate Certificate Pattern

Use this pattern for finite-horizon accelerated-gradient results where the
main output is a gradient-norm or endpoint residual upper bound.

Typical source material:

- parameter recurrence or shooting construction;
- symbolic dual-feasibility certificate;
- interpolation inequalities for smooth convex functions;
- trajectory or memory-efficient implementation;
- final finite-horizon gradient-rate theorem.

Typical Lean modules:

- parameter assumptions, recurrence construction, and uniqueness;
- quadratic-form or matrix/slack utilities;
- certificate feasibility and nonnegativity;
- interpolation gap semantics and factorization;
- normalized trajectory and direct convergence;
- actual or memory-efficient algorithm equivalence;
- sharp-rate and full-convergence wrappers.

Default exclusions:

- continuous-time ODE or Lyapunov limits;
- informal rate interpretation not needed for the finite theorem;
- diagrams and numerical motivation;
- parametrization equivalences that are not required by the headline Lean
  theorem.

Include excluded material only when the user explicitly selects it as a target
theorem.

## Function-Value Certificate Pattern

Use this pattern for finite-horizon strongly convex method results where the
main output is a function-value upper bound.

Typical source material:

- geometric point or shooting construction;
- algebraic certificate data;
- dual/SOS identity;
- low-rank or memory form of the algorithm;
- function-model interpolation bridge;
- final finite-horizon upper bound for the generated algorithm.

Typical Lean modules:

- basic normalized definitions and finite sums;
- shooting angles, points, symmetries, and certificate existence;
- derived algebraic certificate;
- residuals, edge/Gram identities, displacement, and energy identities;
- low-rank certificate and low-rank algorithm compatibility;
- function model, interpolation feasibility, and convergence;
- complete algorithm theorem and comparator-facing wrappers.

Default exclusions:

- figure-only geometric illustrations;
- lower-bound or tightness discussion unless a formal lower-bound theorem is
  explicitly selected;
- numerical solver history, except as provenance for the certificate data.

## Theorem Surface

Create theorem-facing wrappers early. A good wrapper file should:

- import the internal project root;
- state stable paper-facing theorem names;
- expose only assumptions intended to appear in the final claim;
- call internal lemmas rather than duplicate proof details;
- be suitable for manuscript, ledger, or comparator references.

If the project uses a comparator or independent checker, keep `Solution.lean`
and `Challenge.lean` theorem statements synchronized and keep `config.json`
aligned with the exact theorem names and permitted axioms. Run the comparator
only after `lake build` and static hygiene pass and only after the human
researcher approves the wrapper/config surface. Record the comparator command
and output separately from the build+hygiene evidence.
