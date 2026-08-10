---
name: bnb-pep-skill
description: Formalize, derive, and locally implement Branch-and-Bound Performance Estimation Programming (BnB-PEP) instances from math or plain English. Use when a researcher or agent needs worst-case performance analysis or stepsize/parameter optimization of fixed-step first-order methods via performance estimation problems (PEP), translating a function class, finite interpolation conditions, method update equations, performance measure, and initial condition into the Generalized BnB-PEP derivation and Julia/JuMP models for the primal SDP, dual SDP, and Stage 1/2 local nonlinear workflows. Covers smooth (strongly) convex, smooth nonconvex, weakly convex, Lipschitz, indicator/support-function, and composite/proximal OptISTA-style setups. Also covers explicitly requested BnB-PEP Stage 3 spatial branch-and-bound planning and static linting, while default generation remains Stage 1/2 only.
---

# BnB-PEP Skill

## Core Rule

Use the Generalized BnB-PEP methodology. Do not silently guess mathematical assumptions. Do not generate Julia until the user explicitly approves the Markdown derivation. Default workflows are Stage 1/2 only: do not implement, suggest, or run BnB-PEP Stage 3, spatial branch-and-bound, global nonconvex optimization, or any Gurobi global-solver path unless the user explicitly asks for BnB-PEP Stage 3 in those terms.

## Source Grounding

Load these references only as needed:

- `references/onboarding.md`: first-run guide for new users, Julia environment setup, checker commands, and starter prompts.
- `references/bnb-pep-methodology.md`: primary standalone construction of the BnB-PEP methodology, including primal SDP, dual SDP, Cholesky PSD conversion, Stage 1/2 workflow, and a canonical example.
- `references/formalization-schema.md`: checklist for turning user input into a precise BnB-PEP instance.
- `references/interpolation-conditions.md`: compact lookup table for retained function-class conditions.
- `references/composite-primitives.md`: package-neutral rules for finite or signed sums of component functions.
- `references/derivation-template.md`: required Markdown derivation structure.
- `references/julia-implementation-guide.md`: Julia generation style and Stage 1/2 modeling constraints.
- `references/smoke-tests.md`: small `N = 1,2,3,4,5` smoke-test and static-lint guidance.
- `references/supported-setups.md`: portable map of supported setup families, citation hints, solver expectations, and controlled self-extension rules.
- `references/stage3-global-optimization.md`: explicitly opt-in BnB-PEP Stage 3 spatial branch-and-bound protocol, default `N = 1` horizon, Gurobi/global-solver boundary, and solver-evidence checklist.

Use `references/supported-setups.md` to decide whether a supplied problem matches a currently supported setup family. This skill is designed to be copied as a standalone folder; do not rely on repository-local papers, logs, manuscripts, or source trees during ordinary skill use.

## Self-Extension Rule

Extend this skill only when the user explicitly supplies a new mathematical interpolation condition, oracle condition, or primitive-step definition. Do not invent missing conditions, do not silently generalize from a single supplied condition to a broader function class, and do not present an extension as established unless its status is explicit.

- For a new interpolation or oracle condition, update `references/interpolation-conditions.md` only after checking variables, index ranges, constants, class assumptions, scalar/vector/semidefinite form, necessity/sufficiency/exactness status, dual multipliers, and source or proof provenance.
- For a new primitive step, update the minimal retained reference file only after formalizing the graph relation, introduced samples, auxiliary variables, scalar/vector constraints, dual multipliers, and whether the relation is exact or a relaxation.
- If a user-supplied condition introduces an LMI block \(M_r(G,q;\theta)\preceq0\), record the PSD multiplier \(Y_r\succeq0\), the dual contribution \(\langle Y_r,M_r(G,q;\theta)\rangle\), and either the Stage 2 factorization \(Y_r=Q_rQ_r^\top\) or an explicit fixed-SDP-only boundary until a Stage 2 representation is supplied.
- If the new setup needs nontrivial implementation guidance, add a concise entry to `references/julia-implementation-guide.md` that maps the new variables and constraints to JuMP syntax without changing the Stage 1/2 boundary.
- Label every new entry with one provenance label: `user-supplied`, `literature-supported`, `proved in-session`, or `conjectural/needs check`.
- Ask for targeted clarification when any required mathematical object is missing. If the user asks for code before the new condition is vetted, stop at a formalization checklist.

## Workflow

1. **Handle first-run onboarding when needed.**
   - If the user is new to the skill, asks how to start, asks how to install or check Julia packages, asks whether their environment is ready, or asks for a first workflow, load `references/onboarding.md` before mathematical derivation.
   - Use onboarding to explain required packages, recommended solvers, checker commands, and starter prompts.
   - Do not install packages unless the user explicitly asks; report exact missing hard requirements before smoke tests.

2. **Formalize the instance.**
   - Read the user's math or plain-English description.
   - Fill the schema in `references/formalization-schema.md`.
   - Identify the function class `\mathcal{F}`, interpolation inequalities, index sets, FSFOM update equations and parameters, performance measure `\mathcal{E}`, initial condition `\mathcal{C}`, constants, dimension assumptions, normalization choices, and iteration budget `N`.
   - If the user names a retained function class but does not provide the finite interpolation conditions, load `references/interpolation-conditions.md` and extract the relevant constraints.
   - Treat any future rows labeled "necessary condition" as necessary constraints only; do not call them exact interpolation conditions. For worst-case maximization, state that they define a relaxed upper-bound model for the original class unless a separate exactness theorem is supplied.
   - If the retained weakly convex bounded-subgradient row is used, include the auxiliary \(C_{j,i}\) witnesses and the required subgradient-bound constraints.
   - If the instance involves a finite or signed sum of functions, a composite or difference-of-convex stationary point, an exact Euclidean proximal map for a proper closed convex function, or an OptISTA-style double-function composite/proximal FSFOM, load `references/composite-primitives.md`.
   - If the task asks what setup families are currently supported, or if the user-provided setup may require a new condition or primitive, load `references/supported-setups.md`.
   - Ask targeted follow-up questions whenever any mathematical object is ambiguous or missing.

3. **Handle explicit extensions before deriving.**
   - If the supplied instance is not covered by the current interpolation, oracle, composite, or primitive references, ask the user for the missing mathematical condition or primitive definition.
   - When the user supplies the missing material, apply the self-extension rule, record the required provenance label, and update the minimal reference file needed.
   - Re-check the formalized instance after the extension. Continue only when another researcher could write every constraint without guessing.

4. **Generate a Markdown derivation.**
   - Use `references/bnb-pep-methodology.md` for the mathematical construction and `references/derivation-template.md` for the required derivation structure.
   - Derive the outer problem, inner worst-case problem, infinite-dimensional formulation, interpolation reduction, finite-dimensional maximization, Gramian SDP, dual SDP, strong-duality statement, and local Stage 1/2 design problem.
   - Include the certificate status of every retained condition: exact interpolation, necessary-only relaxation, sufficient-only restriction, or user-supplied status.
   - When replacing `Z \succeq 0`, cite Lemma `Lem:quadratic-characterization-psd-1`: use `Z = P P^\top` with `P` lower triangular and nonnegative diagonal.
   - For cubic or trilinear expressions, either model the direct local nonlinear program with a compatible local solver or introduce auxiliary variables to obtain a quadratic/bilinear QCQP formulation. Document the choice.
   - End with a derivation-to-Julia mapping checklist.

5. **Stop for approval.**
   - Ask the user to review the Markdown derivation.
   - If corrections are requested, update the derivation and ask again.
   - Proceed to Julia only after explicit approval.

6. **Generate Julia after approval.**
   - Follow `references/julia-implementation-guide.md`.
   - Include a data generator, primal SDP for fixed parameters, dual SDP for fixed parameters, and a Stage 2 local nonlinear solve.
   - Implement only Stage 1 and Stage 2 of the Generalized BnB-PEP Algorithm: solve a convex dual SDP for a feasible point, then warm-start a local nonlinear solve.
   - Prefer Mosek/MosekTools for SDPs and KNITRO for local nonlinear solves when installed, but generated workflows must remain valid with the required open fallback stack Clarabel and Ipopt.

7. **Run or describe smoke tests.**
   - Use `N = 1,2,3,4,5`.
   - Check primal SDP, dual SDP, and local Stage 1/2 path.
   - Run `scripts/check_julia_environment.jl` to report required fallback packages and recommended solver availability.
   - Run `scripts/validate_generated_instance.py` as static lint on generated Markdown/Julia artifacts before claiming the skill output is ready.

8. **Handle BnB-PEP Stage 3 only on explicit request.**
   - Trigger this path only when the user explicitly asks for "BnB-PEP Stage 3", "spatial branch-and-bound", or "global nonconvex search" for a BnB-PEP-QCQP.
   - Load `references/stage3-global-optimization.md`.
   - Keep the Stage 1/2 smoke/default horizon policy `N = 1,2,3,4,5` separate from the Stage 3 default horizon. Stage 3 defaults to `N = 1`; larger Stage 3 horizons require an explicit user override.
   - Treat Stage 3 output as solver evidence only. Do not call it a theorem, formal proof, or Lean verification.
   - Do not run Stage 3 unless the user separately approves a solver execution with solver, time limit, tolerance, logging, and artifact locations fixed.

## Hard Constraints

- In default Stage 1/2 workflows, do not implement or invoke `solution_type = :find_globally_optimal`.
- In default Stage 1/2 workflows, do not require Gurobi.
- Do not run large instances or BnB-PEP Stage 3 without explicit solver-execution approval.
- If BnB-PEP Stage 3 is explicitly requested, keep it separate from the AutoOPT pipeline's Stage 3 Lean formalization.
- Do not weaken the approval gate between derivation and Julia generation.
- Keep claims traceable to the supplied instance, `references/bnb-pep-methodology.md`, retained reference files, generated computations, or entries labeled `user-supplied`, `literature-supported`, `proved in-session`, or `conjectural/needs check`.
