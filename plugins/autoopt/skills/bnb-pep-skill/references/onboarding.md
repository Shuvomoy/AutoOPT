# First-Run Onboarding

Use this guide when the user is new to the skill, asks how to start, asks
whether their Julia environment is ready, or wants a first BnB-PEP workflow.

## What This Skill Does

The skill helps an optimization researcher move from a problem statement to:

- a precise BnB-PEP formalization;
- a Markdown derivation of the primal SDP, dual SDP, and Stage 1/2 local nonlinear model;
- Julia code using JuMP for fixed-parameter primal/dual SDPs and Stage 1/2
  local computation;
- small smoke tests for horizons `N = 1,2,3,4,5`.

The skill does not implement Stage 3, global spatial branch-and-bound, Gurobi
global-solver paths, or global-optimality certification by default. If the user
explicitly asks for BnB-PEP Stage 3, load
`references/stage3-global-optimization.md`; that opt-in path defaults to
`N = 1` and treats outputs as solver evidence only. The skill also does not
invent missing interpolation conditions or primitive graph relations.

## How To Invoke The Skill

### Installed Through The AutoOPT Plugin

When AutoOPT is installed as an Agent Plugin, `bnb-pep-skill` is already bundled. Do not copy or symlink a separate standalone skill folder. Start the agent in the working project, confirm that AutoOPT is installed, and invoke the plugin-qualified BnB-PEP skill name displayed by the host. When running bundled checks, resolve scripts from the loaded `bnb-pep-skill` directory while preserving the working project's current directory.

Example:

```text
Use the AutoOPT plugin's BnB-PEP skill to onboard me and check whether my Julia environment is ready.
```

```text
Use the AutoOPT plugin's BnB-PEP skill to formalize this fixed-step first-order method as a BnB-PEP instance. Stop after the Markdown derivation until I approve Julia generation.
```

### Alternative Standalone Skill Installation

The instructions below are alternatives for users deploying this skill without the AutoOPT plugin. They are not required for AutoOPT plugin users and are not a claim of AutoOPT Agent Plugin support in those hosts.

For standalone Codex skill discovery, copy or symlink this folder to `$HOME/.agents/skills/bnb-pep-skill` or `<repository-root>/.agents/skills/bnb-pep-skill`, preserve all bundled resources, restart Codex if needed, confirm discovery with `/skills`, and invoke `$bnb-pep-skill`.

For standalone Claude Code skill loading, copy the folder to `~/.claude/skills/bnb-pep-skill` or `<project>/.claude/skills/bnb-pep-skill`, preserve the folder name and resources, and invoke it in plain language or with `/bnb-pep-skill`. This is a standalone skill-loading alternative, not claimed AutoOPT Agent Plugin support for Claude Code.

## Julia Requirements

Julia must be installed before generated BnB-PEP code can be run. The hard
required packages for Stage 1/2 workflows are:

- `JuMP`;
- `OffsetArrays`;
- `Clarabel`;
- `Ipopt`.

Recommended solver packages are:

- `MosekTools` and `Mosek` for SDP models when available;
- `KNITRO` for local nonlinear solves when available.

Recommended packages are accelerators, not hard requirements. Do not require
unrelated Julia packages or any global branch-and-bound solver path for this
default Stage 1/2 check.

Version floors: `JuMP >= 1.15` is required, because generated Stage 2 models
build cubic/trilinear terms through JuMP's nonlinear-expression interface
(ScalarNonlinearFunction), which older JuMP versions do not support. Julia
`>= 1.10` and `Ipopt >= 1.4` are recommended minimums. The environment checker
`scripts/check_julia_environment.jl` verifies the JuMP floor and reports
package versions.

## If Julia Is Not Installed

For macOS and Linux, install Julia by running the following in terminal:

```bash
curl -fsSL https://install.julialang.org | sh
```

For Windows, install Julia by running the following in terminal:

```bash
winget install --name Julia --id 9NJNWW8PVKMN -e -s msstore
```

Once Julia is installed, start Julia from terminal by typing:

```bash
julia
```

and then pressing enter. In the Julia REPL, install the hard required packages
by typing:

```text
] add JuMP OffsetArrays Clarabel Ipopt
```

and then pressing enter.

## First Formalization Prompt

For a first real problem, ask the user for:

- function class and all constants;
- interpolation or oracle conditions if the class is not already supported;
- method update equations and fixed or optimized parameters;
- performance measure;
- initial condition;
- iteration budget `N`;
- whether Julia generation is requested after derivation approval.

Starter prompt:

```text
Use $bnb-pep-skill to formalize the following problem as a BnB-PEP instance.
First check whether the setup is supported. Then produce the Markdown derivation
and stop for my approval before writing Julia.

Function class:
Method:
Performance measure:
Initial condition:
Iteration budget:
Parameters to optimize or keep fixed:
```

## First Smoke-Test Prompt

After the user approves a derivation and generated Julia exists:

```text
Use $bnb-pep-skill to validate the generated derivation and Julia file. Run the
static linter, check my Julia environment if you can resolve the checker script,
and, if the hard packages are available, run smoke tests for N = 1,2,3,4,5.
Report any missing package, solver status, objective values, residuals, and
whether Stage 1/2 validation succeeded.
```

Do not claim computational validation when only static lint or environment
checking was possible.
