# AutoOPT

This repository contains the user `skill`s and Lean verification code for the following paper: 


> Heechang Kim, Ernest K. Ryu, Shuvomoy Das Gupta, "A Domain-Specific Harness for End-to-End Automation of Optimization Research"

A preprint of the work is available on Optimization Online at the link: [https://optimization-online.org/2026/08/a-domain-specific-harness-for-end-to-end-automation-of-optimization-research/](https://optimization-online.org/2026/08/a-domain-specific-harness-for-end-to-end-automation-of-optimization-research/)



![AutoOPT pipeline with repository grounding, numerical algorithm design, symbolic fitting, Lean verification, and human approval gates](assets/autoopt-pipeline.png)


## Repository contents

### Portable skills

[`Skills/`](Skills/) contains the eight `skill`s used by the `AutoOPT` framework.

The main skills are:

| Skill | Role |
|---|---|
| [`auto-opt`](Skills/auto-opt/SKILL.md) | The main pipeline |
| [`research-repo-manager`](Skills/research-repo-manager/SKILL.md) | Skill for maintaining the research repository  |
| [`bnb-pep-skill`](Skills/bnb-pep-skill/SKILL.md) | Stage1 of `AutoOPT` to run BnB-PEP methodology |
| [`frontier-llm-consult`](Skills/frontier-llm-consult/SKILL.md) | Stage 2 of `AutoOPT` to find an analytical form of the algorithm + convergence proof |
| [`lean-verify`](Skills/lean-verify/SKILL.md) | Stage 3 of `AutoOPT` for Lean formalization |

The main skills use the following additional skills:

| Skill | Role |
|---|---|
| [`chatgpt-pro-handoff`](Skills/chatgpt-pro-handoff/SKILL.md) | Auxiliary skill |
| [`chatgpt-pro-session`](Skills/chatgpt-pro-session/SKILL.md) | Auxiliary skill |
| [`solve-with-highest-reasoning`](Skills/solve-with-highest-reasoning/SKILL.md) | Auxiliary skill |


### Lean verification projects

[`Lean-Related/`](Lean-Related/) contains two projects pinned to Lean 4.32.0
and mathlib 4.32.0:

- [`LemniAcc`](Lean-Related/LemniAcc/README.md) formalizes the discrete and
  continuous lemniscate-acceleration results, including its recurrence,
  Lyapunov, convergence, interpolation, and lemniscatic components.
- [`ITEM-f`](Lean-Related/ITEM-f/README.md) formalizes the analytic ITEM-f
  construction, algorithm, model, Lyapunov argument, and convergence result.

Each project includes its Lean source, pinned Lake environment, theorem-facing
`Challenge.lean` and `Solution.lean` wrappers, and an `AxiomAudit.lean` target.

**Miscellaneous/Self-contained analytical proofs**. [`Selfcontained-PEP-proofs-for-Lemniscate-and-Itemf/`](Selfcontained-PEP-proofs-for-Lemniscate-and-Itemf/) folder located in the `Miscellaneous` folder
contains self-contained PEP-based convergence proofs for  lemniscate acceleration and ITEM-f.  These documents are self-contained: they state the algorithms and rates, construct their parameters,
formulate the corresponding PEPs, and give the analytical dual certificates
and their feasibility proofs. Note that in the paper we provide the slightly more compact proofs based on Lyapunov analysis.

## Installing `AutoOPT`

You can install `AutoOPT` skills in two ways: (i) by installing the skills manually, 
(ii) by installing the `AutoOPT` plugin (new!). 

### Runtime prerequisites

`AutoOPT` requires the following prerequisites. You can either install them before
installing `AutoOPT`, or  install `AutoOPT` 
first, and then from the agent (e.g., `Codex`)  just ask it to install the prerequisites).

The prerequisites are:

* OpenAI Codex (or a similar agent)
* Python 3.10 or newer 
* Julia 1.10 or newer, and Julia packages JuMP, Ipopt, Clarabel, Mosek, Gurobi, KNITRO (note that commerical solvers Mosek, Gurobi, KNITRO are optional)
* Chrome extension Codex (or browser extension the agent in consideration)
* Lean, Lake, the required mathlib project
* Comparator or Landrun tooling 

### Install the AutoOPT skills manually

First, please see the
[Skills/README.md](Skills/README.md) for more details about the skills.

Copy or symlink the required directories from [`Skills/`](Skills/) into a
location scanned by your agent. For Codex, use `$HOME/.agents/skills/` for
user-wide installation or `<repository-root>/.agents/skills/` for
repository-scoped installation; for Claude Code, use `~/.claude/skills/` for
user-wide installation. In Codex CLI or the IDE extension, run `/skills` to
confirm discovery, invoke a skill as `$skill-name`, and restart Codex if an
installed skill does not appear.

### *NEW!* Install the packaged Codex plugin

We have made a plugin for Codex based on the new plugin standard!

The packaged `autoopt` plugin is the portable installation for
the Codex app and CLI. Codex plugin availability does not include the IDE
extension. 

From any directory, run these two
commands to install the plugin directly from this GitHub repository:

```sh
codex plugin marketplace add https://github.com/Shuvomoy/AutoOPT
codex plugin add autoopt@autoopt
```

The first command asks Codex to fetch and register the marketplace stored in
this repository. The second command installs the `autoopt` plugin from that
marketplace.

Verify the installation:

```sh
codex plugin list --marketplace autoopt --json
```

Start a new Codex task so that the installed plugin is loaded, then invoke the
pipeline with:

```text
$autoopt:auto-opt
```

The plugin packages the full AutoOPT skill set, including `bnb-pep-skill`; do
not install `bnb-pep-skill` separately.

## Build the Lean projects

Each project uses its checked-in `lean-toolchain` and `lake-manifest.json`:

```sh
cd Lean-Related/LemniAcc
lake build
```

```sh
cd Lean-Related/ITEM-f
lake build
```




## Reporting issues

Please report any issues via the [Github issue tracker](https://github.com/Shuvomoy/AutoOPT/issues). All types of issues are welcome including bug reports, feature requests, and so on.

## Contact
Please feel free to send an email :email: to [sd158@rice.edu](sd158@rice.edu) regarding any subject including but not limited to comments about this codebase/paper, or just to say hi 😃!
