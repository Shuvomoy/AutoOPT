# Reproducibility Protocol

Use this reference when initializing or refreshing `EXPERIMENTS.md`,
`ARTIFACTS.md`, or `REPRODUCIBILITY.md`, or when auditing computational
evidence for optimization, OR, computation, and game-theory projects.

## Experiment Ledger Fields

Record enough information to rerun or falsify each computational claim:

- experiment ID and research question;
- exact command and working directory;
- code commit or snapshot;
- environment file and language versions;
- solver name, version, relevant settings, and redacted license-sensitive data;
- seeds, generated instance parameters, and input paths;
- output paths, figures, tables, logs, and certificates;
- termination status, objective/bound values, gaps, tolerances, and time limit;
- hardware, thread count, and wall-clock time when material;
- status: `reproduced`, `partial`, `failed`, `stale`, or `not attempted`;
- supported claim IDs from `FINDINGS.md`.

## Artifact Map Fields

Map paper-visible outputs and durable computational artifacts to their
dependencies:

- artifact ID and path;
- producing command or notebook/script;
- inputs and source data;
- outputs and downstream paper references;
- supported findings or experiments;
- rerun command and expected regeneration behavior.

## Environment Notes

- For Julia, prefer `julia --project=.` and preserve `Project.toml` and
  `Manifest.toml` when they define the active environment.
- For Python, preserve `pyproject.toml`, `requirements.txt`,
  `environment.yml`, or equivalent environment files.
- For Mathematica notebooks, keep a text-exported `.wl` file or a research-log
  summary when possible.
- Record random seeds and solver thread counts because they can change
  benchmark and branch-and-bound behavior.
