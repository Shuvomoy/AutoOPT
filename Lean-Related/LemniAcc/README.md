# LemniAcc  Lean verification

This directory contains the build-only LemniAcc formalization, pinned to Lean
4.32.0 and mathlib 4.32.0. It covers the discrete and continuous
lemniscate-acceleration results for the current manuscript, not the legacy
Lean 4.28 formalization.

## Build

From the repository root, run:

```sh
cd Lean-Related/LemniAcc
lake build
```

The checked-in `lean-toolchain` and `lake-manifest.json` pin Lean and the
dependency closure. The default build compiles the `LemniAcc`, `Challenge`,
`Solution`, and `AxiomAudit` targets.

This public directory does not include project-local validation scripts or
recorded build, hygiene, axiom-audit, or Comparator artifacts. A fresh
`lake build` checks the distributed Lean sources and builds the `AxiomAudit`
target, but it does not reproduce the omitted hygiene or Comparator checks.
