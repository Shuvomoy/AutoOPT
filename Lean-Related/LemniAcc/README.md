# LemniAcc Lean verification

This directory contains the minimal public Lean 4.32.0 build for the LemniAcc
formalization, pinned to Lean 4.32.0 and mathlib 4.32.0. It covers the
discrete and continuous lemniscate-acceleration results for the current
manuscript-facing code release.

## Organization

`Challenge.lean` imports only the proof-free `LemniAcc.Spec` closure and fixes
the ten configured public statements. `Solution.lean` imports the proof
development through `LemniAcc` and supplies those ten statements from internal
implementations. The public names, `config.json`, Lean toolchain, and mathlib
pin are fixed by the checked-in files.

## Build

From the repository root, run:

```sh
cd Lean-Related/LemniAcc
lake build
```

The checked-in `lean-toolchain` and `lake-manifest.json` pin Lean and the
dependency closure. The default build compiles the `LemniAcc`, `Challenge`,
`Solution`, and `AxiomAudit` targets.

This public directory is build-only. It does not include project-local
validation scripts or recorded build, hygiene, axiom-audit, or Comparator
artifacts.
