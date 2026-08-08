# Comparator Platform Routes

Load this reference before preparing, approving, or running Comparator. Select
one supported route and record the route in the closeout evidence.

## Contents

- Common qualification contract
- Route selection
- Linux
- Native macOS
- Windows 11 with WSL2
- Evidence record
- Authoritative sources

## Common qualification contract

Before every replay:

1. complete `lake build`, hygiene, and any required axiom audit;
2. pin compatible Lean, Comparator, and `lean4export` revisions;
3. inspect `Challenge.lean`, `Solution.lean`, and `config.json`;
4. show the human researcher the wrapper paths and hashes, theorem names,
   permitted axioms, platform route, sandbox backend, tool paths and revisions,
   and exact command;
5. wait for explicit approval;
6. preserve the exact command, exit status, complete relevant output, and tool
   metadata.

A replay qualifies only when the approved Comparator command exits
successfully and reports its final success verdict. A failed, incomplete, or
stopped replay does not qualify.

## Route selection

| Host | Execution environment | Required Landrun route | Qualifies after success |
|:--|:--|:--|:--|
| Linux | Linux | Real Landrun | Yes |
| macOS | Native macOS | Official upstream `scripts/fake-landrun.sh`, unsandboxed | Yes |
| Windows 11 | WSL2 Linux distribution | Real Landrun | Yes |

Native Windows, WSL1, an unofficial no-op shim, or a platform whose required
preflight fails is not a qualifying route. Record the blocker and keep the
evidence label at `Lean build+hygiene verified`.

## Linux

Use real Landrun and follow Comparator's current ordinary Linux instructions,
including any required outer `systemd-run` protection. Record the Linux kernel,
Landrun revision and binary hash, Comparator revision, `lean4export` revision,
and sandbox-engagement evidence.

Do not silently replace real Landrun with a shim. If Landrun or the required
systemd protection is unavailable, record the blocker rather than weakening
the command.

## Native macOS

Use the official `scripts/fake-landrun.sh` from a recorded upstream Comparator
checkout. Set `COMPARATOR_LANDRUN` to that script and
`COMPARATOR_LEAN4EXPORT` to the compatible exporter. Do not substitute a
homemade or unidentified no-op wrapper.

The approval packet must state that:

- the official shim ignores Landrun's isolation flags;
- Challenge and Solution build/export subprocesses execute unsandboxed;
- the replay makes no hostile-code isolation claim;
- successful replay nevertheless qualifies for
  `Lean+comparator verified` under this skill's evidence policy.

Record the macOS version and architecture, Comparator commit, shim path and
SHA256, `lean4export` revision and SHA256, Lean toolchain, exact environment
variables, command, exit status, and Comparator output.

A representative command shape is:

```bash
COMPARATOR_LANDRUN=/absolute/path/to/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/absolute/path/to/lean4export \
lake env /absolute/path/to/comparator config.json
```

Use the project's pinned Lean/Lake launcher around this command when required.
The exact command remains human-gated.

## Windows 11 with WSL2

Run the complete Comparator workflow inside a WSL2 Linux distribution. Do not
run Comparator natively on Windows and do not use `fake-landrun.sh`.

Before presenting the Comparator command for approval:

1. confirm from Windows that the selected distribution reports WSL version 2;
2. record the WSL version, distribution, Linux kernel, and architecture;
3. confirm systemd is running inside the distribution, enabling it first when
   the distribution does not enable it by default;
4. confirm the kernel has Landlock enabled;
5. identify and hash the real Landrun binary and record its upstream revision;
6. run the selected Landrun release's maintained test or a denial probe that
   demonstrates an attempted write outside the allowed paths is rejected;
7. record the successful sandbox-engagement evidence.

After this preflight, follow Comparator's ordinary Linux instructions verbatim
inside WSL2, including the real Landrun binary and any required outer
`systemd-run` protection. Run from the WSL2 Linux environment, using Linux
paths and Linux executables. A successful replay qualifies for
`Lean+comparator verified`.

If WSL2, systemd, Landlock, real Landrun, or the sandbox probe is unavailable,
record the blocker. Do not fall back to WSL1, native Windows, or a fake shim.

## Evidence record

Record at least:

- host operating system;
- execution operating system or WSL2 distribution;
- kernel and architecture;
- sandbox backend: `real-landrun` or
  `official-fake-landrun-unsandboxed`;
- sandbox-engagement result, or explicit `not applicable` for native macOS;
- Lean, Lake, Comparator, `lean4export`, Landrun or shim revisions and hashes;
- wrapper and configuration paths and hashes;
- theorem names and permitted axioms;
- exact approved command and environment variables;
- start and end times, exit status, and final Comparator verdict;
- output artifact paths and any warnings or limitations.

## Authoritative sources

- [Comparator documentation](https://github.com/leanprover/comparator)
- [Official Comparator fake-Landrun shim](https://github.com/leanprover/comparator/blob/master/scripts/fake-landrun.sh)
- [Landrun requirements and compatibility](https://github.com/Zouuup/landrun#requirements)
- [Install WSL](https://learn.microsoft.com/en-us/windows/wsl/install)
- [Use systemd with WSL](https://learn.microsoft.com/en-us/windows/wsl/systemd)
- [Microsoft WSL2 kernel configuration](https://github.com/microsoft/WSL2-Linux-Kernel/blob/linux-msft-wsl-6.6.y/arch/x86/configs/config-wsl)
