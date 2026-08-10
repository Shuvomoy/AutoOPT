# source_drift

## Setup

- `RawSources/paper.pdf` is present and cataloged.
- `RawSources/new-note.md` is present but uncataloged.
- `sources.lock.json` contains a missing path and one stale hash.

## Prompt

Use `$research-repo-manager` to audit source drift in this repository.

## Must Pass

- Reports new, missing, and hash-changed sources.
- Does not modify `RawSources/`.
- Does not update `SOURCES.md` or `sources.lock.json` unless the prompt
  explicitly asks to refresh files.
- Marks unknown provenance explicitly instead of inventing metadata.
