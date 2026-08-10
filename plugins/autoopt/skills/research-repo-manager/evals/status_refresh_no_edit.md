# status_refresh_no_edit

## Setup

- Repository has populated `GOALS.md`, `FINDINGS.md`, `NEXTSTEP.md`,
  `SOURCES.md`, and `ResearchLog/`.
- No explicit request to edit files is made.

## Prompt

Use `$research-repo-manager` to summarize the current research state.

## Must Pass

- Produces a chat summary of active goal, reliable claims, evidence, open gaps,
  drift, and one full-workday next session.
- Does not edit planning files.
- Labels conjectural or computational evidence as such.
