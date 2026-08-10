---
name: chatgpt-pro-handoff
description: Package a full-workspace or directed file-selection handoff for attended ChatGPT Pro consultation through the Chrome plugin at chatgpt.com using GPT-5.6 Sol with Intelligence set to Pro, monitor by waiting in internal chunks of at most 60 seconds while inspecting the ChatGPT UI only roughly every 5 minutes after reasoning or generation visibly starts unless an error or ambiguous state is suspected, then import the response back into Codex. Use when the user wants Codex to prepare project or task context for ChatGPT's web UI through Chrome, then bring the response back into the local Codex workflow.
---

# ChatGPT Pro Handoff

## Portable Command Paths

Resolve `<chatgpt-pro-handoff-skill-dir>` to the directory containing this loaded `SKILL.md`, then substitute that absolute directory in every helper command below. Preserve the user's current working directory so workspace-relative and artifact-relative operands keep their original meaning.

## Required Browser Backend

This workflow requires the `Chrome:Chrome` skill from
`plugin://chrome@openai-bundled` for the ChatGPT Web submission and monitoring
steps. Before opening `chatgpt.com`, read and follow the Chrome skill. Use the
Chrome plugin browser-client backend, specifically
`agent.browsers.get("extension")`.

Do not use `Browser:browser`, the Codex in-app browser,
`agent.browsers.get("iab")`, the native ChatGPT app, Computer Use, AppleScript,
shell browser automation, Playwright CLI, or any other browser fallback for the
submission and monitoring steps. If the Chrome plugin is unavailable, the Codex
Chrome Extension connection does not work, or only the generic Browser plugin is
available, stop and report that Chrome-backed handoff cannot proceed in this
session.

## Workflow

1. Create the handoff package with `scripts/chatgpt_handoff.py create`.
2. Inspect `manifest.json` before upload, especially `selection`, `included`, `omitted_by_selection`, `warnings`, and excluded paths.
3. Ask the user for action-time confirmation before attaching or sending `context-<timestamp>.zip` to ChatGPT, because upload transmits local files to a third party. State what data will be sent, destination, and why.
4. Verify the Chrome plugin is available and the Codex Chrome Extension connection works, using the checks in the Chrome skill when needed.
5. Use the Chrome plugin to open ChatGPT Web at `chatgpt.com`. Start a new chat, select `GPT-5.6 Sol`, set `Intelligence` to `Pro`, and verify both selections. If either control is unavailable, ambiguous, or cannot be selected, pause for user takeover instead of using a fallback. Paste `prompt.md`, attach `context-<timestamp>.zip`, and submit only after confirmation.
6. After reasoning or generation visibly starts, do not sleep for 5 minutes inside a single tool call. Instead, wait in internal chunks of at most 60 seconds, but inspect the ChatGPT UI only after roughly 5 minutes have elapsed; repeat until the response is complete. Inspect sooner only if an error, navigation change, lost connection, or ambiguous state is suspected.
7. When ChatGPT finishes, extract or save the full marked response to a local text file and run `scripts/chatgpt_handoff.py import-response --handoff-dir <dir> --response-file <file>`. Use `--from-clipboard` only after verifying that the system clipboard contains both stable response markers.
8. Read `response.md` and continue the Codex workflow from the imported response.

Use `GPT-5.6 Sol` with `Intelligence` set to `Pro` for submission. If the ChatGPT UI does not show either control, either label is ambiguous, or either setting cannot be selected, pause for user takeover instead of submitting with a fallback model or Intelligence level.

Do not use the native ChatGPT app for this workflow because the required model and `Intelligence` controls must be selected in ChatGPT Web. Do not solve CAPTCHAs, enter passwords, bypass browser security warnings, scrape private ChatGPT internals, or use undocumented ChatGPT/session APIs. If the Chrome plugin, Codex Chrome Extension connection, ChatGPT login, upload, model selection, or Intelligence selection blocks the flow, pause for user takeover.

## Monitoring After Submission

Once ChatGPT accepts the upload and reasoning or generation visibly starts, do
not wait for 5 minutes inside a single tool call. Wait in internal chunks of at
most 60 seconds, but inspect the ChatGPT UI only when roughly 5 minutes have
elapsed. If ChatGPT is still reasoning or generating, leave the run undisturbed
and repeat the same 5-minute observation window. Inspect sooner only if an
error, navigation change, lost connection, or ambiguous state is suspected. If
the response is complete, import the full response. If the UI state is
ambiguous, logged out, blocked, errored, or no longer clearly using
`GPT-5.6 Sol` with `Intelligence` set to `Pro`, pause for user takeover.

## Response Capture

Prefer response-file import over clipboard import for Chrome handoffs. Chrome's
tab clipboard and the macOS system clipboard may be separate, and ChatGPT's
``Copy response'' button may not populate the system clipboard under extension
automation. After the response is complete, extract the visible response text
bounded by `BEGIN_CHATGPT_PRO_HANDOFF_RESPONSE` and
`END_CHATGPT_PRO_HANDOFF_RESPONSE`, save it to a local text file, and import
with `--response-file`.

The imported `response.md` is marker-bounded Markdown whose internal structure
should be chosen by ChatGPT Pro according to the actual task prompt. Do not
require predetermined section headings unless the prompt explicitly asks for
them. The generated prompt requires the begin and end markers exactly once, each
on its own line, with no response text outside the markers and no placeholder
text inside them.

Use `--from-clipboard` only if a direct system clipboard check, such as
`pbpaste` on macOS, confirms that both response markers are present. Do not
treat `tab.clipboard.readText()` as proof that the system clipboard is ready
for `--from-clipboard`.

## Packaging

Use:

```bash
python3 "<chatgpt-pro-handoff-skill-dir>/scripts/chatgpt_handoff.py" create \
  --workspace "$PWD" \
  --task "Consult on the attached project context and identify the most useful next steps." \
  --requested-model "GPT-5.6 Sol with Intelligence set to Pro"
```

By default, the script packages the whole workspace after safety/build/cache exclusions. For a directed handoff, pass `--include`, `--exclude`, or `--file-list`; directed mode is user-directed and does not infer relevance from the prompt.

The script creates `.chatgpt_handoffs/<timestamp>/` with:

- `prompt.md`: the exact prompt to paste into ChatGPT, including stable response markers, a context-selection summary, prompt-injection resistance guidance for attached files, and instructions to use task-appropriate response organization.
- `context-<timestamp>.zip`: the workspace bundle for upload, omitted when `--dry-run` is used.
- `manifest.json`: selected included files with sizes and SHA-256 hashes, selection criteria, eligible files omitted by directed selection, excluded paths with reasons, and warnings for potentially sensitive included files.

Default exclusions include `.git`, `.chatgpt_handoffs`, caches, virtual environments, build outputs, `.env*`, private key/certificate files, and common local editor/system artifacts. Symlinks are not followed.

Directed examples:

```bash
python3 "<chatgpt-pro-handoff-skill-dir>/scripts/chatgpt_handoff.py" create \
  --workspace "$PWD" \
  --task "Review the selected source and design notes for risks, gaps, and next implementation steps." \
  --include "src/**/*" \
  --include "docs/design*.md" \
  --exclude "src/experiments/**"
```

```bash
python3 "<chatgpt-pro-handoff-skill-dir>/scripts/chatgpt_handoff.py" create \
  --workspace "$PWD" \
  --task "Consult on the files listed in selected-files.txt." \
  --file-list selected-files.txt
```

`--file-list` entries are exact workspace-relative paths, one per line; blank lines and lines starting with `#` are ignored. In directed mode, `manifest.json` records `selection.mode: "directed"`, the criteria used, and `omitted_by_selection`; those omitted files are not uploaded.

`prompt.md` also summarizes the selected context before the handoff task. It
records the selection mode, included file count, included byte count, and, in
directed mode, the include patterns, exclude patterns, file-list entries, and
number of eligible files omitted by selection. In directed mode, the prompt
warns ChatGPT Pro not to treat absence from the archive as evidence that a file,
requirement, data source, configuration, behavior, or implementation does not
exist.

## Importing Responses

Use one of:

```bash
python3 "<chatgpt-pro-handoff-skill-dir>/scripts/chatgpt_handoff.py" import-response \
  --handoff-dir .chatgpt_handoffs/<timestamp> \
  --from-clipboard
```

```bash
python3 "<chatgpt-pro-handoff-skill-dir>/scripts/chatgpt_handoff.py" import-response \
  --handoff-dir .chatgpt_handoffs/<timestamp> \
  --response-file /path/to/chatgpt-output.md
```

The importer writes `raw_response.md` and `response.md`. If ChatGPT returned the requested stable markers, `response.md` contains only the marked content with whatever Markdown structure the task prompt called for; otherwise it contains the full response and records a warning. The importer only extracts markers; it does not validate headings, assumptions, or quality guidance.

## Confirmation Template

Before upload/send, use wording like:

`I am ready to attach and send <context-YYYYMMDD-HHMMSS.zip> to ChatGPT at chatgpt.com in Chrome using GPT-5.6 Sol with Intelligence set to Pro. This will transmit the files listed under included in <manifest.json>; if selection.mode is directed, files under omitted_by_selection are not uploaded. Potentially sensitive included files are flagged in warnings. Please confirm that I should upload and send this bundle.`
