---
name: chatgpt-pro-session
description: Persistent ChatGPT Pro workflow for starting, claiming, and continuing one reusable ChatGPT Web conversation with an initial project context bundle, monitored by waiting in internal chunks of at most 60 seconds while inspecting the ChatGPT UI only roughly every 5 minutes after reasoning or generation visibly starts unless an error or ambiguous state is suspected. Use when the user asks Codex to use ChatGPT Pro Session, keep working in the same ChatGPT Pro chat, reuse an already uploaded context bundle, claim an existing ChatGPT conversation URL as reusable context, request follow-up Pro analysis or diffs in the same session, or avoid repeatedly reuploading the same workspace context. Explicit invocation is standing consent to upload the initial selected context bundle to ChatGPT Web using GPT-5.6 Sol with Intelligence set to Pro; later implementation of Pro recommendations remains opt-in.
---

# ChatGPT Pro Session

## Purpose

Use this skill to maintain a reusable Codex-to-ChatGPT Pro consultation session. The first turn packages and uploads selected project context to a ChatGPT Web conversation; later turns reopen the same conversation URL and ask follow-up questions without reuploading the original bundle.

This skill is relay-only by default. Do not implement ChatGPT Pro recommendations unless the user separately asks Codex to implement them after the Pro answer or artifact has been imported and locally validated.

## Required Tools

Use the Chrome plugin for ChatGPT Web submission and monitoring. Before opening `chatgpt.com`, read and follow the Chrome skill if it is available, and use the Chrome extension browser backend, specifically `agent.browsers.get("extension")`.

Do not use the Codex in-app Browser, native ChatGPT app, AppleScript, Computer Use, shell browser automation, Playwright CLI, or undocumented ChatGPT/session APIs for submission, upload, monitoring, or response capture. If Chrome plugin access, the Codex Chrome Extension connection, ChatGPT login, upload, model selection, or Intelligence selection is blocked or ambiguous, pause for user takeover. Do not submit with a fallback model, Intelligence level, or browser path.

## Session State

Store session metadata in the handoff directory:

```text
.chatgpt_handoffs/<timestamp>/
  session.json
  manifest.json
  prompt.md
  context-<timestamp>.zip
  response.md
  turns/
    001/
      prompt.md
      raw_response.md
      response.md
      response_import.json
      artifacts/
```

Use `scripts/session_state.py` to create and update `session.json` and `.chatgpt_handoffs/session-index.json`. The script only manages metadata and directories; it does not upload files, drive Chrome, or validate artifact semantics.

Common commands:

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-session/scripts/session_state.py init \
  --workspace "$PWD" \
  --handoff-dir .chatgpt_handoffs/<timestamp> \
  --chat-url "https://chatgpt.com/c/..." \
  --context-zip .chatgpt_handoffs/<timestamp>/context-<timestamp>.zip \
  --manifest .chatgpt_handoffs/<timestamp>/manifest.json \
  --prompt-file .chatgpt_handoffs/<timestamp>/prompt.md
```

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-session/scripts/session_state.py claim \
  --workspace "$PWD" \
  --chat-url "https://chatgpt.com/c/..." \
  --handoff-dir .chatgpt_handoffs/<timestamp-or-claimed-id>
```

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-session/scripts/session_state.py new-turn \
  --handoff-dir .chatgpt_handoffs/<timestamp> \
  --kind followup \
  --prompt-file /path/to/followup-prompt.md
```

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-session/scripts/session_state.py complete-turn \
  --handoff-dir .chatgpt_handoffs/<timestamp> \
  --turn-id 001 \
  --raw-response .chatgpt_handoffs/<timestamp>/turns/001/raw_response.md \
  --response .chatgpt_handoffs/<timestamp>/turns/001/response.md
```

## Start A New Session

Use the existing handoff packager:

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-handoff/scripts/chatgpt_handoff.py create \
  --workspace "$PWD" \
  --task "<initial session task>" \
  --requested-model "GPT-5.6 Sol with Intelligence set to Pro"
```

Choose context automatically:

- Use directed context when the user names specific files, directories, modules, errors, or a narrow issue. Pass `--include`, `--exclude`, or `--file-list`.
- Use full-workspace context when the request is broad or no reliable narrower selection is available.
- Keep the script's default exclusions for `.env*`, keys/certificates, `.git`, `.chatgpt_handoffs`, caches, virtual environments, dependency directories, and build outputs.

Inspect `manifest.json` before upload, especially `selection`, `included`, `omitted_by_selection`, `warnings`, and excluded paths. Explicit invocation of this skill is standing consent to upload the initial selected bundle to ChatGPT Web, so do not ask for a separate upload confirmation unless the manifest is empty, plainly wrong, or contains an unexpected sensitive file.

Open a new ChatGPT Web chat through Chrome, select `GPT-5.6 Sol`, set `Intelligence` to `Pro`, and verify both selections. If either control is unavailable, ambiguous, or cannot be selected, pause for user takeover instead of using a fallback. Attach `context-<timestamp>.zip`, paste `prompt.md`, and submit.

After submission, save the conversation URL with `session_state.py init`. If the ChatGPT response is also part of the requested work, monitor it using the cadence below and import it as described below.

## Continue A Session

When the user asks to continue a Pro session, prefer the active or latest session recorded in `.chatgpt_handoffs/session-index.json`. If the user gives a specific handoff directory or ChatGPT URL, use that instead.

Reopen the saved ChatGPT conversation URL in Chrome. Select `GPT-5.6 Sol` and set `Intelligence` to `Pro` if either visible setting is wrong, then verify both selections. If either control is unavailable, ambiguous, or cannot be selected, pause for user takeover instead of using a fallback.

Do not reupload the original context bundle. Write the follow-up prompt so ChatGPT Pro knows it should use the context already available in the conversation. Save the prompt with `session_state.py new-turn`, submit it in the existing chat, monitor it using the cadence below, then save/import the response under that turn directory.

For follow-up diffs or edits against already uploaded files, verify context freshness when possible before submitting: compare the current local file hash, size, or timestamp against `manifest.json` entries from the active context snapshot. If a relevant file has materially changed, refresh context or clearly state in the prompt that Pro is working from the older uploaded version. Refresh context only if the user explicitly asks to upload more files, the task depends on files not in the original bundle, or the workspace has materially changed. Record refreshes with `session_state.py add-context`.

## Monitoring Cadence

After reasoning or generation visibly starts, do not perform one long unattended sleep.
Wait in internal chunks of at most 60 seconds, but inspect the ChatGPT UI only
when roughly 5 minutes have elapsed. Repeat that 5-minute observation window
while ChatGPT is still reasoning or generating. Inspect sooner only if an error,
navigation change, lost connection, or ambiguous state is suspected. If the UI
state is ambiguous, logged out, blocked, errored, or no longer clearly using
`GPT-5.6 Sol` with `Intelligence` set to `Pro`, pause for user takeover.

## Claim An Existing Session

When the user gives an existing ChatGPT URL and asks to reuse it, claim it:

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-session/scripts/session_state.py claim \
  --workspace "$PWD" \
  --chat-url "https://chatgpt.com/c/..." \
  --handoff-dir .chatgpt_handoffs/<chosen-session-id>
```

If the user also identifies an existing `.chatgpt_handoffs/<timestamp>` directory, use it. Otherwise create a new claimed session directory. Mark claimed sessions as relying on prior chat context; do not assume the local manifest is complete unless it is present.

## Response Capture And Import

For ordinary prose responses, require the standard markers:

```text
BEGIN_CHATGPT_PRO_HANDOFF_RESPONSE
...
END_CHATGPT_PRO_HANDOFF_RESPONSE
```

### Capture Current Turn

Capture only the latest assistant response for the current turn. Do not count or extract markers from the full page text: older responses and the user's prompt may contain the same marker strings.

When extracting code blocks from ChatGPT Web, preserve rendered line breaks. Prefer the rendered text of the relevant final `<pre>` block, such as `innerText`; avoid relying on `textContent` when ChatGPT renders code with nested spans or `<br>` elements, because it can flatten a unified diff into one line.

Save the full captured response to `turns/<id>/raw_response.md`, then import with the existing handoff importer:

```bash
python3 /Users/shuvo/My\ Drive/GitHub/Shuvos_Skills/chatgpt-pro-handoff/scripts/chatgpt_handoff.py import-response \
  --handoff-dir .chatgpt_handoffs/<timestamp>/turns/<id> \
  --response-file .chatgpt_handoffs/<timestamp>/turns/<id>/raw_response.md
```

If the importer needs the root handoff directory instead of a turn directory for compatibility with a specific workflow, save a copy at the root and document the mapping in `session.json`.

Prefer response-file import over clipboard import. Use `--from-clipboard` only after verifying with a system clipboard check such as `pbpaste` that both response markers are present.

Relay the imported Pro answer faithfully in Codex. Do not summarize, critique, reorder, or implement it unless the user asks for that next.

## Artifact And Diff Requests

For whitespace-sensitive artifacts, especially unified diffs, always request a fenced artifact block from the start. This prevents ChatGPT Web rendering from stripping leading spaces in diff context lines.

Use this structure:

````text
BEGIN_CHATGPT_PRO_HANDOFF_RESPONSE
BEGIN_MAIN_TEX_DIFF
```diff
diff --git a/path/file b/path/file
--- a/path/file
+++ b/path/file
@@ ...
 context line begins with one literal space
+addition
-deletion
```
END_MAIN_TEX_DIFF
END_CHATGPT_PRO_HANDOFF_RESPONSE
````

The `@@ ...` hunk header above is only an example for the prompt. The actual returned artifact must contain real unified hunk headers and complete hunks. If the target path contains spaces, ask Pro to quote the `---` and `+++` file header paths, for example `--- "a/path with spaces/file.md"` and `+++ "b/path with spaces/file.md"`.

After capture, save the raw response, extract the marker-bounded artifact, strip only the outer code fence, and validate locally before reporting it as usable. For a Git patch, confirm all of the following:

- the extracted response has exactly one handoff marker pair and exactly one artifact marker pair;
- the artifact contains exactly the expected target path scope and at least one `diff --git` header;
- the artifact has no placeholder hunk headers such as `@@ ...`;
- the final hunk is visibly complete, with nonempty trailing context when the prompt requested context;
- the patch passes local validation.

Run:

```bash
git apply --check <artifact.diff>
git apply --stat <artifact.diff>
```

If the workspace is not a Git repository, `git apply` can still validate a patch against local files. Use `patch --dry-run` only as a last-resort diagnostic; it may prompt or fail on quoted paths or filenames containing spaces.

Do not apply, merge, or edit local source files unless the user separately asks for implementation.

## Failure Behavior

If a response lacks markers, contains corrupt artifacts, uses the wrong path scope, or fails local validation, save it as an invalid attempt and ask ChatGPT Pro once for a corrected response in the same session. Include the exact local validation error and the smallest necessary corrective instruction.

Record invalid and corrected attempts in session metadata. Use `session_state.py complete-turn --status invalid` or `--status superseded` for the failed turn, attach the invalid artifact with `--artifact`, then create a correction turn. Mark the correction turn `completed` only after capture, import, artifact extraction, and local validation have all passed.

If the corrected response still fails, stop and report the blocker with artifact paths.

If Chrome or ChatGPT Web state is ambiguous, stop and ask for user takeover rather than switching tools or models.
