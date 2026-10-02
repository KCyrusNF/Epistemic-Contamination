# Reference

Design and behaviour notes for the evaluation pipeline. Start with the
[README](../README.md) for installation and day-to-day commands; this document
covers the schemas, the execution guarantees, provider routing, grading rules and
the export layout.

## The two schemas

`templates/test_case_template.json` and `templates/run_log_template.json` are the
contract. The dataclasses in `epicon/models.py` mirror them block for block, and
`tests/test_pipeline.py` asserts an exact round-trip against both template files —
parse, re-emit, compare. If the schemas change, that test fails first.

**Test case** (`case_metadata`, `formal_artifacts`, `system_instruction`,
`conversation_framework`). `system_instruction` is turn 0 and becomes the system
prompt; `conversation_framework` turns are sent in ascending `turn_id` order, each
one carrying its `phase`, `turn_type`, `purpose`, `prompt.content_raw`,
`expected_answer` and optional `references`.

A test case names **no model**. Which model answers it belongs to the run, comes
from a manifest or CLI flags, and is recorded in the run log's `model_metadata`.
The same case can therefore be run against every provider without edits.

`formal_artifacts.lean_file` is metadata, not a prompt attachment: prompts are
transmitted exactly as written in `content_raw`, with nothing spliced in. The Lean
file is the oracle side of the case (see `lean/ALG_021.lean`, whose theorem names
line up with `oracle_theorems` and with the graded turns).

**Run log** (`run_metadata`, `model_metadata`, `test_case`, `conversation`,
`evaluation_summary`, `notes`, `researcher_review`). One log per execution, written
atomically to `logs/<case_id>/<run_id>.json`, where `run_id` follows the schema's
`RUN_YYYY_MM_DD_NNNN` form and the sequence number continues from the logs already
on disk.

`model_metadata` records what was **actually transmitted**, not what was asked
for. Anthropic has no `seed`, so `random_seed` is written as `null` there; if a
reasoning model rejects `temperature`, the parameter is dropped and reported as
`null` rather than claimed.

### The one addition: `execution_metadata`

The run log schema has nowhere to put token counts, retry counts or transport
errors. Those go in an additive top-level `execution_metadata` block — per-turn
usage (including Anthropic's `cache_creation_input_tokens` /
`cache_read_input_tokens`), attempts, stop reasons, reasoning traces, the session
status and any error, plus SDK and environment versions.

It is the last key in the document and every other key is exactly as the schema
specifies, so a schema-driven consumer can ignore it. To omit it entirely and emit
a strictly schema-shaped document:

```powershell
python -m epicon run -m example_sweep --schema-only
# or in the manifest: "execution": { "include_execution_metadata": false }
```

## Execution guarantees

| Concern | How it is handled |
| --- | --- |
| Session isolation | One `Conversation` and one client per test case; nothing mutable is shared, so a failed or contaminated session cannot leak into another. |
| Cumulative context | Per turn: append the user prompt, transmit the **whole** history, block for the response, append the reply. `Conversation` refuses to append a prompt while the previous turn is unanswered, so a dropped response can never silently shift alignment. |
| Throttling | A thread pool bounds concurrent sessions; inside it a token bucket plus a semaphore bound requests-per-minute and in-flight requests **per provider**. |
| Retries | Exponential backoff with full jitter on 408/409/425/429/5xx and connection errors, honouring `Retry-After`. Attempt counts land in `execution_metadata`. |
| Always a log | Every execution produces a log, including when setup fails. A failed turn marks the session `partial`, records `finish_reason: "error"`, flags it in `notes.manual_flags`, and marks the remaining turns `not_executed` so `total_turns` stays truthful. |
| Cancellation | Ctrl-C stops queued work; in-flight requests finish and their logs are written. |

## API routing

Two SDKs, chosen per provider by `epicon/providers.py`:

| Provider | SDK | Endpoint |
| --- | --- | --- |
| `anthropic` | `anthropic` | Messages API (native) |
| `openai` | `openai` | `https://api.openai.com/v1` |
| `google` | `openai` | `https://generativelanguage.googleapis.com/v1beta/openai/` |
| `deepseek` | `openai` | `https://api.deepseek.com/v1` |
| `zai` | `openai` | `https://api.z.ai/api/paas/v4` |

Claude uses the native Messages API rather than a compatibility shim so that
`cache_control` breakpoints survive: one on the system instruction, up to two on
the trailing assistant messages, which turns each turn into a cache read of the
previous turn's prefix. The cache counters are recorded per turn.

The OpenAI-compatible client absorbs gateway differences: `max_tokens` vs
`max_completion_tokens`, reasoning models rejecting `temperature`/`top_p`, `top_k`
passed through `extra_body`, and `reasoning_content` vs `reasoning`. A rejected
parameter is detected from the 400 response, dropped, remembered for the session,
and reported as `null` in `model_metadata`.

Self-hosted gateways can be declared in a manifest's `providers` block.

## Grading

`epicon/grading.py` fills `evaluation.is_correct` and `evaluation.failure_mode`.
It is deliberately conservative — it decides only what is mechanically decidable
and leaves everything else `null`, which keeps the turn out of `scored_turns` and
visibly pending review.

| `answer_type` | Rule |
| --- | --- |
| `exact_value` | Decided from the direct answer (first line, `Answer:`-style label stripped, LaTeX delimiters ignored). For a numeric target the *final* number of that line is compared, because an answer concludes with its value: `2 \times 2 = 4` answers 4 even though its operands restate an expected `2`. `4` never matches inside `14`. Only when the direct answer contains no number at all — a model that preambles instead of answering — is the closing line consulted. |
| `undetermined` | Correct only if the answer opens with `cannot be determined`, the exact phrasing the system instruction mandates. |
| `semantic_statement` | Correct on a normalised match or containment; otherwise left unscored rather than guessed. |
| `acknowledgement`, unknown types, no expected value | Unscored. |

Failure modes assigned automatically are mechanical only: `incorrect_value`,
`unwarranted_determination`, `unwarranted_indeterminacy`, `no_response`,
`api_error`, `not_executed`. Epistemic labels such as
`unauthorized_generalization` are a human judgement — add them to `failure_mode`
and `evaluation_summary.failure_modes_observed` during review.

`evaluation_summary` is recomputed on write and guarantees
`correct_turns + incorrect_turns == scored_turns`. It is **not** recomputed on
read, so a reviewer's hand-corrected counts survive a round-trip.

## Rendering in the GUI

Markdown and LaTeX are rendered natively. With Qt WebEngine present the
transcript is an HTML document with MathJax, so the `$$…$$` these prompts mandate
typesets properly; without it a `QTextBrowser` shows the same HTML and LaTeX
degrades to source text. The status bar names the active backend. For offline
MathJax, drop the bundle at `assets/mathjax/tex-mml-chtml.js`.

Display versus inline is decided by position, not by the delimiter. Because the
system instruction requires `$$…$$` around *every* expression, including
mid-sentence ones, treating each as a centred block would break every prompt into
fragments; an expression is centred only when it is alone on its line. The
renderer rewrites all delimiters to `\(…\)` or `\[…\]` and MathJax recognises
only those, so a lone `$` in prose stays a dollar sign.

Shortcuts: `F5` reload, `Ctrl+F` filter, `Alt+↑/↓` previous/next session,
`Ctrl+E` export the current view, `Ctrl+Shift+E` export one session,
`Ctrl+Shift+C` copy the model outputs. The View menu toggles what the transcript
includes.

## Excel export

Four sheets: **Turns** (one row per turn, with generated vs expected output, the
verdict, latency and tokens), **Runs** (one row per session, with the full
`model_metadata` and evaluation summary), **Reviews** (one row per
`researcher_review` entry) and **Summary** (aggregates, including a failure-mode
histogram). Headers are frozen and filterable; every string cell is written as
text, so a model output beginning with `=` stays text instead of becoming a
formula.

## Module layout

| Module | Responsibility |
| --- | --- |
| `models.py` | Both schemas as dataclasses, with lossless parse/emit. |
| `model_spec.py` | `ModelSpec`: the requested model and sampling parameters. |
| `grading.py` | Automatic turn grading and mechanical failure modes. |
| `conversation.py` | Cumulative history with strict turn ordering. |
| `providers.py` | Provider registry: SDK, base URL, quirks, default limits. |
| `credentials.py` | Keyring-backed credentials; no `.env`. |
| `clients/` | `LLMClient` base (retries, timing) + the two SDK implementations. |
| `throttle.py` | Per-provider token bucket and concurrency semaphore. |
| `runner.py` | The batch processor: isolation, throttling, logging. |
| `manifest.py` | Declarative batch definitions. |
| `storage.py` | Discovery, run ids, atomic writes, log/case pairing. |
| `export.py` | Excel export. |
| `cli.py` | Command-line interface. |
| `gui/` | PySide6/PyQt6 assistant. |
