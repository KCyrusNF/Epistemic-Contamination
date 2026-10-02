# Epistemic Contamination — evaluation pipeline & assistant GUI

Two programs over one pair of JSON schemas:

- **Automated testing program (bench-runner)** — reads test cases from
  `test_cases/`, replays each one as a sixteen-turn conversation against an LLM,
  and writes an independent run log under
  `results/{ModelName}-run-{N}/{domain}/{CaseID}-{Model}-R{N}.json`.
- **Assistant GUI (bench-assistant)** — hierarchical inspector
  (`Model → Domain → Case → Run`) with the ingested prompt and Lean oracle on the
  left, the raw completion (and collapsible thinking) on the right.

There is no runtime grading. `evaluation.is_correct`, `failure_mode` and
`comments` are written as `null` and reserved for post-hoc human audit. Decoding
is greedy (`temperature = 0.0`); thinking models use `max_tokens = 2048`.

An interrupted session can be continued with `--resume`: completed turns are
rebuilt from the append-only `.journals/` file and transmission restarts at the
next turn.

The experiment behind it: establish a rule, replace it with a modified one, and see
whether the model reasons from what it was actually given or leaks unstated
standard properties back in. That demands long sessions with exact cumulative
context, so every turn transmits the entire history, each case runs in isolation,
and requests are throttled per provider.

```
epicon/       the package          templates/   the two canonical schemas
test_cases/   test case configs    manifests/   batch definitions
results/      session logs         lean/        formal artifacts (oracle side)
.journals/    crash-recovery       tests/       offline test suite
docs/         design reference
```

## Install

Python 3.10+.

```powershell
pip install -r requirements.txt
python -m epicon init          # create the data directories
```

## Run the tests

Fully offline — no network, no SDKs, no keyring. A stub client records what would
have been transmitted, which is how cumulative context, session isolation,
crash recovery, the results hierarchy and the schema round-trip are verified.

```powershell
python -m unittest discover -s tests -t . -v
```

45 tests, roughly a second. Run this first: if the dataclasses drift from
`templates/*.json`, the round-trip tests fail before anything reaches an API.

## Configure API keys

Keys live in the OS keyring (Windows Credential Manager, macOS Keychain, Secret
Service). There is no `.env` support by design — `epicon.credentials` raises if it
finds one in the project root.

```powershell
python -m epicon creds set anthropic     # then type the key; it is not echoed
python -m epicon creds set openai
python -m epicon creds list               # which providers have keys
python -m epicon providers                # routing + key status
```

Supported providers: `anthropic`, `openai`, `google`, `deepseek`, `zai`. Claude
goes through the native `anthropic` SDK; the rest use the `openai` SDK against
their OpenAI-compatible base URLs.

The prompt needs a real console. Where there is none it exits with code 2 rather
than blocking, so for scripts and CI pipe the key in instead:

```powershell
type key.txt | python -m epicon creds set anthropic --stdin
```

## Run a live test

A test case carries no model, so the model comes from a manifest or from flags.

```powershell
python -m epicon validate                          # parse every case first
python -m epicon run -m example_sweep --dry-run
python -m epicon run -m example_sweep
python -m epicon run -m example_sweep --resume          # continue an interrupted journal

# or without a manifest:
python -m epicon run test_cases --provider anthropic --model Claude-4.6-Opus `
    --run-index 1 --workers 3
```

Start with `--dry-run`: it resolves credentials-free and prints the destination
path plus the `model_metadata` that would be recorded.

Useful flags: `--only CASE_ID …`, `--run-index`, `--resume`, `--rpm`,
`--concurrency`, `--turn-delay`, `--results-dir`, `--stop-on-error`, `--thinking`,
`--export`, `-v`. Ctrl-C stops queued work while in-flight sessions finish and
are written.

## Launch the GUI

```powershell
python -m epicon gui
```

The sidebar is `Model → Domain → Case ID → Run Index`. The inspector is split:
prompt, Lean theorem reference and Lean ground truth on the left; raw completion,
telemetry and a collapsible thinking pane on the right. Markdown and LaTeX render
via MathJax when Qt WebEngine is available.

Export from the GUI, or on the command line:

```powershell
python -m epicon export -o results.xlsx
```

One worksheet per `(case_id, model)` group, turns 1–16 down the page, runs 1–5
side-by-side against the Lean ground truth, with empty bordered cells for the
manual audit.

## Further reading

[`docs/reference.md`](docs/reference.md) covers the schemas, isolation and retry
guarantees, provider routing, and the module layout.
