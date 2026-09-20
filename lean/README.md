# Epistemic Contamination — Lean Oracles

This directory contains the Lean formalizations for 60 benchmark test cases, with 16 named oracle theorems per case. The project uses **Lean 4.34.0 and Mathlib v4.34.0**.

Each case has a separate oracle source and axiom audit. Build and review cases individually as their test case definitions are developed.

**All 60 oracle files compile successfully, and their axiom audits are complete.** The formalizations remain provisional pending manual semantic review.

## Directory structure

Paths in this table are relative to `lean/`.

| Path | Purpose |
| --- | --- |
| `lean-toolchain` | Specifies the Lean version. |
| `lakefile.lean` | Configures the package, Mathlib dependency, and oracle library. |
| `lake-manifest.json` | Locks dependency revisions for reproducible setup. |
| `oracles.lean` | Root module for the oracle library; imports only `oracles.Support`. |
| `oracles/Support.lean` | Defines shared concepts used by the case formalizations. |
| `oracles/<domain>/<case>.lean` | Contains the oracle declarations for one case. |
| `audits/<domain>/<case>.lean` | Prints the axiom dependencies of that case's 16 oracle theorems. |
| `.lake/` | Generated local dependencies and build products. Exclude from version control. |

Test case definitions are stored separately under `test_cases/` at the repository root. Oracle and audit folders use the same domain and case names.

Case paths and oracle metadata are documented in [manifests](../manifests/README.md).

## Setup

Open PowerShell in the repository's `lean/` directory. Check the selected compiler:

```powershell
lean --version
```

The version should match `lean-toolchain`. For a new checkout, retrieve available compiled Mathlib dependencies:

```powershell
lake exe cache get
```

Keep `.lake/` locally so Lake can reuse downloaded dependencies and build products. Exclude it from Git; keep `lake-manifest.json` in version control. Cache retrieval is a setup or recovery step, not something to repeat before every case build.

## Build configuration

The `Oracles` library in `lakefile.lean` uses the `oracles` module root:

```lean
lean_lib Oracles where
  roots := #[`oracles]
  globs := #[.one `oracles]
```

The corresponding root file, `oracles.lean`, imports only the shared support module:

```lean
import oracles.Support
```

`roots` makes modules under `oracles` available to Lake. The single-module `globs` entry selects the root for library builds, which also build its imports. Keep case and audit imports out of this root file so a library build does not select every case. These settings follow [Lake's library configuration](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

The library has no `@[default_target]` annotation. Use an explicit case target for normal work. To build only the root and its required dependencies, use `lake build Oracles`.

## Work on one case

### 1. Build the oracle

From the `lean/` directory, select the case by its module name:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake build '+oracles.boolean_algebra.«BA-49»'
```

Lake builds the selected case and its required dependencies, reusing current build products. Support is handled as a dependency and normally needs no separate build. Use the corresponding domain and case ID for another case. The `+` selects a module target; `«BA-49»` quotes the hyphenated Lean name, and the outer single quotes preserve the argument in PowerShell.

The thread setting applies to the current PowerShell session and inherited Lean processes. It is not a hard limit on total CPU or memory use. Individual builds can still require substantial work when shared dependencies are missing or outdated.

### 2. Inspect the axiom audit

After the case builds successfully, run its audit:

```powershell
lake env lean audits/boolean_algebra/BA-49.lean
```

The audit uses `#print axioms` to list each oracle theorem's axiom dependencies. Review the output for `sorryAx` and any assumptions outside the project's accepted foundations.

The audit prints information; it does not automatically reject unwanted axioms or export expected-answer values.

## Verification status

Compilation and axiom audits are complete for all 60 oracle files. The audits report only the accepted axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or unapproved axiom dependencies.

| Check | Status | Scope | What it establishes |
| --- | --- | --- | --- |
| Lean compilation | Complete | All 60 oracle source files and their required dependencies. | Lean accepts the declarations in the selected source. |
| Axiom review | Complete | All 960 named oracle theorems across the 60 cases. | The proof dependencies have been inspected for admitted proofs and unapproved assumptions. |
| Manual semantic review | Pending | Each oracle statement, its corresponding test case prompt, and the recorded expected answer. | The formal statements faithfully represent the test case definitions and support the recorded expected answers. |

Only manual semantic review remains before the formalizations can be accepted as verified benchmark oracles. Successful compilation and axiom audits do not by themselves establish semantic correspondence with the test case definitions.

`Benchmark.Underdetermined valid query` means that two interpretations satisfying `valid` produce different results for `query`. Proving this formal statement and checking that it matches the intended question are separate responsibilities.

## File conventions

- Use UTF-8 text with CRLF line endings.
- Place Lean module documentation in `/-! ... -/` blocks after imports. Include the file path, creation date, author, and purpose or case description.
- In oracle headers, `Source` identifies the corresponding test case definition. In audit headers, it identifies the corresponding oracle source.
- Preserve existing creation dates when editing files.
- Keep `import oracles.Support` in case sources. Each audit imports its corresponding case module.
- Do not add comment headers to JSON manifests or `lean-toolchain`.
