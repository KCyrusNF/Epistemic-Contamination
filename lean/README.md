# Epistemic Contamination — Lean Oracles

This directory contains the Lean formalizations for 60 benchmark test cases, with 16 named oracle theorems per case. The project uses **Lean 4.34.0 and Mathlib v4.34.0**.

Each case has a separate oracle source and axiom audit. Build and review cases individually as their test case definitions are developed.

**The formalizations remain provisional.** Semantic validation is still required, and AA-18 and CT-01 have unresolved expected-answer discrepancies described below.

## Directory structure

Paths in this table are relative to `lean/`.

| Path | Purpose |
| --- | --- |
| `lean-toolchain` | Specifies the Lean version. |
| `lakefile.lean` | Configures the package, Mathlib dependency, and oracle library. |
| `lake-manifest.json` | Locks dependency revisions for reproducible setup. |
| `oracle_manifest.json` | Records case paths, theorem names, expected answers, source hashes, and known discrepancies. |
| `oracles/Support.lean` | Defines shared concepts used by the case formalizations. |
| `oracles/<domain>/<case>.lean` | Contains the oracle declarations for one case. |
| `audits/<domain>/<case>.lean` | Prints the axiom dependencies of that case's 16 oracle theorems. |
| `.lake/` | Generated local dependencies and build products. Exclude from version control. |

Test case definitions are stored separately under `test_cases/` at the repository root. Oracle and audit folders use the same domain and case names.

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

## Work on one case

### 1. Build the oracle

From the `lean/` directory, specify the case source explicitly:

```powershell
lake build oracles/boolean_algebra/BA-49.lean
```

Lake builds the selected case and its required dependencies, reusing current build products. Support is handled as a dependency and normally needs no separate build. Use the corresponding domain and filename for another case.

The library configuration selects only `oracles.Support` for a library-wide build. Case modules remain available as explicit build targets. Individual builds can still require substantial work when shared dependencies are missing or outdated.

### 2. Inspect the axiom audit

After the case builds successfully, run its audit:

```powershell
lake env lean audits/boolean_algebra/BA-49.lean
```

The audit uses `#print axioms` to list each oracle theorem's axiom dependencies. Review the output for `sorryAx` and any assumptions outside the project's accepted foundations.

The audit prints information; it does not automatically reject unwanted axioms or export expected-answer values.

## Verification status

Compilation, axiom review, and semantic validation serve different purposes:

| Check | What it establishes |
| --- | --- |
| Lean compilation | Lean accepts the declarations in the selected source. |
| Axiom review | The proof dependencies have been inspected for admitted proofs and unapproved assumptions. |
| Semantic validation | The formal statements faithfully represent the test case definitions and support the recorded expected answers. |

The formalizations require compilation, axiom review, and semantic validation before use as verified benchmark oracles. Successful compilation alone does not establish that a formal statement accurately represents its test case definition or supports the recorded expected answer.

### Unresolved discrepancies

| Case | Turns | Issue |
| --- | --- | --- |
| AA-18 | 5 and 8 | The manifest records `No.`, while the formal oracles establish underdetermination through admissible completions with different membership results. |
| CT-01 | 8 | The manifest records `p`, while the formal oracle establishes underdetermination because the supplied composition table leaves a required composition unspecified. |

**AA-18 and CT-01 are not final.** Review their test case definitions, formal statements, and recorded answers together before using them as validated benchmark cases. Semantic review is also required for the remaining cases.

`Benchmark.Underdetermined valid query` means that two interpretations satisfying `valid` produce different results for `query`. Proving this formal statement and checking that it matches the intended question are separate responsibilities.

## File conventions

- Use UTF-8 text with CRLF line endings.
- Place Lean module documentation in `/-! ... -/` blocks after imports. Include the file path, creation date, author, and purpose or case description.
- In oracle headers, `Source` identifies the corresponding test case definition. In audit headers, it identifies the corresponding oracle source.
- Preserve existing creation dates when editing files.
- Keep `import oracles.Support` in case sources. Each audit imports its corresponding case module.
- Do not add comment headers to JSON manifests or `lean-toolchain`.
