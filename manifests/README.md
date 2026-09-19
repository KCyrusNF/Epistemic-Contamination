# Manifests

This directory contains machine-readable manifests for benchmark file locations and oracle metadata. Both manifests identify cases by `case_id` and use repository-root-relative file paths.

## Contents

| File | Purpose |
| --- | --- |
| `case_paths.json` | Maps each case ID to its test case definition, Lean source, and axiom audit. |
| `oracle_manifest.json` | Records oracle theorem mappings, expected answers, source hashes, and known discrepancies. |

## Case paths format

`case_paths.json` contains `created`, `author`, `case_count`, and a `cases` array. The creation date uses `YYYY-MM-DD`, and `case_count` must equal the number of entries in `cases`. Git tracks revisions to the manifest. Each case entry has these fields:

| Field | Meaning |
| --- | --- |
| `case_id` | Unique benchmark case identifier, such as `BA-49`. |
| `definition` | Path to the test case definition. |
| `lean_source` | Path to the corresponding Lean oracle source. |
| `axiom_audit` | Path to the corresponding Lean axiom audit. |

Example with one case (the full manifest has `case_count: 60`):

```json
{
  "created": "2026-09-18",
  "author": "Koorosh Nobakhtfar",
  "case_count": 1,
  "cases": [
    {
      "case_id": "BA-49",
      "definition": "test_cases/boolean_algebra/BA-49.json",
      "lean_source": "lean/oracles/boolean_algebra/BA-49.lean",
      "axiom_audit": "lean/audits/boolean_algebra/BA-49.lean"
    }
  ]
}
```

The current manifest lists 60 cases across six domains.

## Oracle manifest format

`oracle_manifest.json` contains case and oracle counts, review metadata, known answer discrepancies, and a `cases` array. Each case entry records:

| Field | Meaning |
| --- | --- |
| `case_id` | Case identifier used to match the entry in `case_paths.json`. |
| `case_title` | Descriptive title of the case. |
| `lean_file` | Repository-root-relative path to the Lean oracle source. |
| `oracle_theorems` | Names of the case's oracle theorems. |
| `source_case_sha256` | Recorded hash of the source test case definition. |
| `turns` | Turn IDs, recorded expected answers, and prompt hashes. |

The manifest covers 60 cases and 960 oracle theorems. Its `lean_file` value must match the corresponding `lean_source` value in `case_paths.json`, for example `lean/oracles/boolean_algebra/BA-49.lean`.

Expected answers and hashes are recorded metadata, not proof of correctness. Hashes must be checked against the intended source version, and known discrepancies must be resolved through semantic review.

## Path conventions

- Resolve every path relative to the repository root, not this directory or the terminal's current working directory.
- Use forward slashes, including on Windows.
- Do not include a leading slash, drive letter, or parent-directory traversal (`..`).
- Keep case IDs unique and entries sorted by case ID.
- Store source-file paths only. Build artifacts and experimental run logs are not entries in these manifests.
- Save text files as UTF-8 with CRLF line endings.

For example, `test_cases/boolean_algebra/BA-49.json` identifies that file beneath the repository root. A script reading `manifests/case_paths.json` can resolve it against the parent of the `manifests` directory.

## Maintenance and use

When adding, renaming, moving, or removing a case, update the affected entries in both manifests and keep their case counts consistent with their contents. Check that the case IDs agree, the three paths in `case_paths.json` identify the intended files, and `oracle_manifest.json` records the same Lean source path.

When a test case definition or formalization changes, review the corresponding theorem mappings, expected answers, hashes, and discrepancy records. Update hashes only against the intended source files; a refreshed hash does not establish semantic validity.

Any tool consuming these manifests must resolve paths from the repository root. Editing a manifest does not automatically update its consumers or trigger a Lean build.

Build and audit workflows should continue to operate on individual cases or an explicitly selected set. Reading the complete index does not require compiling every listed file.

Neither manifest establishes that the referenced files exist, that Lean compilation succeeded, or that expected answers are mathematically correct. File checks, compilation, axiom review, and semantic validation remain separate requirements.
