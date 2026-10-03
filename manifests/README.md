# Manifests

This directory contains machine-readable manifests for benchmark file locations and oracle metadata. Both manifests identify cases by `case_id` and use repository-root-relative file paths.

## Contents

| File | Purpose |
| --- | --- |
| `case_paths.json` | Maps each case ID to its test case definition, Lean source, axiom audit, and listed result files, with a path and SHA-512 hash for each file. |
| `oracle_manifest.json` | Records oracle theorem mappings, expected answers, source hashes, and known discrepancies. |

## Case paths format

`case_paths.json` contains `created`, `author`, `case_count`, and a `cases` array. The creation date uses `YYYY-MM-DD`, and `case_count` must equal the number of entries in `cases`. Git tracks revisions to the manifest. Each case entry has these fields:

| Field | Meaning |
| --- | --- |
| `case_id` | Unique benchmark case identifier, such as `BA-49`. |
| `definition` | Object containing the test case definition’s `path` and `sha512`. |
| `lean_source` | Object containing the Lean oracle source’s `path` and `sha512`. |
| `axiom_audit` | Object containing the Lean axiom audit’s `path` and `sha512`. |
| `results` | Array of result-file objects, each containing `path` and `sha512`; empty when no results are listed. |

Each file object contains a repository-root-relative `path` and a `sha512` value. Use `null` until the hash is populated; a populated hash is a lowercase string of 128 hexadecimal characters. `null` means no hash has been recorded.

Every case includes a `results` array. Use `[]` when no result files are listed, rather than `null` or a placeholder file with no path. Multiple result files may be recorded for the same case.

Example with one case (the full manifest has `case_count: 60`):

```json
{
  "created": "2026-09-18",
  "author": "Koorosh Nobakhtfar",
  "case_count": 1,
  "cases": [
    {
      "case_id": "BA-49",
      "definition": {
        "path": "test_cases/boolean_algebra/BA-49.json",
        "sha512": null
      },
      "lean_source": {
        "path": "lean/oracles/boolean_algebra/BA-49.lean",
        "sha512": null
      },
      "axiom_audit": {
        "path": "lean/audits/boolean_algebra/BA-49.lean",
        "sha512": null
      },
      "results": []
    }
  ]
}
```

The current manifest lists 60 cases across six domains. Result files do not increase `case_count`.

A populated `results` array contains file objects such as the following (illustrative paths):

```json
[
  {
    "path": "results/BA-49/run-001.json",
    "sha512": null
  },
  {
    "path": "results/BA-49/run-002.json",
    "sha512": null
  }
]
```

SHA-512 hashes represent exact file bytes, including whitespace, encoding, and line endings. They identify a recorded file version; they do not establish the validity of a result or its evaluation.

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

The manifest covers 60 cases and 960 oracle theorems. Its `lean_file` value must match the corresponding `lean_source.path` value in `case_paths.json`, for example `lean/oracles/boolean_algebra/BA-49.lean`.

Expected answers and hashes are recorded metadata, not proof of correctness. Hashes must be checked against the intended source version, and known discrepancies must be resolved through semantic review.

## Path conventions

- Resolve every path relative to the repository root, not this directory or the terminal's current working directory.
- Use forward slashes, including on Windows.
- Do not include a leading slash, drive letter, or parent-directory traversal (`..`).
- Keep case IDs unique and entries sorted by case ID.
- Store test case definitions, oracle sources, and audits in their designated fields. List result files, including experimental run logs, in the corresponding case’s `results` array. Exclude compiled build artifacts.
- Save text files as UTF-8 with CRLF line endings.

For example, `test_cases/boolean_algebra/BA-49.json` identifies that file beneath the repository root. A script reading `manifests/case_paths.json` can resolve it against the parent of the `manifests` directory.

## Maintenance and use

When adding, renaming, moving, or removing a case, update the affected entries in both manifests and keep their case counts consistent with their contents. Check that the case IDs agree, the source and result paths in `case_paths.json` identify the intended files, and `oracle_manifest.json` records the same Lean source path.

When a test case definition or formalization changes, review the corresponding theorem mappings, expected answers, hashes, and discrepancy records. When result files are added, moved, or removed, update the corresponding `results` array. Update hashes only against the intended file versions; a refreshed hash does not establish semantic validity.

Consumers of `case_paths.json` must read `definition.path`, `lean_source.path`, and `axiom_audit.path`, and iterate over `results` to read each file’s `path` and `sha512`. Any tool consuming these manifests must resolve paths from the repository root. Editing a manifest does not automatically update its consumers or trigger a Lean build.

Build and audit workflows should continue to operate on individual cases or an explicitly selected set. Reading the complete index does not require compiling every listed file.

Neither manifest establishes that the referenced files exist, that Lean compilation succeeded, or that expected answers are mathematically correct. File checks, compilation, axiom review, and semantic validation remain separate requirements.
