# Scripts

This directory contains small helper scripts that support project work outside the main program. Utilities may handle tasks such as validation, data extraction, file conversion, or report and spreadsheet generation. Each script has a specific purpose and documents its own requirements, usage, and outputs.

## Available scripts

| Script | Purpose |
| --- | --- |
| `check_json_syntax.py` | Checks whether a file contains valid JSON syntax. |
| `validate_case_definition.py` | Checks test case structure, conversation protocol, canonical system instructions, expected-answer conventions, and format labels for prompts and expected answers. |
| `validate-all-test-cases.ps1` | Runs the case-definition validator sequentially for every JSON file under `test_cases/`, including nested folders, and summarizes failures. |

## Validation utilities

The following sections describe `check_json_syntax.py`, `validate_case_definition.py`, and `validate-all-test-cases.ps1`. Their requirements and limitations apply to these scripts.

### Requirements

The two Python validators require Python 3.9 or later. They use the Python standard library and require no additional packages. Keep both files together in this `scripts/` directory: the case-definition validator imports the shared JSON loader from `check_json_syntax.py`. Each Python script has its own command-line entry point. The PowerShell script requires PowerShell 5.1 or later and must remain beside both Python validators.

Run the examples below from the repository root. For the Python commands, input paths are resolved relative to the terminal's current working directory; absolute paths are also accepted. Quote paths that contain spaces.

### Check JSON syntax

```powershell
python scripts/check_json_syntax.py "manifests/case_paths.json"
```

This utility can check any JSON file, including manifests, test case definitions, and run logs. It reports parsing errors with line and column numbers where available, and rejects nonstandard constants such as `NaN` and `Infinity`.

A successful check means the file can be parsed as JSON. It does not check required fields, field types, or the meaning of the data. Duplicate object keys are allowed by default; optionally reject them with:

```powershell
python scripts/check_json_syntax.py "manifests/case_paths.json" --reject-duplicate-keys
```

### Validate a test case definition

```powershell
python scripts/validate_case_definition.py "test_cases/boolean_algebra/BA-49.json"
```

The validator checks:

- JSON syntax and duplicate object keys.
- Required fields, field types, nonempty required text, and unexpected fields.
- Supported domains, case ID format, and agreement between the case ID prefix and domain.
- Author and reviewer list structure, with at least one author required.
- UTC creation timestamp format and date validity.
- A system instruction at turn 0 with no expected answer, followed by exactly 16 ordered, consecutively numbered conversation turns.
- The prescribed phase and turn type for each position in the conversation.
- Exact agreement of the complete system-instruction block with `EXPECTED_SYSTEM_INSTRUCTION` in the validator.
- Expected-answer fields `answer_type`, `content_raw`, and `content_format`.
- Supported expected-answer types: `exact_value`, `semantic_statement`, and `undetermined`.
- The exact `content_raw` value `Cannot be determined.` for every expected answer classified as `undetermined`.
- Classification as `undetermined` when the expected-answer `content_raw` matches “cannot be determined” after trimming surrounding whitespace, converting to lowercase, and removing trailing periods.
- Prompt and expected-answer format labels restricted to `plain`, `latex`, and `mixed`, with content-based checks for turns 1–16.
- Paired, nonempty `$$...$$` mathematical blocks; unsupported mathematical delimiters are rejected.
- Reference structure and duplicate reference IDs within each turn.

The validation rules are defined within the utility. Changes to the test case format or conversation protocol require corresponding changes to those rules. Templates containing placeholder case IDs are not valid production case definitions.

The validator calls the shared JSON loader once, with duplicate-key rejection enabled, then checks the parsed case structure. Running the syntax checker separately beforehand is unnecessary.

#### Canonical system instruction

Every case must match the complete reference block stored in `EXPECTED_SYSTEM_INSTRUCTION`, including the purpose, full prompt text, `content_format: "plain"`, and `null` values for `expected_answer` and `references`. Errors identify the differing field.

The comparison uses parsed JSON values. Object-key order, indentation, and equivalent JSON escape representations do not matter; capitalization, punctuation, and whitespace within strings must match exactly. Changes to the shared instruction require updating both the reference constant and the case definitions.

#### Underdetermined expected answers

An expected answer with `answer_type: "undetermined"` must have exactly `"Cannot be determined."` in `content_raw`, with `content_format: "plain"`. Different capitalization, missing punctuation, extra whitespace, or an appended explanation fails validation.

The stored expected value contains the direct answer only. The canonical system instruction separately asks the model to begin its response with that text and add one short explanatory sentence. The validator checks the expected-answer convention; it does not establish mathematical underdetermination or validate actual model responses.

#### Prompt and expected-answer format checks

For turns 1–16, prompts and expected answers both contain `content_raw` and `content_format`. Expected answers also require `answer_type`:

```json
"expected_answer": {
  "answer_type": "exact_value",
  "content_raw": "$$2$$",
  "content_format": "latex"
}
```

The shared `check_content_format` function scans `content_raw` and compares the detected format with `content_format` using the same rules for both:

| Label | Required content | Example |
| --- | --- | --- |
| `plain` | No mathematical blocks. | `Is the operation associative?` |
| `latex` | One or more `$$...$$` blocks, with only whitespace outside them. | `$$2 + 3$$` |
| `mixed` | Mathematical blocks combined with other text or punctuation. | `Calculate $$2 + 3$$.` |

Punctuation outside a mathematical block counts as surrounding content: `$$2 + 3$$.` is classified as `mixed`. Whitespace between mathematical blocks does not change a `latex` classification.

The scanner rejects unmatched delimiters, empty or whitespace-only blocks, and runs of dollar signs other than exactly `$$`. It also rejects `\(...\)` and `\[...\]` mathematical delimiters. Literal dollar signs must be escaped in `content_raw` as `\$` (represented as `"\\$"` in JSON). Delimiter errors are reported before attempting format classification.

The canonical system instruction is exempt from this scan because its `$$...$$` is an instructional example; its required `plain` label is enforced by the exact block comparison.

These delimiter and format-label checks apply to both question prompts and expected answers. They do not validate actual model responses. Turn 0 retains `expected_answer: null`.

Markdown is not a supported format label. The validator does not interpret Markdown, mask code blocks, or detect and prohibit Markdown syntax. It also does not validate LaTeX commands or detect mathematical content missing its delimiters: `Calculate 2 + 3.` is classified as `plain`.

### Validate all test case definitions

From the repository root:

```powershell
.\scripts\validate-all-test-cases.ps1
```

If Python is available through the Windows `py` launcher, use:

```powershell
.\scripts\validate-all-test-cases.ps1 -Python py -PythonArguments '-3'
```

`-Python` accepts an executable name or full path; it defaults to `python`. `-PythonArguments` supplies optional interpreter arguments.

The script locates `test_cases/` relative to its own location, recursively discovers all `.json` files, and validates them one at a time in sorted path order. It calls `validate_case_definition.py`, which reuses the JSON loader from `check_json_syntax.py`; no separate syntax-check pass is needed. It does not use `manifests/case_paths.json`.

Each case's diagnostics appear in the terminal. A failed case does not stop the remaining cases from being checked. The final summary reports the numbers checked, passed, invalid, and affected by execution or read errors, followed by the paths of failed cases. A setup error, such as a missing validator, unavailable Python interpreter, or missing or empty `test_cases/` directory, stops the run.

If execution policy blocks the script, run it in a separate PowerShell process with a policy override for that process only:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\scripts\validate-all-test-cases.ps1 -Python py -PythonArguments '-3'
```

Every run validates all discovered definitions again using the current Python rules, including checks for the canonical system instruction, underdetermined expected-answer values, and formats for prompts and expected answers. It does not skip unchanged files or enforce a fixed case count.

The script does not modify test case definitions, create report files, or invoke Lean.

### Reuse from other scripts

`check_json_syntax.py` owns JSON reading and parsing. Its functions do not print, exit, or modify files:

| API | Behavior |
| --- | --- |
| `load_json(path, *, reject_duplicate_keys=False)` | Reads a UTF-8 file with an optional BOM and returns parsed data. |
| `parse_json(text, *, reject_duplicate_keys=False)` | Parses an already-decoded JSON string. |
| `JsonValidationError` | Raised for invalid syntax, nonstandard constants, or duplicate keys when rejection is enabled. |
| `validate_case(data)` in `validate_case_definition.py` | Returns a list of structure, protocol, instruction, answer-convention, and content-format errors for parsed data; an empty list means those checks passed. |

For another script in this directory:

```python
from check_json_syntax import load_json
from validate_case_definition import validate_case

data = load_json("test_cases/boolean_algebra/BA-49.json",
                 reject_duplicate_keys=True)
errors = validate_case(data)
```

For imports from the repository root, use `from scripts.check_json_syntax import load_json` and `from scripts.validate_case_definition import validate_case`. Both command-line tools also support module invocation from the repository root, for example `python -m scripts.validate_case_definition "test_cases/boolean_algebra/BA-49.json"`.

The shared loader rejects `NaN` and `Infinity`. Integers become Python `int` values; decimal and exponent numbers become `decimal.Decimal` values to avoid floating-point rounding or overflow. With duplicate-key rejection disabled, the last value for a repeated key is retained.

Callers handle `JsonValidationError` for invalid input, `OSError` for file access failures, `UnicodeError` for invalid encoding, and `RecursionError` for excessive nesting. Importing either module performs no checks. Each `main(argv=None)` function provides its command-line entry point and returns an exit code; `argparse` handles help and invalid command usage.

### Output and exit codes

Both Python utilities print their result to the terminal. Successful checks go to standard output; errors go to standard error. They do not modify the input file or create report files.

| Exit code | Meaning |
| --- | --- |
| `0` | The requested checks passed. |
| `1` | Invalid JSON or a failed case-definition check. |
| `2` | Invalid command usage, a file-read or encoding error, or nesting beyond the parser's processing limit. |

For `validate-all-test-cases.ps1`, exit codes summarize the entire run:

| Exit code | Meaning |
| --- | --- |
| `0` | All discovered test case definitions passed. |
| `1` | At least one definition failed validation, with no execution or read errors. |
| `2` | A setup, execution, or read error occurred. This takes precedence over validation failures. |

In PowerShell, inspect the exit code immediately after running a command:

```powershell
$LASTEXITCODE
```

Display usage information with:

```powershell
python scripts/check_json_syntax.py --help
python scripts/validate_case_definition.py --help
Get-Help .\scripts\validate-all-test-cases.ps1 -Full
```

### Scope and limitations

The three validation utilities listed above check syntax, structure, the canonical system instruction, expected-answer types and required underdetermined values, and formatting of prompts and expected answers. They do not run Lean, inspect proofs or axiom dependencies, verify mathematical answers, or establish that prompts faithfully represent their intended formal systems.

The case-definition validator does not compare test case entries with the repository manifests or verify citation accuracy. Those require separate checks.

The Python utilities require an explicit file path. The PowerShell script discovers files directly under `test_cases/` and its subdirectories; none of these utilities checks the completeness or accuracy of `case_paths.json`.

The message `Mathematical correctness and external manifest consistency were not verified.` describes the scope of the case-definition validator. It is informational and does not indicate a validation failure or invalidate separately completed Lean builds and audits.

## File conventions

Use UTF-8 text with CRLF line endings for repository source files and documentation. The JSON validators accept UTF-8 input with or without a byte-order mark and can read LF or CRLF line endings.
