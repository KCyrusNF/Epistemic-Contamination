#!/usr/bin/env python3
"""validate_case_definition.py
Created: 18/09/2026
Author: Koorosh Nobakhtfar

Validate one test case JSON using Python 3.9+ (standard library only).
Usage: python scripts/validate_case_definition.py "path/to/test_case.json"
Exit codes: 0 = valid structure, 1 = invalid data, 2 = usage/read error.

Requires check_json_syntax.py beside this file for shared JSON loading.
Read-only: does not build Lean, scan the repository, or write reports.
Checks structure, not mathematical correctness, citations, proof validity,
or existence of the referenced Lean file/theorems. Unknown fields are rejected
so spelling mistakes cannot silently pass. Update the rules for schema changes.
The sample template's placeholder case ID is not a valid production case ID.
"""

import argparse
from datetime import datetime, timedelta
from pathlib import Path, PurePosixPath
import re
import sys

if __package__:
    from .check_json_syntax import JsonValidationError, load_json
else:
    from check_json_syntax import JsonValidationError, load_json

DOMAINS = {
    "AA": "abstract_algebra",
    "AT": "automata_theory_and_formal_languages",
    "BA": "boolean_algebra",
    "CT": "category_theory",
    "FL": "formal_logics_and_proof_systems",
    "LA": "linear_algebra",
}

PROTOCOL = [
    ('system_initialization', 'system_instruction'),
    ('standard_world_baseline', 'standard_rule_baseline'),
    ('standard_world_baseline', 'standard_derived_rule_baseline'),
    ('structural_perturbation_injection', 'rule_modification_and_application'),
    ('structural_perturbation_injection', 'standard_rule_rejection_test'),
    ('structural_perturbation_injection', 'repeated_rule_application'),
    ('downstream_rule_reconstruction', 'derived_rule_reconstruction_and_base_case_application'),
    ('downstream_rule_reconstruction', 'single_step_derived_rule_application'),
    ('downstream_rule_reconstruction', 'multi_step_derived_rule_application'),
    ('downstream_rule_reconstruction', 'derived_rule_underdetermination'),
    ('testing_indirect_consequences', 'missing_definition_probe'),
    ('testing_indirect_consequences', 'higher_level_implication_test'),
    ('boundary_isolation_and_meta_reasoning', 'world_distinction_test'),
    ('boundary_isolation_and_meta_reasoning', 'parallel_world_evaluation'),
    ('boundary_isolation_and_meta_reasoning', 'standard_rule_recovery'),
    ('boundary_isolation_and_meta_reasoning', 'standard_derived_rule_recovery'),
    ('boundary_isolation_and_meta_reasoning', 'modified_system_re_entry')
]

# Compact, explicit schema. Tuples represent arrays; None permits JSON null.
TEXT = "nonempty string"
PROMPT = {
    "content_raw": TEXT,
    "content_format": TEXT
}
REFERENCE = {
    "reference_id": TEXT,
    "citation": TEXT,
    "identifier": {
        "type": TEXT,
        "value": TEXT
    },
    "locator": "nullable string",
}
TURN = {
    "turn_id": "integer",
    "phase": TEXT,
    "turn_type": TEXT,
    "purpose": TEXT,
    "prompt": PROMPT,
    "expected_answer": {
        "answer_type": TEXT,
        "value": TEXT
    },
    "references": (REFERENCE, "nullable"),
}
SCHEMA = {
    "case_metadata": {
        "case_id": TEXT,
        "case_title": TEXT,
        "domain": TEXT,
        "created_by": (TEXT,),
        "reviewed_by": (TEXT,),
        "creation_timestamp_utc": TEXT,
    },
    "formal_artifacts": {
        "lean_file": TEXT,
        "oracle_theorems": (TEXT,)
    },
    "system_instruction": dict(TURN, expected_answer=None),
    "conversation_framework": (TURN,),
}


def check_shape(value, schema, path, errors):
    """Validate types and required/unknown keys with precise JSON paths."""
    if isinstance(schema, dict):
        if not isinstance(value, dict):
            errors.append(f"{path}: expected an object")
            return
        for key in schema:
            child = f"{path}.{key}"
            if key not in value:
                errors.append(f"{child}: missing required field")
            else:
                check_shape(value[key], schema[key], child, errors)
        for key in value.keys() - schema.keys():
            errors.append(f"{path}.{key}: unknown field")
    elif isinstance(schema, tuple):
        if value is None and len(schema) == 2:
            return
        if not isinstance(value, list):
            errors.append(f"{path}: expected an array" +
                          (" or null" if len(schema) == 2 else ""))
            return
        for index, item in enumerate(value):
            check_shape(item, schema[0], f"{path}[{index}]", errors)
    elif schema is None:
        if value is not None:
            errors.append(f"{path}: expected null (turn 0 has no oracle answer)")
    elif schema == "integer":
        if type(value) is not int:
            errors.append(f"{path}: expected an integer, not a boolean or decimal")
    elif schema == "nullable string":
        if value is not None and not isinstance(value, str):
            errors.append(f"{path}: expected a string or null")
    elif not isinstance(value, str) or not value.strip():
        errors.append(f"{path}: expected a nonempty string")


def validate_case(data):
    """Return structural errors for parsed data; never read files, print, or exit."""
    errors = []
    check_shape(data, SCHEMA, "$", errors)

    if errors:
        return errors  # Semantic structure checks require the correct types.

    meta = data["case_metadata"]

    if meta["domain"] not in DOMAINS.values():
        errors.append("$.case_metadata.domain: unsupported benchmark domain")

    case_id = meta["case_id"]
    if not re.fullmatch(r"(?:AA|AT|BA|CT|FL|LA)-[0-9]{2}", case_id):
        errors.append("$.case_metadata.case_id: expected a case ID such as BA-49")
    elif meta["domain"] != DOMAINS[case_id[:2]]:
        errors.append("$.case_metadata.domain: does not match the case ID prefix")

    if not meta["created_by"]:
        errors.append("$.case_metadata.created_by: supply at least one author")
    
    stamp = meta["creation_timestamp_utc"]
    try:
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|\+00:00)", stamp):
            raise ValueError
        parsed = datetime.fromisoformat(stamp.replace("Z", "+00:00"))
        if parsed.utcoffset() != timedelta(0):
            raise ValueError
    except ValueError:
        errors.append("$.case_metadata.creation_timestamp_utc: expected a valid UTC timestamp, e.g. 2026-09-18T12:00:00Z")

    artifacts = data["formal_artifacts"]

    lean_path = artifacts["lean_file"]
    path = PurePosixPath(lean_path)
    if (
        path.is_absolute()
        or ".." in path.parts
        or "\\" in lean_path
        or ":" in lean_path
        or path.suffix != ".lean"
        ):
        errors.append("$.formal_artifacts.lean_file: expected a relative .lean path with forward slashes and no '..'")

    names = artifacts["oracle_theorems"]

    case_prefix = case_id.lower().replace("-", "_")
    expected_names = [
        f"{case_prefix}_turn_{turn:02d}_oracle"
        for turn in range(1, 17)
    ]

    if names != expected_names:
        errors.append(
            "$.formal_artifacts.oracle_theorems: theorem names must exactly match "
            f"{case_prefix}_turn_01_oracle through {case_prefix}_turn_16_oracle, in order"
        )

    turns = data["conversation_framework"]

    if len(turns) != 16:
        errors.append("$.conversation_framework: expected exactly 16 turns")
    
    for index, turn in enumerate([data["system_instruction"]] + turns):
        location = "$.system_instruction" if index == 0 else f"$.conversation_framework[{index - 1}]"

        if turn["turn_id"] != index:
            errors.append(f"{location}.turn_id: expected {index}; turns must be ordered and consecutive")

        if index < len(PROTOCOL):
            for key, expected in zip(("phase", "turn_type"), PROTOCOL[index]):
                if turn[key] != expected:
                    errors.append(f"{location}.{key}: expected {expected!r}")

        if turn["prompt"]["content_format"] not in {"plain", "markdown", "latex", "mixed"}:
            errors.append(f"{location}.prompt.content_format: expected plain, markdown, latex, or mixed")

        if index > 0:
            answer = turn["expected_answer"]
            kind, value = answer["answer_type"], answer["value"]

            if kind not in {"exact_value", "semantic_statement", "undetermined"}:
                errors.append(f"{location}.expected_answer.answer_type: unsupported answer type")

            # Activate this test when the files are correctly using the exact same string.
            # if kind == "undetermined" and value != "Cannot be determined.":
            #     errors.append(
            #         f"{location}.expected_answer.value: must be exactly 'Cannot be determined.'"
            #     )

            if value.strip().lower().rstrip(".") == "cannot be determined" and kind != "undetermined":
                errors.append(
                    f"{location}.expected_answer.answer_type: use 'undetermined' for this answer"
                )

        refs = turn["references"]
        if refs is not None:
            ids = [ref["reference_id"] for ref in refs]
            if len(ids) != len(set(ids)):
                errors.append(f"{location}.references: duplicate reference IDs within this turn")
    
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("file", type=Path, help="one test case JSON file")
    args = parser.parse_args(argv)

    try:
        data = load_json(args.file, reject_duplicate_keys=True)
        errors = validate_case(data)
    except (OSError, UnicodeError) as exc:
        print(f"READ ERROR: {exc}", file=sys.stderr)
        return 2
    except JsonValidationError as exc:
        errors = [str(exc)]
    except RecursionError:
        print("ERROR: JSON nesting exceeds this interpreter's processing limit", file=sys.stderr)
        return 2
    
    if errors:
        print(f"INVALID: {args.file}", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    
    print(f"VALID STRUCTURE: {args.file} (16 turns + system instruction)")
    print("Mathematical correctness and Lean artifacts were not verified.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
