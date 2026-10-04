#!/usr/bin/env python3
"""scripts/check_json_syntax.py
Created: 18/09/2026
Author: Koorosh Nobakhtfar

Check JSON syntax without changing the input file.
Usage: python scripts/check_json_syntax.py "path/to/file.json"
Exit codes: 0 = valid JSON, 1 = invalid JSON, 2 = usage or file-read error.

Reusable API: parse_json(text), load_json(path), and JsonValidationError.
These functions return parsed data or raise exceptions; they never print or exit.
"""

import argparse
from decimal import Decimal
import json
from pathlib import Path
import sys
from typing import Any, NoReturn, Optional, Union


class JsonValidationError(ValueError):
    """Invalid JSON syntax or a violation of the requested parsing policy."""


def reject_nonstandard_constant(value: str) -> NoReturn:
    """Reject constants accepted by Python but excluded from standard JSON."""
    raise JsonValidationError(f"{value} is not a valid JSON value")


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Reject duplicate keys before constructing an object."""
    result: dict[str, Any] = {}

    for key, value in pairs:
        if key in result:
            raise JsonValidationError(f"duplicate JSON key: {key!r}")

        result[key] = value

    return result


def parse_json(text: str, *, reject_duplicate_keys: bool = False) -> Any:
    """Parse JSON text, rejecting NaN and Infinity.

    JSON integers become int; decimal/exponent numbers become Decimal to avoid
    floating-point overflow and rounding. Duplicate keys use the last value
    unless reject_duplicate_keys=True. Syntax/policy failures raise
    JsonValidationError; excessive nesting raises RecursionError.
    """
    try:
        return json.loads(
            text,
            parse_constant=reject_nonstandard_constant,
            parse_float=Decimal,
            object_pairs_hook=unique_object if reject_duplicate_keys else None,
        )

    except json.JSONDecodeError as exc:
        raise JsonValidationError(
            f"Line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc

    except JsonValidationError:
        raise

    except ValueError as exc:
        raise JsonValidationError(str(exc)) from exc


def load_json(
    path: Union[str, Path],
    *,
    reject_duplicate_keys: bool = False,
) -> Any:
    """Read a UTF-8 file (optional BOM) and return its parsed contents.

    Accepts a string or Path. Relative paths use the current working directory.
    Propagates OSError, UnicodeError, RecursionError, and JsonValidationError.
    """
    text = Path(path).read_text(encoding="utf-8-sig")
    return parse_json(text, reject_duplicate_keys=reject_duplicate_keys)


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Check a file for valid JSON syntax.")
    parser.add_argument("file", type=Path, help="Path to the JSON file")
    parser.add_argument(
        "--reject-duplicate-keys", action="store_true",
        help="Also reject repeated keys within an object",
    )

    args = parser.parse_args(argv)

    try:
        load_json(args.file, reject_duplicate_keys=args.reject_duplicate_keys)

    except UnicodeError as exc:
        print(f"INVALID ENCODING: {args.file}: expected UTF-8 ({exc})", file=sys.stderr)
        return 2

    except OSError as exc:
        print(f"FILE ERROR: {args.file}: {exc}", file=sys.stderr)
        return 2

    except JsonValidationError as exc:
        print(f"INVALID JSON: {args.file}: {exc}", file=sys.stderr)
        return 1

    except RecursionError:
        print(f"CHECK FAILED: {args.file}: nesting exceeds the parser's limit", file=sys.stderr)
        return 2

    print(f"VALID JSON: {args.file}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
