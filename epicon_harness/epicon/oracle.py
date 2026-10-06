"""Read-only access to the repository's Lean oracle manifest.

Test cases used to carry a ``formal_artifacts`` block naming their Lean file and
sixteen oracle theorems. That block was removed from the case schema, and the
same information now lives in ``manifests/oracle_manifest.json`` at the
repository root, keyed by case id::

    {"cases": [{"case_id": "AA-01",
                "lean_file": "lean/oracles/abstract_algebra/AA-01.lean",
                "oracle_theorems": ["aa_01_turn_01_oracle", ...],
                "turns": [{"turn_id": 1, "expected_answer": "Yes.", ...}, ...]}]}

The manifest sits outside the harness, so it is read through
:func:`epicon.paths.resolve_oracle_path`, which bounds resolution to the
repository root. A missing manifest is not an error: :func:`load_oracle_manifest`
returns an empty manifest and the pipeline runs with no oracle linkage, exactly
as it did before this module existed.
"""

from __future__ import annotations

import json
import threading
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import TYPE_CHECKING, Any

from . import paths
from .errors import SchemaError

if TYPE_CHECKING:  # avoids a cycle: models imports this module
    from .models import TestCase


@dataclass(frozen=True)
class OracleTurn:
    """One ``cases[].turns[]`` entry: the ground truth for a single turn."""

    turn_id: int
    expected_answer: str | None = None
    prompt_sha256: str | None = None


@dataclass(frozen=True)
class OracleCase:
    """Everything the manifest knows about one case."""

    case_id: str
    case_title: str = ""
    lean_file: str | None = None
    oracle_theorems: list[str] = field(default_factory=list)
    source_case_sha256: str | None = None
    turns: list[OracleTurn] = field(default_factory=list)

    def theorem_for(self, turn_id: int) -> str | None:
        """The Lean theorem paired with *turn_id* (1-based)."""
        index = turn_id - 1
        if 0 <= index < len(self.oracle_theorems):
            return self.oracle_theorems[index]
        return None

    def turn(self, turn_id: int) -> OracleTurn | None:
        for candidate in self.turns:
            if candidate.turn_id == turn_id:
                return candidate
        return None

    def expected_answer_for(self, turn_id: int) -> str | None:
        """The verified ground-truth answer for *turn_id*."""
        found = self.turn(turn_id)
        return found.expected_answer if found else None

    def resolved_lean_path(self) -> Path | None:
        """Absolute path of ``lean_file``, confined to the repository root."""
        if not self.lean_file:
            return None
        return paths.resolve_oracle_path(self.lean_file)

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> OracleCase:
        case_id = str(data.get("case_id") or "").strip()
        if not case_id:
            raise SchemaError("'cases[].case_id' is required", source=source)

        theorems = [str(name) for name in (data.get("oracle_theorems") or [])]
        turns = [
            OracleTurn(
                turn_id=int(entry["turn_id"]),
                expected_answer=(
                    str(entry["expected_answer"])
                    if entry.get("expected_answer") is not None
                    else None
                ),
                prompt_sha256=(
                    str(entry["prompt_sha256"])
                    if entry.get("prompt_sha256") is not None
                    else None
                ),
            )
            for entry in (data.get("turns") or [])
            if isinstance(entry, Mapping) and entry.get("turn_id") is not None
        ]

        return cls(
            case_id=case_id,
            case_title=str(data.get("case_title") or ""),
            lean_file=(str(data["lean_file"]) if data.get("lean_file") else None),
            oracle_theorems=theorems,
            source_case_sha256=(
                str(data["source_case_sha256"]) if data.get("source_case_sha256") else None
            ),
            turns=sorted(turns, key=lambda turn: turn.turn_id),
        )


@dataclass(frozen=True)
class OracleManifest:
    """The parsed manifest, indexed by case id."""

    cases: dict[str, OracleCase] = field(default_factory=dict)
    path: Path | None = None

    def for_case(self, case_id: str) -> OracleCase | None:
        return self.cases.get(case_id)

    def __contains__(self, case_id: object) -> bool:
        return case_id in self.cases

    def __len__(self) -> int:
        return len(self.cases)

    @property
    def available(self) -> bool:
        """Whether any oracle data was actually found."""
        return bool(self.cases)

    @classmethod
    def empty(cls, path: Path | None = None) -> OracleManifest:
        return cls(cases={}, path=path)

    @classmethod
    def from_dict(
        cls, data: Mapping[str, Any], source: str, path: Path | None = None
    ) -> OracleManifest:
        raw_cases = data.get("cases")
        if not isinstance(raw_cases, list):
            raise SchemaError("'cases' must be a list", source=source)
        cases: dict[str, OracleCase] = {}
        for entry in raw_cases:
            if not isinstance(entry, Mapping):
                raise SchemaError("'cases[]' entries must be objects", source=source)
            case = OracleCase.from_dict(entry, source)
            cases.setdefault(case.case_id, case)
        return cls(cases=cases, path=path)

    @classmethod
    def from_file(cls, path: str | Path) -> OracleManifest:
        file_path = Path(path)
        try:
            raw = json.loads(file_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise SchemaError(f"invalid JSON ({exc})", source=str(file_path)) from exc
        return cls.from_dict(raw, source=str(file_path), path=file_path)


_lock = threading.Lock()
_cache: dict[Path, OracleManifest] = {}


def load_oracle_manifest(
    path: str | Path | None = None, *, refresh: bool = False
) -> OracleManifest:
    """Load (and memoise) the oracle manifest.

    Defaults to the repository-root manifest. Returns an empty manifest when the
    file is absent, so a harness-only checkout still works.
    """
    target = Path(path).expanduser().resolve() if path else paths.oracle_manifest_path()

    with _lock:
        if not refresh and target in _cache:
            return _cache[target]
        manifest = (
            OracleManifest.from_file(target)
            if target.is_file()
            else OracleManifest.empty(target)
        )
        _cache[target] = manifest
        return manifest


def clear_cache() -> None:
    """Drop memoised manifests (used by tests)."""
    with _lock:
        _cache.clear()


def attach(case: TestCase, manifest: OracleManifest | None = None) -> TestCase:
    """Return *case* with its manifest oracle data attached, matched by case id.

    Returns the case untouched when the manifest has no entry for it, so a case
    without an oracle is a quiet absence rather than a failure.
    """
    resolved = manifest if manifest is not None else load_oracle_manifest()
    found = resolved.for_case(case.case_id)
    if found is None:
        return case
    return replace(case, oracle=found)


def attach_all(
    cases: Iterable[TestCase], manifest: OracleManifest | None = None
) -> list[TestCase]:
    """:func:`attach` over many cases, loading the manifest once."""
    resolved = manifest if manifest is not None else load_oracle_manifest()
    return [attach(case, resolved) for case in cases]
