"""Core data models — one class per block of the two SRS schemas.

* Test case  (SRS 3.1) -> ``templates/test_case_template.json``
* Run log    (SRS 3.2) -> ``results/{Model}-run-{N}/{domain}/{Case}-{Model}-R{N}.json``

The models are written for **round-trip fidelity**: ``from_dict`` followed by
``to_dict`` reproduces the document exactly, keys emitted in schema order and
explicit ``null`` preserved as ``null`` (nothing is pruned). ``tests/`` asserts
this against the template files themselves.

Two consequences of the specification are visible throughout this module:

* **No runtime grading.** SRS 1.3 excludes regex parsers, token extractors and
  string normalizers from the framework, so ``evaluation.is_correct``,
  ``failure_mode`` and ``comments`` are written as ``null`` and reserved for
  post-hoc human audit. ``evaluation_summary`` counts are likewise ``null``.
* **The oracle is static.** ``formal_artifacts.oracle_theorems`` maps 1:1 onto
  turns 1–16, and each logged turn carries its ``oracle_theorem_ref``
  (REQ-RUN-003). No Lean binary is invoked at run time.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from . import paths
from .errors import SchemaError

#: The system instruction occupies turn 0; conversation turns start at 1.
SYSTEM_TURN_ID = 0
#: SRS 3.1: the conversation framework is exactly sixteen turns.
TURNS_PER_CASE = 16

#: SRS 3.1: ``^(AA|CT|FL|BA|AT|LA)-[0-9]{2}$``.
CASE_ID_PATTERN = re.compile(r"^(AA|CT|FL|BA|AT|LA)-[0-9]{2}$")

#: SRS 3.1: the six active mathematical domains. ``type_theory`` is out of scope.
DOMAINS = (
    "abstract_algebra",
    "category_theory",
    "formal_logic",
    "boolean_algebra",
    "automata_theory",
    "linear_algebra",
)

CONTENT_FORMATS = ("plain", "mixed")
ROLE_USER = "user"
ROLE_ASSISTANT = "assistant"

#: SRS 3.1 ``expected_answer.answer_type``.
ANSWER_TYPE_EXACT = "exact_value"
ANSWER_TYPE_SEMANTIC = "semantic_statement"
ANSWER_TYPE_UNDETERMINED = "undetermined"
ANSWER_TYPES = (ANSWER_TYPE_EXACT, ANSWER_TYPE_SEMANTIC, ANSWER_TYPE_UNDETERMINED)

#: SRS 3.2 ``run_metadata.status``.
STATUS_COMPLETED = "COMPLETED"
STATUS_FAILED = "FAILED"

REVIEW_STATUS_UNREVIEWED = "unreviewed"
#: Placeholder id for the reviewer slot the runner initialises.
UNASSIGNED_REVIEWER = "unassigned"


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #
def utc_now() -> str:
    """Current UTC time in the schema's timestamp format (``…:SSZ``)."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def normalise_domain(domain: str) -> str:
    """REQ-RUN-012: ``abstract_algebra`` -> ``abstract-algebra``."""
    return (domain or "").strip().lower().replace("_", "-")


def _mapping(value: Any, source: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise SchemaError(f"expected a JSON object, got {type(value).__name__}", source=source)
    return value


def _req_str(data: Mapping[str, Any], key: str, source: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value.strip():
        raise SchemaError(f"'{key}' is required and must be a non-empty string", source=source)
    return value


def _opt_str(data: Mapping[str, Any], key: str) -> str | None:
    value = data.get(key)
    return value if isinstance(value, str) else None


def _req_int(data: Mapping[str, Any], key: str, source: str) -> int:
    value = data.get(key)
    if isinstance(value, bool) or not isinstance(value, int):
        raise SchemaError(f"'{key}' is required and must be an integer", source=source)
    return value


def _opt_int(data: Mapping[str, Any], key: str) -> int | None:
    value = data.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return int(value)


def _opt_float(data: Mapping[str, Any], key: str) -> float | None:
    value = data.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _opt_bool(data: Mapping[str, Any], key: str) -> bool | None:
    value = data.get(key)
    return value if isinstance(value, bool) else None


def _str_list(value: Any, source: str, key: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, Sequence) or isinstance(value, str):
        raise SchemaError(f"'{key}' must be a list of strings", source=source)
    return [str(item) for item in value]


def canonical_hash(payload: Any) -> str:
    """Stable sha256 of a JSON-serialisable payload."""
    blob = json.dumps(payload, sort_keys=True, ensure_ascii=False, default=str)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


# ========================================================================== #
# TEST CASE SCHEMA (SRS 3.1)
# ========================================================================== #
@dataclass(frozen=True)
class CaseMetadata:
    """``case_metadata`` block."""

    case_id: str
    case_title: str = ""
    domain: str = ""
    created_by: list[str] = field(default_factory=list)
    reviewed_by: list[str] = field(default_factory=list)
    creation_timestamp_utc: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> CaseMetadata:
        where = f"{source}.case_metadata"
        data = _mapping(data, where)

        case_id = _req_str(data, "case_id", where)
        if not CASE_ID_PATTERN.match(case_id):
            raise SchemaError(
                f"'case_id' must match {CASE_ID_PATTERN.pattern} (got '{case_id}')",
                source=where,
            )
        domain = _opt_str(data, "domain") or ""
        if domain not in DOMAINS:
            raise SchemaError(
                f"'domain' must be one of {DOMAINS} (got '{domain}')", source=where
            )

        return cls(
            case_id=case_id,
            case_title=_opt_str(data, "case_title") or "",
            domain=domain,
            created_by=_str_list(data.get("created_by"), where, "created_by"),
            reviewed_by=_str_list(data.get("reviewed_by"), where, "reviewed_by"),
            creation_timestamp_utc=_opt_str(data, "creation_timestamp_utc"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "case_id": self.case_id,
            "case_title": self.case_title,
            "domain": self.domain,
            "created_by": list(self.created_by),
            "reviewed_by": list(self.reviewed_by),
            "creation_timestamp_utc": self.creation_timestamp_utc,
        }


@dataclass(frozen=True)
class FormalArtifacts:
    """``formal_artifacts``: the Lean 4 file and its sixteen oracle theorems."""

    lean_file: str | None = None
    oracle_theorems: list[str] = field(default_factory=list)

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> FormalArtifacts:
        if data is None:
            return cls()
        where = f"{source}.formal_artifacts"
        data = _mapping(data, where)
        return cls(
            lean_file=_opt_str(data, "lean_file"),
            oracle_theorems=_str_list(data.get("oracle_theorems"), where, "oracle_theorems"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "lean_file": self.lean_file,
            "oracle_theorems": list(self.oracle_theorems),
        }

    def resolved_lean_path(self) -> Path | None:
        """Absolute path of ``lean_file``, confined to the project root."""
        if not self.lean_file:
            return None
        return paths.resolve_data_path(self.lean_file)


@dataclass(frozen=True)
class Prompt:
    """A test case ``prompt`` block."""

    content_raw: str
    content_format: str = "plain"

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> Prompt:
        where = f"{source}.prompt"
        data = _mapping(data, where)
        content_format = _opt_str(data, "content_format") or "plain"
        if content_format not in CONTENT_FORMATS:
            raise SchemaError(
                f"'content_format' must be one of {CONTENT_FORMATS}, got '{content_format}'",
                source=where,
            )
        return cls(
            content_raw=_req_str(data, "content_raw", where),
            content_format=content_format,
        )

    def to_dict(self) -> dict[str, Any]:
        return {"content_raw": self.content_raw, "content_format": self.content_format}

    @property
    def contains_latex(self) -> bool:
        return self.content_format == "mixed"


@dataclass(frozen=True)
class ExpectedAnswer:
    """``expected_answer``: the Lean ground truth for one turn.

    This is reference material for the human auditor, not a grading input: nothing
    in the runner compares it to the model's text (SRS 1.3).
    """

    answer_type: str
    value: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> ExpectedAnswer | None:
        if data is None:
            return None
        where = f"{source}.expected_answer"
        data = _mapping(data, where)
        answer_type = _req_str(data, "answer_type", where)
        if answer_type not in ANSWER_TYPES:
            raise SchemaError(
                f"'answer_type' must be one of {ANSWER_TYPES} (got '{answer_type}')",
                source=where,
            )
        return cls(answer_type=answer_type, value=_opt_str(data, "value"))

    def to_dict(self) -> dict[str, Any]:
        return {"answer_type": self.answer_type, "value": self.value}

    @property
    def is_undetermined(self) -> bool:
        """Whether Lean proves no unique answer exists (highlighted by the exporter)."""
        return self.answer_type == ANSWER_TYPE_UNDETERMINED


@dataclass(frozen=True)
class Identifier:
    """``references[].identifier``: a DOI, ISBN or similar."""

    type: str
    value: str

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> Identifier | None:
        if data is None:
            return None
        where = f"{source}.identifier"
        data = _mapping(data, where)
        return cls(type=_req_str(data, "type", where), value=_req_str(data, "value", where))

    def to_dict(self) -> dict[str, Any]:
        return {"type": self.type, "value": self.value}


@dataclass(frozen=True)
class Reference:
    """One entry of a turn's ``references`` list."""

    reference_id: str
    citation: str = ""
    identifier: Identifier | None = None
    locator: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str, index: int) -> Reference:
        where = f"{source}.references[{index}]"
        data = _mapping(data, where)
        return cls(
            reference_id=_req_str(data, "reference_id", where),
            citation=_opt_str(data, "citation") or "",
            identifier=Identifier.from_dict(data.get("identifier"), where),
            locator=_opt_str(data, "locator"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "reference_id": self.reference_id,
            "citation": self.citation,
            "identifier": self.identifier.to_dict() if self.identifier else None,
            "locator": self.locator,
        }


@dataclass(frozen=True)
class Turn:
    """One entry of ``conversation_framework``, or the ``system_instruction``.

    ``references`` distinguishes ``null`` (:data:`None`) from an empty list, since
    the schema uses both.
    """

    turn_id: int
    turn_type: str
    phase: str = ""
    purpose: str = ""
    prompt: Prompt = field(default_factory=lambda: Prompt(content_raw=""))
    expected_answer: ExpectedAnswer | None = None
    references: list[Reference] | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> Turn:
        data = _mapping(data, source)
        turn_id = _req_int(data, "turn_id", source)
        where = f"{source}[turn {turn_id}]"

        references_raw = data.get("references")
        references: list[Reference] | None
        if references_raw is None:
            references = None
        elif isinstance(references_raw, Sequence) and not isinstance(references_raw, str):
            references = [
                Reference.from_dict(item, where, index)
                for index, item in enumerate(references_raw)
            ]
        else:
            raise SchemaError("'references' must be a list or null", source=where)

        return cls(
            turn_id=turn_id,
            turn_type=_req_str(data, "turn_type", where),
            phase=_opt_str(data, "phase") or "",
            purpose=_opt_str(data, "purpose") or "",
            prompt=Prompt.from_dict(data.get("prompt") or {}, where),
            expected_answer=ExpectedAnswer.from_dict(data.get("expected_answer"), where),
            references=references,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "turn_id": self.turn_id,
            "phase": self.phase,
            "turn_type": self.turn_type,
            "purpose": self.purpose,
            "prompt": self.prompt.to_dict(),
            "expected_answer": (
                self.expected_answer.to_dict() if self.expected_answer else None
            ),
            "references": (
                None if self.references is None else [r.to_dict() for r in self.references]
            ),
        }

    @property
    def content(self) -> str:
        """The text transmitted for this turn, exactly as authored."""
        return self.prompt.content_raw


@dataclass(frozen=True)
class TestCase:
    """A complete test case document."""

    case_metadata: CaseMetadata
    formal_artifacts: FormalArtifacts = field(default_factory=FormalArtifacts)
    system_instruction: Turn | None = None
    conversation_framework: list[Turn] = field(default_factory=list)
    source_path: str | None = None
    content_hash: str = ""

    # -- parsing ------------------------------------------------------------ #
    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str = "<test case>") -> TestCase:
        data = _mapping(data, source)

        framework_raw = data.get("conversation_framework")
        if not isinstance(framework_raw, Sequence) or isinstance(framework_raw, str):
            raise SchemaError("'conversation_framework' must be a list", source=source)

        turns = [
            Turn.from_dict(item, f"{source}.conversation_framework") for item in framework_raw
        ]
        expected_ids = list(range(1, TURNS_PER_CASE + 1))
        if [turn.turn_id for turn in turns] != expected_ids:
            raise SchemaError(
                f"'conversation_framework' must hold exactly {TURNS_PER_CASE} turns with "
                f"turn_id 1..{TURNS_PER_CASE} in order (got "
                f"{[turn.turn_id for turn in turns]})",
                source=source,
            )

        artifacts = FormalArtifacts.from_dict(data.get("formal_artifacts"), source)
        if len(artifacts.oracle_theorems) != TURNS_PER_CASE:
            raise SchemaError(
                f"'formal_artifacts.oracle_theorems' must hold exactly {TURNS_PER_CASE} "
                f"identifiers, one per turn (got {len(artifacts.oracle_theorems)})",
                source=source,
            )

        system_raw = data.get("system_instruction")
        system_instruction = (
            Turn.from_dict(system_raw, f"{source}.system_instruction")
            if system_raw is not None
            else None
        )

        return cls(
            case_metadata=CaseMetadata.from_dict(data.get("case_metadata") or {}, source),
            formal_artifacts=artifacts,
            system_instruction=system_instruction,
            conversation_framework=turns,
            content_hash=canonical_hash(data),
        )

    @classmethod
    def from_file(cls, path: str | Path) -> TestCase:
        file_path = Path(path)
        try:
            raw = json.loads(file_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise SchemaError(f"invalid JSON ({exc})", source=str(file_path)) from exc
        case = cls.from_dict(raw, source=str(file_path))
        return replace(case, source_path=paths.as_project_relative(file_path))

    # -- emitting ----------------------------------------------------------- #
    def to_dict(self) -> dict[str, Any]:
        return {
            "case_metadata": self.case_metadata.to_dict(),
            "formal_artifacts": self.formal_artifacts.to_dict(),
            "system_instruction": (
                self.system_instruction.to_dict() if self.system_instruction else None
            ),
            "conversation_framework": [turn.to_dict() for turn in self.conversation_framework],
        }

    # -- convenience -------------------------------------------------------- #
    @property
    def case_id(self) -> str:
        return self.case_metadata.case_id

    @property
    def case_title(self) -> str:
        return self.case_metadata.case_title

    @property
    def domain(self) -> str:
        return self.case_metadata.domain

    @property
    def normalised_domain(self) -> str:
        """The Level 2 subdirectory name (REQ-RUN-012)."""
        return normalise_domain(self.case_metadata.domain)

    @property
    def display_name(self) -> str:
        return self.case_metadata.case_title or self.case_metadata.case_id

    @property
    def system_prompt(self) -> str:
        """Text of the Turn 0 system instruction, or ``""`` when there is none."""
        if self.system_instruction is None:
            return ""
        return self.system_instruction.prompt.content_raw

    @property
    def turn_count(self) -> int:
        return len(self.conversation_framework)

    def turn(self, turn_id: int) -> Turn | None:
        for candidate in self.conversation_framework:
            if candidate.turn_id == turn_id:
                return candidate
        return None

    def oracle_theorem_for(self, turn_id: int) -> str | None:
        """REQ-RUN-003: the Lean theorem paired with *turn_id* (1-based)."""
        index = turn_id - 1
        if 0 <= index < len(self.formal_artifacts.oracle_theorems):
            return self.formal_artifacts.oracle_theorems[index]
        return None

    def test_case_ref(self) -> TestCaseRef:
        """The ``test_case`` block a run log embeds."""
        return TestCaseRef(
            case_id=self.case_metadata.case_id,
            case_title=self.case_metadata.case_title,
            domain=self.case_metadata.domain,
            lean_file=self.formal_artifacts.lean_file,
        )


# ========================================================================== #
# RUN LOG SCHEMA (SRS 3.2)
# ========================================================================== #
@dataclass
class RunMetadata:
    """``run_metadata`` block."""

    run_id: str
    run_index: int = 1
    timestamp_start_utc: str | None = None
    timestamp_end_utc: str | None = None
    total_latency_ms: float | None = None
    status: str = STATUS_COMPLETED

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> RunMetadata:
        where = f"{source}.run_metadata"
        data = _mapping(data, where)
        return cls(
            run_id=_req_str(data, "run_id", where),
            run_index=_opt_int(data, "run_index") or 1,
            timestamp_start_utc=_opt_str(data, "timestamp_start_utc"),
            timestamp_end_utc=_opt_str(data, "timestamp_end_utc"),
            total_latency_ms=_opt_float(data, "total_latency_ms"),
            status=_opt_str(data, "status") or STATUS_COMPLETED,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "run_id": self.run_id,
            "run_index": self.run_index,
            "timestamp_start_utc": self.timestamp_start_utc,
            "timestamp_end_utc": self.timestamp_end_utc,
            "total_latency_ms": self.total_latency_ms,
            "status": self.status,
        }


@dataclass
class ModelMetadata:
    """``model_metadata`` block: the parameters actually transmitted."""

    provider: str = ""
    model_id: str = ""
    api_endpoint: str | None = None
    temperature: float | None = None
    top_p: float | None = None
    max_tokens: int | None = None
    thinking_budget_allocated: int | None = None
    system_prompt_used: bool = False

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> ModelMetadata:
        if data is None:
            return cls()
        where = f"{source}.model_metadata"
        data = _mapping(data, where)
        return cls(
            provider=_opt_str(data, "provider") or "",
            model_id=_opt_str(data, "model_id") or "",
            api_endpoint=_opt_str(data, "api_endpoint"),
            temperature=_opt_float(data, "temperature"),
            top_p=_opt_float(data, "top_p"),
            max_tokens=_opt_int(data, "max_tokens"),
            thinking_budget_allocated=_opt_int(data, "thinking_budget_allocated"),
            system_prompt_used=bool(data.get("system_prompt_used", False)),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "provider": self.provider,
            "model_id": self.model_id,
            "api_endpoint": self.api_endpoint,
            "temperature": self.temperature,
            "top_p": self.top_p,
            "max_tokens": self.max_tokens,
            "thinking_budget_allocated": self.thinking_budget_allocated,
            "system_prompt_used": self.system_prompt_used,
        }

    @property
    def label(self) -> str:
        return f"{self.provider}/{self.model_id}" if self.provider else self.model_id

    @property
    def model_name(self) -> str:
        return self.model_id

    @property
    def display_model(self) -> str:
        return self.model_id


@dataclass
class TestCaseRef:
    """``test_case`` block: enough of the case to identify it."""

    case_id: str
    case_title: str = ""
    domain: str = ""
    lean_file: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> TestCaseRef:
        where = f"{source}.test_case"
        data = _mapping(data or {}, where)
        return cls(
            case_id=_req_str(data, "case_id", where),
            case_title=_opt_str(data, "case_title") or "",
            domain=_opt_str(data, "domain") or "",
            lean_file=_opt_str(data, "lean_file"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "case_id": self.case_id,
            "case_title": self.case_title,
            "domain": self.domain,
            "lean_file": self.lean_file,
        }

    @property
    def normalised_domain(self) -> str:
        return normalise_domain(self.domain)


@dataclass
class TurnUsage:
    """``conversation[].response.usage`` block.

    ``cached_tokens`` is the cache *read* count: NFR-CST-002 logs it to verify that
    server-side KV caching actually engaged across the sixteen turns.
    """

    input_tokens: int = 0
    output_tokens: int = 0
    cached_tokens: int = 0

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None) -> TurnUsage:
        data = data or {}
        return cls(
            input_tokens=int(data.get("input_tokens") or 0),
            output_tokens=int(data.get("output_tokens") or 0),
            cached_tokens=int(data.get("cached_tokens") or 0),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cached_tokens": self.cached_tokens,
        }

    def __add__(self, other: TurnUsage) -> TurnUsage:
        return TurnUsage(
            input_tokens=self.input_tokens + other.input_tokens,
            output_tokens=self.output_tokens + other.output_tokens,
            cached_tokens=self.cached_tokens + other.cached_tokens,
        )


@dataclass
class LoggedPrompt:
    """``conversation[].prompt`` block."""

    content: str
    role: str = ROLE_USER

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> LoggedPrompt:
        where = f"{source}.prompt"
        data = _mapping(data or {}, where)
        return cls(
            role=_opt_str(data, "role") or ROLE_USER,
            content=_opt_str(data, "content") or "",
        )

    def to_dict(self) -> dict[str, Any]:
        return {"role": self.role, "content": self.content}


@dataclass
class LoggedResponse:
    """``conversation[].response`` block: the unmanipulated assistant stream."""

    content: str = ""
    role: str = ROLE_ASSISTANT
    thinking_content: str | None = None
    finish_reason: str | None = None
    latency_ms: float | None = None
    usage: TurnUsage = field(default_factory=TurnUsage)

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> LoggedResponse:
        where = f"{source}.response"
        data = _mapping(data or {}, where)
        return cls(
            role=_opt_str(data, "role") or ROLE_ASSISTANT,
            content=_opt_str(data, "content") or "",
            thinking_content=_opt_str(data, "thinking_content"),
            finish_reason=_opt_str(data, "finish_reason"),
            latency_ms=_opt_float(data, "latency_ms"),
            usage=TurnUsage.from_dict(data.get("usage")),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "role": self.role,
            "content": self.content,
            "thinking_content": self.thinking_content,
            "finish_reason": self.finish_reason,
            "latency_ms": self.latency_ms,
            "usage": self.usage.to_dict(),
        }


@dataclass
class TurnEvaluation:
    """``conversation[].evaluation``: an audit placeholder, never machine-filled.

    ``expected_answer_type`` and ``expected_answer_lean`` are copied from the test
    case so the auditor has the ground truth in front of them; the three verdict
    fields stay ``null`` until a human fills them (SRS 1.3, REQ-RUN-009 scope).
    """

    expected_answer_type: str | None = None
    expected_answer_lean: str | None = None
    is_correct: bool | None = None
    failure_mode: str | None = None
    comments: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> TurnEvaluation:
        where = f"{source}.evaluation"
        data = _mapping(data or {}, where)
        return cls(
            expected_answer_type=_opt_str(data, "expected_answer_type"),
            expected_answer_lean=_opt_str(data, "expected_answer_lean"),
            is_correct=_opt_bool(data, "is_correct"),
            failure_mode=_opt_str(data, "failure_mode"),
            comments=_opt_str(data, "comments"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "expected_answer_type": self.expected_answer_type,
            "expected_answer_lean": self.expected_answer_lean,
            "is_correct": self.is_correct,
            "failure_mode": self.failure_mode,
            "comments": self.comments,
        }

    @classmethod
    def unscored_for(cls, expected: ExpectedAnswer | None) -> TurnEvaluation:
        """The placeholder written at run time."""
        return cls(
            expected_answer_type=expected.answer_type if expected else None,
            expected_answer_lean=expected.value if expected else None,
        )

    @property
    def audited(self) -> bool:
        return self.is_correct is not None

    @property
    def is_undetermined(self) -> bool:
        return self.expected_answer_type == ANSWER_TYPE_UNDETERMINED


@dataclass
class ConversationTurn:
    """One entry of the run log's ``conversation`` list."""

    turn_id: int
    phase: str = ""
    turn_type: str = ""
    oracle_theorem_ref: str | None = None
    prompt: LoggedPrompt = field(default_factory=lambda: LoggedPrompt(content=""))
    response: LoggedResponse = field(default_factory=LoggedResponse)
    evaluation: TurnEvaluation = field(default_factory=TurnEvaluation)

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str) -> ConversationTurn:
        data = _mapping(data, source)
        turn_id = _req_int(data, "turn_id", source)
        where = f"{source}[turn {turn_id}]"
        return cls(
            turn_id=turn_id,
            phase=_opt_str(data, "phase") or "",
            turn_type=_opt_str(data, "turn_type") or "",
            oracle_theorem_ref=_opt_str(data, "oracle_theorem_ref"),
            prompt=LoggedPrompt.from_dict(data.get("prompt"), where),
            response=LoggedResponse.from_dict(data.get("response"), where),
            evaluation=TurnEvaluation.from_dict(data.get("evaluation"), where),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "turn_id": self.turn_id,
            "phase": self.phase,
            "turn_type": self.turn_type,
            "oracle_theorem_ref": self.oracle_theorem_ref,
            "prompt": self.prompt.to_dict(),
            "response": self.response.to_dict(),
            "evaluation": self.evaluation.to_dict(),
        }

    @property
    def answered(self) -> bool:
        return bool(self.response.content)


@dataclass
class EvaluationSummary:
    """``evaluation_summary``: totals only; the counts await a human auditor."""

    total_turns: int = TURNS_PER_CASE
    correct_turns: int | None = None
    incorrect_turns: int | None = None
    failure_modes_observed: list[str] = field(default_factory=list)
    comments: str | None = None

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None, source: str) -> EvaluationSummary:
        if data is None:
            return cls()
        where = f"{source}.evaluation_summary"
        data = _mapping(data, where)
        return cls(
            total_turns=_opt_int(data, "total_turns") or 0,
            correct_turns=_opt_int(data, "correct_turns"),
            incorrect_turns=_opt_int(data, "incorrect_turns"),
            failure_modes_observed=_str_list(
                data.get("failure_modes_observed"), where, "failure_modes_observed"
            ),
            comments=_opt_str(data, "comments"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "total_turns": self.total_turns,
            "correct_turns": self.correct_turns,
            "incorrect_turns": self.incorrect_turns,
            "failure_modes_observed": list(self.failure_modes_observed),
            "comments": self.comments,
        }

    @property
    def audited(self) -> bool:
        return self.correct_turns is not None or self.incorrect_turns is not None


@dataclass
class ResearcherReview:
    """One reviewer slot of ``researcher_review``. Written by humans, read by the GUI."""

    researcher_id: str = UNASSIGNED_REVIEWER
    researcher_name: str | None = None
    review_status: str = REVIEW_STATUS_UNREVIEWED
    overall_assessment: str | None = None
    notable_observations: list[str] = field(default_factory=list)

    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str, index: int) -> ResearcherReview:
        where = f"{source}.researcher_review[{index}]"
        data = _mapping(data, where)
        return cls(
            researcher_id=_opt_str(data, "researcher_id") or UNASSIGNED_REVIEWER,
            researcher_name=_opt_str(data, "researcher_name"),
            review_status=_opt_str(data, "review_status") or REVIEW_STATUS_UNREVIEWED,
            overall_assessment=_opt_str(data, "overall_assessment"),
            notable_observations=_str_list(
                data.get("notable_observations"), where, "notable_observations"
            ),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "researcher_id": self.researcher_id,
            "researcher_name": self.researcher_name,
            "review_status": self.review_status,
            "overall_assessment": self.overall_assessment,
            "notable_observations": list(self.notable_observations),
        }

    @property
    def reviewed(self) -> bool:
        return self.review_status != REVIEW_STATUS_UNREVIEWED


# --------------------------------------------------------------------------- #
# the run log itself
# --------------------------------------------------------------------------- #
@dataclass
class RunLog:
    """A complete run log: one isolated execution of one test case."""

    run_metadata: RunMetadata
    test_case: TestCaseRef
    model_metadata: ModelMetadata = field(default_factory=ModelMetadata)
    conversation: list[ConversationTurn] = field(default_factory=list)
    evaluation_summary: EvaluationSummary = field(default_factory=EvaluationSummary)
    researcher_review: list[ResearcherReview] = field(default_factory=list)
    #: Where this log was read from or written to; not part of the schema.
    log_path: str | None = None

    # -- parsing ------------------------------------------------------------ #
    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str = "<run log>") -> RunLog:
        data = _mapping(data, source)

        conversation_raw = data.get("conversation") or []
        if not isinstance(conversation_raw, Sequence) or isinstance(conversation_raw, str):
            raise SchemaError("'conversation' must be a list", source=source)

        reviews_raw = data.get("researcher_review") or []
        if not isinstance(reviews_raw, Sequence) or isinstance(reviews_raw, str):
            raise SchemaError("'researcher_review' must be a list", source=source)

        return cls(
            run_metadata=RunMetadata.from_dict(data.get("run_metadata") or {}, source),
            model_metadata=ModelMetadata.from_dict(data.get("model_metadata"), source),
            test_case=TestCaseRef.from_dict(data.get("test_case"), source),
            conversation=[
                ConversationTurn.from_dict(item, f"{source}.conversation")
                for item in conversation_raw
            ],
            # Preserved verbatim: an auditor may have filled the counts in by hand.
            evaluation_summary=EvaluationSummary.from_dict(
                data.get("evaluation_summary"), source
            ),
            researcher_review=[
                ResearcherReview.from_dict(item, source, index)
                for index, item in enumerate(reviews_raw)
            ],
        )

    @classmethod
    def from_file(cls, path: str | Path) -> RunLog:
        file_path = Path(path)
        try:
            raw = json.loads(file_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise SchemaError(f"invalid JSON ({exc})", source=str(file_path)) from exc
        log = cls.from_dict(raw, source=str(file_path))
        log.log_path = paths.as_project_relative(file_path)
        return log

    # -- emitting ----------------------------------------------------------- #
    def to_dict(self) -> dict[str, Any]:
        return {
            "run_metadata": self.run_metadata.to_dict(),
            "model_metadata": self.model_metadata.to_dict(),
            "test_case": self.test_case.to_dict(),
            "conversation": [turn.to_dict() for turn in self.conversation],
            "evaluation_summary": self.evaluation_summary.to_dict(),
            "researcher_review": [review.to_dict() for review in self.researcher_review],
        }

    # -- construction ------------------------------------------------------- #
    @classmethod
    def for_test_case(
        cls,
        case: TestCase,
        *,
        run_id: str,
        run_index: int = 1,
        model_metadata: ModelMetadata | None = None,
        reviewers: Sequence[str] | None = None,
    ) -> RunLog:
        """A fresh log with the audit placeholders initialised."""
        slots = [ResearcherReview(researcher_id=name) for name in (reviewers or ())]
        return cls(
            run_metadata=RunMetadata(
                run_id=run_id,
                run_index=run_index,
                timestamp_start_utc=utc_now(),
                status=STATUS_COMPLETED,
            ),
            model_metadata=model_metadata or ModelMetadata(),
            test_case=case.test_case_ref(),
            evaluation_summary=EvaluationSummary(total_turns=case.turn_count),
            researcher_review=slots or [ResearcherReview()],
        )

    # -- convenience -------------------------------------------------------- #
    @property
    def run_id(self) -> str:
        return self.run_metadata.run_id

    @property
    def run_index(self) -> int:
        return self.run_metadata.run_index

    @property
    def case_id(self) -> str:
        return self.test_case.case_id

    @property
    def domain(self) -> str:
        return self.test_case.domain

    @property
    def model_id(self) -> str:
        return self.model_metadata.model_id

    @property
    def display_name(self) -> str:
        return self.test_case.case_title or self.test_case.case_id

    @property
    def status(self) -> str:
        return self.run_metadata.status

    @property
    def completed(self) -> bool:
        return self.run_metadata.status == STATUS_COMPLETED

    @property
    def answered_turns(self) -> int:
        return sum(1 for turn in self.conversation if turn.answered)

    @property
    def usage_totals(self) -> TurnUsage:
        total = TurnUsage()
        for turn in self.conversation:
            total = total + turn.response.usage
        return total

    @property
    def reviewed(self) -> bool:
        return any(review.reviewed for review in self.researcher_review)

    def turn(self, turn_id: int) -> ConversationTurn | None:
        for candidate in self.conversation:
            if candidate.turn_id == turn_id:
                return candidate
        return None


def total_usage(logs: Sequence[RunLog]) -> TurnUsage:
    total = TurnUsage()
    for log in logs:
        total = total + log.usage_totals
    return total


# --------------------------------------------------------------------------- #
# transport-level token accounting (not part of either schema)
# --------------------------------------------------------------------------- #
@dataclass
class Usage:
    """What an SDK reported for one call.

    Richer than the schema's :class:`TurnUsage` because Anthropic separates cache
    writes from cache reads and reasoning models bill thinking tokens; the extra
    counters inform throttling and cost review, then collapse into ``TurnUsage``
    when the turn is logged.
    """

    input_tokens: int = 0
    output_tokens: int = 0
    cache_creation_input_tokens: int = 0
    cache_read_input_tokens: int = 0
    reasoning_tokens: int = 0

    @classmethod
    def from_dict(cls, data: Mapping[str, Any] | None) -> Usage:
        data = data or {}
        return cls(
            input_tokens=int(data.get("input_tokens") or 0),
            output_tokens=int(data.get("output_tokens") or 0),
            cache_creation_input_tokens=int(data.get("cache_creation_input_tokens") or 0),
            cache_read_input_tokens=int(data.get("cache_read_input_tokens") or 0),
            reasoning_tokens=int(data.get("reasoning_tokens") or 0),
        )

    def to_log_usage(self) -> TurnUsage:
        return TurnUsage(
            input_tokens=self.input_tokens,
            output_tokens=self.output_tokens,
            cached_tokens=self.cache_read_input_tokens,
        )

    def __add__(self, other: Usage) -> Usage:
        return Usage(
            input_tokens=self.input_tokens + other.input_tokens,
            output_tokens=self.output_tokens + other.output_tokens,
            cache_creation_input_tokens=self.cache_creation_input_tokens
            + other.cache_creation_input_tokens,
            cache_read_input_tokens=self.cache_read_input_tokens
            + other.cache_read_input_tokens,
            reasoning_tokens=self.reasoning_tokens + other.reasoning_tokens,
        )
