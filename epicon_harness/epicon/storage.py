"""Filesystem layer: test case discovery, the SRS results hierarchy, and journaling.

Two storage concerns live here.

**The results hierarchy (SRS 1.2, REQ-RUN-012/013).** Every session log lands at::

    results/{ModelName}-run-{RunIndex}/{normalised-domain}/{CaseID}-{ModelID}-R{RunIndex}.json

Level 1 uses the model identifier as configured, Level 2 the domain with
underscores converted to hyphens, Level 3 the sanitised model id. The exporter and
the GUI rediscover sessions by walking the same two levels.

**The in-flight journal (REQ-RUN-015/016).** Each completed turn is appended to a
JSON-Lines file under ``.journals/`` and flushed with :func:`os.fsync`, so a
``SIGKILL`` at turn 8 leaves turns 1–7 intact on disk. ``--resume`` reads the
journal back and restarts transmission at the first unrecorded turn, without
re-billing what already completed.
"""

from __future__ import annotations

import json
import os
import re
import tempfile
import threading
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from . import paths
from .errors import SchemaError
from .models import ConversationTurn, RunLog, TestCase, normalise_domain

_SAFE_NAME = re.compile(r"[^A-Za-z0-9._-]+")

#: Run id format from the schema, e.g. ``RUN_2026_04_14_0001``.
RUN_ID_PATTERN = re.compile(r"^RUN_(\d{4})_(\d{2})_(\d{2})_(\d{4})$")
#: Level 1 directory: ``{ModelName}-run-{RunIndex}``.
SESSION_DIR_PATTERN = re.compile(r"^(?P<model>.+)-run-(?P<index>\d+)$")
#: Level 3 file stem: ``{CaseID}-{SanitizedModelID}-R{RunIndex}``.
RESULT_STEM_PATTERN = re.compile(r"^(?P<case>[A-Z]{2}-\d{2})-(?P<model>.+)-R(?P<index>\d+)$")

_run_id_lock = threading.Lock()
_issued_run_ids: set[str] = set()


def safe_filename(value: str, fallback: str = "unnamed") -> str:
    cleaned = _SAFE_NAME.sub("_", (value or "").strip()).strip("._")
    return cleaned or fallback


def safe_dirname(value: str, fallback: str = "model") -> str:
    """Filesystem-safe directory component, preserving dots and hyphens.

    Model identifiers routinely contain a slash (``meta/llama-3.1`` on NIM) or a
    colon, neither of which can appear in a path segment.
    """
    cleaned = _SAFE_NAME.sub("-", (value or "").strip()).strip("-._")
    return cleaned or fallback


# --------------------------------------------------------------------------- #
# test case discovery
# --------------------------------------------------------------------------- #
def iter_json_files(root: Path, *, recursive: bool = True) -> Iterator[Path]:
    if root.is_file():
        yield root
        return
    if not root.exists():
        return
    pattern = "**/*.json" if recursive else "*.json"
    for path in sorted(root.glob(pattern)):
        if path.is_file():
            yield path


def discover_test_case_files(root: Path | None = None, *, recursive: bool = True) -> list[Path]:
    return list(iter_json_files(root or paths.TEST_CASES_DIR, recursive=recursive))


def load_test_cases(
    targets: Sequence[Path | str] | None = None, *, strict: bool = True
) -> tuple[list[TestCase], list[tuple[Path, Exception]]]:
    """Load test cases from files and/or directories.

    Returns the successfully parsed cases plus a list of ``(path, error)`` pairs.
    With ``strict=True`` the first parse error is raised instead.
    """
    if targets is None:
        files = discover_test_case_files()
    else:
        files = []
        for target in targets:
            path = Path(target)
            files.extend(iter_json_files(path) if path.is_dir() else [path])

    cases: list[TestCase] = []
    failures: list[tuple[Path, Exception]] = []
    seen: dict[str, Path] = {}

    for path in files:
        try:
            case = TestCase.from_file(path)
        except (SchemaError, OSError) as exc:
            if strict:
                raise
            failures.append((path, exc))
            continue

        if case.case_id in seen:
            error = SchemaError(
                f"duplicate case_id '{case.case_id}' (already defined in {seen[case.case_id]})",
                source=str(path),
            )
            if strict:
                raise error
            failures.append((path, error))
            continue

        seen[case.case_id] = path
        cases.append(case)

    return cases, failures


# --------------------------------------------------------------------------- #
# the results hierarchy
# --------------------------------------------------------------------------- #
def session_dirname(model_id: str, run_index: int) -> str:
    """Level 1 component: ``{ModelName}-run-{RunIndex}``."""
    return f"{safe_dirname(model_id)}-run-{run_index}"


def result_filename(case_id: str, sanitised_model_id: str, run_index: int) -> str:
    """Level 3 component: ``{CaseID}-{SanitizedModelID}-R{RunIndex}.json``."""
    return f"{safe_filename(case_id)}-{safe_filename(sanitised_model_id)}-R{run_index}.json"


def session_path(
    *,
    model_id: str,
    sanitised_model_id: str,
    run_index: int,
    domain: str,
    case_id: str,
    results_dir: Path | None = None,
) -> Path:
    """The full REQ-RUN-013 destination for one session."""
    base = results_dir or paths.RESULTS_DIR
    return (
        base
        / session_dirname(model_id, run_index)
        / normalise_domain(domain)
        / result_filename(case_id, sanitised_model_id, run_index)
    )


@dataclass(frozen=True)
class ResultLocation:
    """What a result path says about the session it holds."""

    path: Path
    model_id: str
    run_index: int
    domain: str
    case_id: str
    sanitised_model_id: str

    @property
    def group_key(self) -> tuple[str, str, str]:
        """REQ-EXP-002 composite key: ``(domain, case_id, model_id)``."""
        return (self.domain, self.case_id, self.model_id)


def parse_result_path(path: Path) -> ResultLocation | None:
    """Recover model, run index, domain and case id from a result path.

    Returns ``None`` for anything that does not sit at the specified depth, so a
    stray file in ``results/`` is ignored rather than breaking a batch export.
    """
    domain_dir = path.parent
    session_dir = domain_dir.parent
    session_match = SESSION_DIR_PATTERN.match(session_dir.name)
    if session_match is None:
        return None

    run_index = int(session_match.group("index"))
    stem_match = RESULT_STEM_PATTERN.match(path.stem)
    case_id = stem_match.group("case") if stem_match else path.stem
    sanitised = stem_match.group("model") if stem_match else ""

    return ResultLocation(
        path=path,
        model_id=session_match.group("model"),
        run_index=run_index,
        domain=domain_dir.name,
        case_id=case_id,
        sanitised_model_id=sanitised,
    )


def discover_result_files(results_dir: Path | None = None) -> list[Path]:
    """REQ-EXP-001: recursive scan of ``results/*-run-*/*/*.json``."""
    base = results_dir or paths.RESULTS_DIR
    if base.is_file():
        return [base]
    if not base.exists():
        return []
    return sorted(
        path
        for path in base.glob("*-run-*/*/*.json")
        if path.is_file() and not path.name.startswith(".")
    )


def load_results(
    results_dir: Path | None = None, *, strict: bool = False
) -> tuple[list[tuple[RunLog, ResultLocation]], list[tuple[Path, Exception]]]:
    """Every session under ``results/``, paired with what its path encodes."""
    loaded: list[tuple[RunLog, ResultLocation]] = []
    failures: list[tuple[Path, Exception]] = []

    for path in discover_result_files(results_dir):
        location = parse_result_path(path)
        if location is None:
            continue
        try:
            log = RunLog.from_file(path)
        except (SchemaError, OSError) as exc:
            if strict:
                raise
            failures.append((path, exc))
            continue
        loaded.append((log, location))

    loaded.sort(
        key=lambda pair: (
            pair[0].test_case.domain or pair[1].domain,
            pair[0].case_id,
            pair[0].model_id or pair[1].model_id,
            pair[0].run_index,
        )
    )
    return loaded, failures


def load_run_logs(
    results_dir: Path | None = None, *, strict: bool = False
) -> tuple[list[RunLog], list[tuple[Path, Exception]]]:
    loaded, failures = load_results(results_dir, strict=strict)
    return [log for log, _ in loaded], failures


# --------------------------------------------------------------------------- #
# run ids
# --------------------------------------------------------------------------- #
def next_run_id(results_dir: Path | None = None, *, now: datetime | None = None) -> str:
    """Mint the next ``RUN_YYYY_MM_DD_NNNN`` id for today.

    The sequence continues from the highest id already recorded under
    *results_dir*, so ids stay unique and ordered across separate invocations.
    Thread-safe, and ids handed out but not yet written are also accounted for.
    """
    base = results_dir or paths.RESULTS_DIR
    stamp = (now or datetime.now(timezone.utc)).strftime("%Y_%m_%d")
    prefix = f"RUN_{stamp}_"

    with _run_id_lock:
        highest = 0
        for path in discover_result_files(base):
            try:
                run_id = json.loads(path.read_text(encoding="utf-8"))["run_metadata"]["run_id"]
            except (OSError, ValueError, KeyError, TypeError):
                continue
            match = RUN_ID_PATTERN.match(str(run_id))
            if match and str(run_id).startswith(prefix):
                highest = max(highest, int(match.group(4)))
        for issued in _issued_run_ids:
            if issued.startswith(prefix):
                highest = max(highest, int(issued.rsplit("_", 1)[1]))

        run_id = f"{prefix}{highest + 1:04d}"
        _issued_run_ids.add(run_id)
        return run_id


# --------------------------------------------------------------------------- #
# persistence
# --------------------------------------------------------------------------- #
def run_log_path(
    log: RunLog, results_dir: Path | None = None, *, sanitised_model_id: str | None = None
) -> Path:
    """Where *log* belongs under ``results/``."""
    return session_path(
        model_id=log.model_metadata.model_id or "model",
        sanitised_model_id=sanitised_model_id
        or safe_filename(log.model_metadata.model_id or "model"),
        run_index=log.run_index,
        domain=log.test_case.domain,
        case_id=log.case_id,
        results_dir=results_dir,
    )


def write_json_atomic(path: Path, payload: object) -> Path:
    """Write JSON via a temp file + ``os.replace`` so readers never see a partial file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=f".{path.stem}.",
        suffix=".tmp",
        delete=False,
    )
    try:
        with handle as stream:
            json.dump(payload, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(handle.name, path)
    except BaseException:
        Path(handle.name).unlink(missing_ok=True)
        raise
    return path


def write_run_log(
    log: RunLog,
    results_dir: Path | None = None,
    path: Path | None = None,
    *,
    sanitised_model_id: str | None = None,
) -> Path:
    """Persist *log* into the results hierarchy and stamp its ``log_path``."""
    target = path or run_log_path(log, results_dir, sanitised_model_id=sanitised_model_id)
    write_json_atomic(target, log.to_dict())
    log.log_path = paths.as_project_relative(target)
    return target


# --------------------------------------------------------------------------- #
# in-flight journaling (REQ-RUN-015 / REQ-RUN-016)
# --------------------------------------------------------------------------- #
#: Record kinds written to a journal.
JOURNAL_HEADER = "session"
JOURNAL_TURN = "turn"


def journal_path(
    *,
    model_id: str,
    sanitised_model_id: str,
    run_index: int,
    domain: str,
    case_id: str,
    journal_dir: Path | None = None,
) -> Path:
    """The journal mirroring one session's result path, with a ``.jsonl`` suffix."""
    base = journal_dir or paths.JOURNAL_DIR
    return (
        base
        / session_dirname(model_id, run_index)
        / normalise_domain(domain)
        / result_filename(case_id, sanitised_model_id, run_index).replace(".json", ".jsonl")
    )


@dataclass
class JournalState:
    """What a journal on disk says about an interrupted session."""

    path: Path
    header: dict[str, Any]
    turns: list[ConversationTurn]

    @property
    def last_turn_id(self) -> int:
        return max((turn.turn_id for turn in self.turns), default=0)

    @property
    def resume_from(self) -> int:
        """The first turn still to be transmitted."""
        return self.last_turn_id + 1

    @property
    def run_id(self) -> str | None:
        value = self.header.get("run_id")
        return str(value) if value else None


class TurnJournal:
    """Append-only JSON-Lines journal for one session.

    Each record is written, flushed and ``fsync``-ed before the next API call is
    made, which is what lets a killed process resume without re-billing.
    """

    def __init__(self, path: Path) -> None:
        self.path = path
        self._stream = None
        self._lock = threading.Lock()

    def open(self, header: dict[str, Any]) -> None:
        """Open for appending, writing *header* if the file is new."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        is_new = not self.path.exists() or self.path.stat().st_size == 0
        self._stream = self.path.open("a", encoding="utf-8")
        if is_new:
            self._write({"record": JOURNAL_HEADER, **header})

    def append_turn(self, turn: ConversationTurn) -> None:
        self._write({"record": JOURNAL_TURN, "turn": turn.to_dict()})

    def _write(self, payload: dict[str, Any]) -> None:
        if self._stream is None:  # pragma: no cover - misuse
            raise RuntimeError("journal is not open")
        with self._lock:
            json.dump(payload, self._stream, ensure_ascii=False)
            self._stream.write("\n")
            self._stream.flush()
            os.fsync(self._stream.fileno())

    def close(self) -> None:
        if self._stream is not None:
            try:
                self._stream.close()
            finally:
                self._stream = None

    def discard(self) -> None:
        """Remove the journal once the session log has been persisted."""
        self.close()
        self.path.unlink(missing_ok=True)
        for parent in (self.path.parent, self.path.parent.parent):
            try:
                parent.rmdir()
            except OSError:
                break

    def __enter__(self) -> TurnJournal:
        return self

    def __exit__(self, *_exc_info: object) -> None:
        self.close()


def read_journal(path: Path) -> JournalState | None:
    """Reconstruct turns 1..k from a journal, tolerating a truncated final line.

    A process killed mid-write can leave a partial record; that line is dropped
    rather than treated as corruption, because the turn it describes was never
    confirmed complete.
    """
    if not path.exists():
        return None

    header: dict[str, Any] = {}
    turns: list[ConversationTurn] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            payload = json.loads(line)
        except ValueError:
            continue  # truncated tail from an interrupted write
        if payload.get("record") == JOURNAL_HEADER:
            header = {key: value for key, value in payload.items() if key != "record"}
        elif payload.get("record") == JOURNAL_TURN:
            try:
                turns.append(
                    ConversationTurn.from_dict(payload.get("turn") or {}, str(path))
                )
            except SchemaError:
                continue

    turns.sort(key=lambda turn: turn.turn_id)
    return JournalState(path=path, header=header, turns=turns)


def discover_journals(journal_dir: Path | None = None) -> list[Path]:
    base = journal_dir or paths.JOURNAL_DIR
    if not base.exists():
        return []
    return sorted(path for path in base.glob("*-run-*/*/*.jsonl") if path.is_file())


# --------------------------------------------------------------------------- #
# pairing logs back to their test cases
# --------------------------------------------------------------------------- #
class TestCaseIndex:
    """Lookup of test cases by ``case_id``."""

    def __init__(self, cases: Iterable[TestCase]) -> None:
        self._by_id: dict[str, TestCase] = {}
        for case in cases:
            self._by_id.setdefault(case.case_id, case)

    @classmethod
    def load(cls, root: Path | None = None) -> TestCaseIndex:
        cases, _ = load_test_cases([root] if root is not None else None, strict=False)
        return cls(cases)

    def for_log(self, log: RunLog) -> TestCase | None:
        return self._by_id.get(log.case_id)

    def get(self, case_id: str) -> TestCase | None:
        return self._by_id.get(case_id)

    def __iter__(self) -> Iterator[TestCase]:
        return iter(self._by_id.values())

    def __len__(self) -> int:
        return len(self._by_id)


def load_sessions(
    results_dir: Path | None = None, test_cases_dir: Path | None = None
) -> list[tuple[RunLog, TestCase | None]]:
    """Every session under ``results/``, paired with its test case when available."""
    logs, _ = load_run_logs(results_dir)
    index = TestCaseIndex.load(test_cases_dir)
    return [(log, index.for_log(log)) for log in logs]
