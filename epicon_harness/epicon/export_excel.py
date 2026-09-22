"""Multi-run Excel exporter (REQ-EXP-001 … REQ-EXP-006).

The workbook is organised the way an auditor actually reads the data: one sheet
per ``(case_id, model_id)`` group, sixteen turns down the page, and the five
independent runs of that model laid out side-by-side next to the Lean ground
truth. Verdict / failure-mode / auditor-notes cells are left empty and bordered
so the post-hoc audit can be filled in by hand.

Colour conventions
------------------
* Light blue  — Lean ground-truth cells (the oracle, not a model output).
* Light yellow — turns whose expected answer is ``undetermined``.
"""

from __future__ import annotations

import re
from collections import defaultdict
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from . import paths, storage
from .errors import MissingDependency
from .models import ANSWER_TYPE_UNDETERMINED, TURNS_PER_CASE, RunLog, TestCase
from .storage import ResultLocation

#: Excel refuses cell values longer than this.
MAX_CELL_CHARS = 32_000
_ILLEGAL_CHARS = re.compile(r"[\000-\010\013\014\016-\037]")
_SHEET_ILLEGAL = re.compile(r'[:\\/?*\[\]]')

#: REQ-EXP-004: five independent runs sit side-by-side.
MAX_RUNS = 5
GROUND_TRUTH_FILL = "D6EAF8"  # light blue
UNDERDETERMINED_FILL = "FFF3CD"  # light yellow
HEADER_FILL = "2F4858"
AUDIT_BORDER = "7F8C8D"

Session = tuple[RunLog, "TestCase | None"]


@dataclass
class ExportResult:
    path: Path
    run_count: int
    turn_count: int
    group_count: int
    review_count: int = 0


def _clip(value: str | None) -> str:
    text = _ILLEGAL_CHARS.sub("", value or "")
    if len(text) > MAX_CELL_CHARS:
        return text[: MAX_CELL_CHARS - 20] + "\n…[truncated]"
    return text


def _sheet_name(case_id: str, model_id: str, used: set[str]) -> str:
    """REQ-EXP-003: unique worksheet title, truncated to 31 characters."""
    stem = _SHEET_ILLEGAL.sub("-", f"{case_id}_{model_id}")[:31] or "sheet"
    candidate = stem
    index = 2
    while candidate in used:
        suffix = f"_{index}"
        candidate = f"{stem[: 31 - len(suffix)]}{suffix}"
        index += 1
    used.add(candidate)
    return candidate


def _group_key(log: RunLog, location: ResultLocation | None = None) -> tuple[str, str]:
    """REQ-EXP-002: ``(case_id, model_name)``."""
    model = log.model_id or (location.model_id if location else "")
    return (log.case_id, model)


def _as_text(cell) -> None:
    if isinstance(cell.value, str):
        cell.data_type = "s"


def export_results(
    results_dir: str | Path | None,
    output_path: str | Path,
    *,
    test_cases_dir: str | Path | None = None,
    only: Sequence[str] | None = None,
) -> ExportResult:
    """REQ-EXP-001: recursively scan ``results/`` and write the audit workbook."""
    loaded, _failures = storage.load_results(Path(results_dir) if results_dir else None)
    if only:
        wanted = set(only)
        loaded = [(log, loc) for log, loc in loaded if log.case_id in wanted]
    index = storage.TestCaseIndex.load(Path(test_cases_dir) if test_cases_dir else None)
    sessions = [(log, index.for_log(log), loc) for log, loc in loaded]
    return export_grouped(sessions, output_path)


def export_sessions(sessions: Sequence[Session], output_path: str | Path) -> ExportResult:
    """Back-compat wrapper used by the GUI (no path-derived location)."""
    return export_grouped([(log, case, None) for log, case in sessions], output_path)


def export_logs(
    logs: Sequence[RunLog],
    output_path: str | Path,
    *,
    test_cases: Sequence[TestCase] | None = None,
) -> ExportResult:
    index = storage.TestCaseIndex(test_cases) if test_cases is not None else storage.TestCaseIndex.load()
    return export_sessions([(log, index.for_log(log)) for log in logs], output_path)


def export_grouped(
    sessions: Sequence[tuple[RunLog, TestCase | None, ResultLocation | None]],
    output_path: str | Path,
) -> ExportResult:
    try:
        from openpyxl import Workbook
        from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
        from openpyxl.utils import get_column_letter
    except ImportError as exc:  # pragma: no cover
        raise MissingDependency("openpyxl", "Excel export") from exc

    path = Path(output_path)
    path.parent.mkdir(parents=True, exist_ok=True)

    groups: dict[tuple[str, str], list[tuple[RunLog, TestCase | None]]] = defaultdict(list)
    for log, case, location in sessions:
        groups[_group_key(log, location)].append((log, case))

    workbook = Workbook()
    header_font = Font(bold=True, color="FFFFFF")
    header_fill = PatternFill("solid", fgColor=HEADER_FILL)
    ground_fill = PatternFill("solid", fgColor=GROUND_TRUTH_FILL)
    under_fill = PatternFill("solid", fgColor=UNDERDETERMINED_FILL)
    wrap = Alignment(vertical="top", wrap_text=True)
    thin = Border(
        left=Side(style="thin", color=AUDIT_BORDER),
        right=Side(style="thin", color=AUDIT_BORDER),
        top=Side(style="thin", color=AUDIT_BORDER),
        bottom=Side(style="thin", color=AUDIT_BORDER),
    )

    used_names: set[str] = set()
    index_rows: list[tuple[str, str, str, int]] = []
    first = True
    turn_count = 0
    run_count = 0

    for (case_id, model_id), members in sorted(groups.items()):
        by_index: dict[int, RunLog] = {}
        case = members[0][1]
        for log, member_case in members:
            by_index[log.run_index] = log
            case = case or member_case
        run_count += len(by_index)

        title = _sheet_name(case_id, model_id, used_names)
        sheet = workbook.active if first else workbook.create_sheet()
        first = False
        sheet.title = title
        index_rows.append((case_id, model_id, title, len(by_index)))

        headers = [
            "Turn",
            "Phase",
            "Turn Type",
            "Oracle Theorem",
            "Lean Ground Truth",
            "Answer Type",
        ]
        for run_index in range(1, MAX_RUNS + 1):
            headers.extend(
                [
                    f"Run {run_index} Output",
                    f"Run {run_index} Verdict",
                    f"Run {run_index} Failure Mode",
                    f"Run {run_index} Auditor Notes",
                ]
            )
        sheet.append(headers)
        for cell in sheet[1]:
            cell.font = header_font
            cell.fill = header_fill
            cell.alignment = Alignment(vertical="top", wrap_text=True)

        sample = next(iter(by_index.values()))
        for turn_id in range(1, TURNS_PER_CASE + 1):
            spec = case.turn(turn_id) if case else None
            sample_turn = sample.turn(turn_id)
            expected = (
                spec.expected_answer
                if spec and spec.expected_answer
                else None
            )
            ground = (
                expected.value
                if expected
                else (sample_turn.evaluation.expected_answer_lean if sample_turn else None)
            )
            answer_type = (
                expected.answer_type
                if expected
                else (sample_turn.evaluation.expected_answer_type if sample_turn else None)
            )
            undetermined = (answer_type == ANSWER_TYPE_UNDETERMINED) or (
                sample_turn.evaluation.is_undetermined if sample_turn else False
            )
            row: list[object] = [
                turn_id,
                (spec.phase if spec else (sample_turn.phase if sample_turn else "")),
                (spec.turn_type if spec else (sample_turn.turn_type if sample_turn else "")),
                (
                    case.oracle_theorem_for(turn_id)
                    if case
                    else (sample_turn.oracle_theorem_ref if sample_turn else "")
                )
                or "",
                _clip(ground),
                answer_type or "",
            ]
            for run_index in range(1, MAX_RUNS + 1):
                log = by_index.get(run_index)
                turn = log.turn(turn_id) if log else None
                row.append(_clip(turn.response.content) if turn else "")
                # REQ-EXP-005: empty bordered cells for the human auditor.
                row.extend(["", "", ""])
            sheet.append(row)
            turn_count += 1

            excel_row = turn_id + 1
            for cell in sheet[excel_row]:
                cell.alignment = wrap
                _as_text(cell)
                if undetermined:
                    cell.fill = under_fill
            # Lean ground truth is column 5.
            truth_cell = sheet.cell(row=excel_row, column=5)
            truth_cell.fill = ground_fill
            for run_index in range(1, MAX_RUNS + 1):
                # Verdict, failure mode, notes sit at columns 8/9/10, 12/13/14, …
                base = 7 + (run_index - 1) * 4
                for offset in (1, 2, 3):
                    audit = sheet.cell(row=excel_row, column=base + offset)
                    audit.border = thin

        widths = [8, 28, 32, 28, 28, 16] + [36, 14, 18, 24] * MAX_RUNS
        for index, width in enumerate(widths, start=1):
            sheet.column_dimensions[get_column_letter(index)].width = width
        sheet.freeze_panes = "A2"
        sheet.auto_filter.ref = f"A1:{get_column_letter(len(headers))}{TURNS_PER_CASE + 1}"

    index_sheet = workbook.create_sheet("Index", 0)
    index_sheet.append(["Case ID", "Model", "Sheet", "Runs present"])
    for cell in index_sheet[1]:
        cell.font = header_font
        cell.fill = header_fill
    for row in index_rows:
        index_sheet.append(list(row))
    for letter, width in zip("ABCD", (14, 28, 31, 14), strict=True):
        index_sheet.column_dimensions[letter].width = width
    index_sheet.freeze_panes = "A2"

    workbook.save(path)
    return ExportResult(
        path=path,
        run_count=run_count,
        turn_count=turn_count,
        group_count=len(groups),
    )


def default_results_dir() -> Path:
    return paths.RESULTS_DIR
